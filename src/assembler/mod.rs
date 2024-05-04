use core::fmt;
use std::{
    borrow::Borrow,
    collections::{BTreeSet, HashMap, HashSet},
};

use extend::ext;
use lazy_static::lazy_static;

use crate::{
    assembler::par_copy::{serialize_copies, SerializedStep},
    inter::{
        constant::Const,
        ir::{
            Address, BlockRef, GlobalVar, Inst, InstRef, Method, ProgPt, Program, StackSlotRef,
            Terminator,
        },
        types::Type,
    },
    opt::{
        dom::{compute_dominance, Dominance},
        for_each_successor, predecessors, reverse_postorder, split_critical_edges,
    },
};

use self::{imm_nm::ImmediateNonMaterializer, regalloc::RegAllocator, spill::Spiller};

pub mod imm_nm;
pub mod par_copy;
pub mod regalloc;
pub mod spill;

/// An augmentation to the `Method` struct that contains information needed for
/// code generation.
#[derive(Debug, Clone)]
pub struct LoweredMethod {
    /// The method being lowered. Critical edges have been split.
    /// While instructions can be modified, the control flow graph should not
    /// be, for otherwise the dominance information will be invalid.
    pub method: Method,

    /// The maximum number of registers available.
    pub max_reg: usize,

    // Common CFG info needed for codegen
    /// The dominance information of the method.
    pub dom: Dominance,
    /// The dominator tree of the method.
    pub dom_tree: Vec<Vec<BlockRef>>,
    /// The predecessors of each block.
    pub predecessors: Vec<HashSet<BlockRef>>,

    /// Non-materialized arguments. An argument is not materialized if it does
    /// not reside in a register when the instruction using the argument is
    /// executed. An argument can be non-materialized for two reasons.
    /// - For a large call, there's no way to store all of its argument in
    ///   registers.
    /// - For constants can usually just be encoded as immediates and do not
    ///   require a separate register.
    pub nm_args: HashMap<InstRef, HashSet<InstRef>>,

    // Filled in by the spiller
    /// A mapping from spilled variables to their spill slots.
    pub spill_slots: HashMap<InstRef, StackSlotRef>,

    // Filled in by the register allocator
    pub live_at: HashMap<ProgPt, im::HashSet<InstRef>>,
    pub reg: HashMap<InstRef, usize>,
}

impl LoweredMethod {
    fn new(method: &Method) -> Self {
        let method = split_critical_edges(method);
        let dom = compute_dominance(&method);
        let dom_tree = dom.dominator_tree();
        let predecessors = predecessors(&method);
        LoweredMethod {
            method,
            dom,
            dom_tree,
            predecessors,

            max_reg: 0,
            spill_slots: HashMap::new(),
            nm_args: HashMap::new(),
            live_at: HashMap::new(),
            reg: HashMap::new(),
        }
    }
}

#[ext(name = NonMaterializedArgMapExt)]
impl HashMap<InstRef, HashSet<InstRef>> {
    fn is_materialized(&self, inst_ref: InstRef, arg_ref: InstRef) -> bool {
        self.get(&inst_ref)
            .map_or(true, |set| !set.contains(&arg_ref))
    }
}

/// Use callee-saved registers for now
// pub const REGS: [&str; 3] = ["%r12", "%r13", "%r14"];
// pub const REGS: [&str; 4] = ["%r12", "%r13", "%r14", "%r15"];
const CALLEE_SAVE_REGS: [&str; 5] = ["%r12", "%r13", "%r14", "%r15", "%rbx"];
const CALLER_SAVE_REGS: [&str; 7] = ["%r8", "%r9", "%r10", "%r11", "%rcx", "%rdi", "%rsi"];
const ARG_REGS: [&str; 6] = ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"];
lazy_static! {
    static ref REGS: Vec<&'static str> = {
        let mut regs = Vec::new();
        regs.extend_from_slice(&CALLEE_SAVE_REGS);
        regs.extend_from_slice(&CALLER_SAVE_REGS);
        regs
    };
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct PendingBoundsCheck {
    index: AsmArg,
    length: usize,
    line: usize,
}

pub struct Assembler {
    program: Program,
    // corresponds to .data
    data: Vec<String>,
    // corresponds to .text
    code: Vec<String>,
}

impl Assembler {
    pub fn new(program: Program) -> Self {
        Self {
            program,
            data: Vec::new(),
            code: Vec::new(),
        }
    }

    /// Emit a line of assembly to the data section
    fn emit_data_code<T: std::fmt::Display>(&mut self, code: T) {
        self.data.push(format!("    {}", code));
    }

    fn emit_data_label(&mut self, label: &str) {
        self.data.push(format!("{}:", label));
    }

    /// Emit a line of assembly to the code section
    fn emit_code<T: std::fmt::Display>(&mut self, code: T) {
        self.code.push(format!("    {}", code));
    }

    #[allow(dead_code)]
    fn emit_annotated_code<T: std::fmt::Display>(&mut self, code: T, annotation: &str) {
        self.code
            .push(format!("    {:<30}     # {}", code, annotation));
    }

    fn emit_label(&mut self, label: &str) {
        self.code.push(format!("{}:", label));
    }

    fn emit_annotated_label(&mut self, label: &str, annotation: &str) {
        self.code.push(format!("{}:     # {}", label, annotation));
    }

    pub fn assemble_lowered(&mut self, file_name: &str) -> String {
        // todo: remove the .clone()
        for global in self.program.globals.clone().values() {
            self.assemble_global(global);
        }

        for method in self.program.methods.clone().values() {
            // crate::utils::show_graphviz(&method.dump_graphviz());
            let mut lowered = LoweredMethod::new(method);
            ImmediateNonMaterializer::new(&mut lowered).run();
            Spiller::new(&self.program, &mut lowered, REGS.len()).spill();
            RegAllocator::new(&self.program, &mut lowered).allocate();
            MethodAssembler::new(self, &lowered).assemble_method();
        }

        self.emit_label("bounds_check.fail");
        self.emit_code("leaq index_out_of_bounds_msg(%rip), %rdi");
        self.emit_code("call printf");
        // Call exit(-1)
        self.emit_code("movq $-1, %rdi");
        self.emit_code("call exit");

        self.emit_data_label("index_out_of_bounds_msg");
        self.emit_data_code(".string \"Error: index out of bounds on line %d. Array length is %d; queried index is %d.\\n\"");

        self.emit_data_label("no_return_value_msg");
        self.emit_data_code(
            ".string \"Error: Method finished without returning anything when it should have.\\n\"",
        );

        let mut output = format!(".file 0 \"{}\"\n.data\n", file_name);
        for data in self.data.iter() {
            output.push_str(data.as_str());
            output.push('\n');
        }
        output.push('\n');
        output.push_str(".text\n");
        output.push_str(".globl main\n");
        for code in self.code.iter() {
            output.push_str(code.as_str());
            output.push('\n');
        }
        output
    }

    fn emit_const_data(&mut self, c: &Const) {
        match c {
            Const::Int(val) => self.emit_data_code(format!(".quad {}", val)),
            Const::Bool(val) => self.emit_data_code(format!(".quad {}", if *val { 1 } else { 0 })),
            Const::Array(val) => {
                for v in val.iter() {
                    self.emit_const_data(v);
                }
            }
            Const::Repeat(val, n) => match &**val {
                Const::Int(0) | Const::Bool(false) => {
                    // Fast path for zero-initialized arrays
                    self.emit_data_code(format!(".zero {}", c.size()));
                }
                _ => {
                    for _ in 0..*n {
                        self.emit_const_data(val);
                    }
                }
            },
        }
    }

    fn load_int_or_bool_const(&mut self, c: &Const, dst: &str) {
        match c {
            Const::Int(v) => {
                if *v <= i32::MAX as i64 && *v >= i32::MIN as i64 {
                    // Value fits within 32 bits, use movq
                    self.emit_code(format!("movq ${}, {}", v, dst));
                } else {
                    // Value requires more than 32 bits, use movabsq
                    self.emit_code(format!("movabsq ${}, {}", v, dst));
                }
            }
            Const::Bool(b) => {
                // Boolean values always fit within 32 bits
                let val = if *b { 1 } else { 0 };
                self.emit_code(format!("movq ${}, {}", val, dst));
            }
            _ => unreachable!(),
        }
    }

    fn assemble_global(&mut self, var: &GlobalVar) {
        self.emit_data_label(&var.name.inner);
        self.emit_const_data(&var.init);
        self.emit_data_code(".align 16");
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum AsmArg {
    Reg(&'static str),
    Imm(i64),
    Stack(i64),
}

impl fmt::Display for AsmArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AsmArg::Reg(reg) => write!(f, "{}", reg),
            AsmArg::Imm(imm) => write!(f, "${}", imm),
            AsmArg::Stack(offset) => write!(f, "{}(%rbp)", offset),
        }
    }
}

pub struct MethodAssembler<'a> {
    asm: &'a mut Assembler,
    l: &'a LoweredMethod,
    name: &'a str,

    regs: Vec<&'static str>,
    stack_slot_to_offset: HashMap<StackSlotRef, i64>,
    tainted_callee_saved_regs: BTreeSet<&'static str>,
    pending_bounds_check: BTreeSet<PendingBoundsCheck>,
}

impl<'a> MethodAssembler<'a> {
    fn new(asm: &'a mut Assembler, l: &'a LoweredMethod) -> Self {
        // crate::utils::show_graphviz(&l.method.dump_graphviz());
        Self {
            asm,
            name: &l.method.name.inner,
            stack_slot_to_offset: HashMap::new(),
            pending_bounds_check: BTreeSet::new(),
            tainted_callee_saved_regs: BTreeSet::new(),
            regs: REGS.clone(),
            l,
        }
    }

    fn emit_code<T: std::fmt::Display>(&mut self, code: T) {
        self.asm.emit_code(code);
    }

    fn emit_label(&mut self, label: &str) {
        self.asm.emit_label(label);
    }

    fn emit_data_code<T: std::fmt::Display>(&mut self, code: T) {
        self.asm.emit_data_code(code);
    }

    fn emit_data_label(&mut self, label: &str) {
        self.asm.emit_data_label(label);
    }

    fn emit_annotated_label(&mut self, label: &str, annotation: &str) {
        self.asm.emit_annotated_label(label, annotation);
    }

    fn emit_annotated_code<T: std::fmt::Display>(&mut self, code: T, annotation: &str) {
        self.asm.emit_annotated_code(code, annotation);
    }

    fn block_label(&self, block_ref: BlockRef) -> String {
        format!("{}.{}", self.name, block_ref)
    }

    fn emit_prologue(&mut self) {
        // Compute stack spaces
        let mut stack_space = 0i64;
        // Everything has a home on the stack -- for now?
        for (stack_slot_ref, stack_slot) in self.l.method.iter_slack_slots() {
            stack_space += stack_slot.ty.size() as i64;
            self.stack_slot_to_offset
                .insert(stack_slot_ref, -stack_space);
        }
        self.tainted_callee_saved_regs = self
            .l
            .reg
            .values()
            .map(|&r| self.regs[r])
            .filter(|&r| CALLEE_SAVE_REGS.contains(&r))
            .collect::<BTreeSet<_>>();
        // Align stack space to 16 bytes
        stack_space = (stack_space + 15) & !15;
        if self.tainted_callee_saved_regs.len() % 2 == 1 {
            // Extra 8 bytes to ensure stack is aligned to 16 bytes after
            // pushing all tainted callee-saved registers
            stack_space += 8;
        }

        self.emit_code(format!(
            ".loc 0 {} {}",
            self.l.method.span.start().line,
            self.l.method.span.start().column
        ));
        self.emit_code("push %rbp".to_string());
        self.emit_code("movq %rsp, %rbp".to_string());
        self.emit_code(format!("subq ${}, %rsp", stack_space));

        // Save all callee-saved registers
        let mut pushes = vec![];
        for reg in self.tainted_callee_saved_regs.iter() {
            pushes.push(format!("pushq {}", reg));
        }
        pushes.into_iter().for_each(|push| self.emit_code(push));

        {
            let n_args = self.l.method.params.len();
            for (arg_idx, arg_slot_iter) in self
                .l
                .method
                .iter_slack_slots()
                .enumerate()
                .take(n_args)
                .take(6)
            {
                self.emit_code(format!(
                    "movq {}, {}(%rbp)",
                    ARG_REGS[arg_idx], self.stack_slot_to_offset[&arg_slot_iter.0]
                ));
            }
            let mut stack_offset = 16; // return address is 8 bytes. saved rbp is also 8 bytes.
            for (arg_slot_ref, arg_slot) in self.l.method.iter_slack_slots().take(n_args).skip(6) {
                self.emit_code(format!("movq {}(%rbp), %rax", stack_offset));
                stack_offset += arg_slot.ty.size() as i64;
                self.emit_code(format!(
                    "movq %rax, {}(%rbp)",
                    self.stack_slot_to_offset[&arg_slot_ref]
                ));
            }
        }
    }

    fn emit_epilogue(&mut self) {
        // Restore all callee-saved registers
        for reg in self.tainted_callee_saved_regs.clone().into_iter().rev() {
            self.emit_code(format!("popq {}", reg));
        }
        // Restore stack frame
        self.emit_code("leave");
        self.emit_code("ret");
    }

    fn emit_block_label(&mut self, block_ref: BlockRef) {
        if let Some(block_annotation) = self.l.method.get_block_annotation(&block_ref) {
            self.emit_annotated_label(&self.block_label(block_ref), &block_annotation.to_string());
        } else {
            self.emit_label(&self.block_label(block_ref));
        }
    }

    fn reg(&self, inst_ref: impl Borrow<InstRef>) -> &'static str {
        let inst_ref = inst_ref.borrow();
        if let Some(reg) = self.l.reg.get(inst_ref) {
            self.regs[*reg]
        } else {
            panic!("no register assigned for {} ({:?})", inst_ref, self.l.reg);
        }
    }

    fn emit_inst_annotation(&mut self, inst_ref: InstRef) {
        if let Some(annotation) = self.l.method.get_inst_annotation(&inst_ref) {
            for span in annotation.spans() {
                let start_loc = span.start().to_owned();
                self.emit_annotated_code(
                    format!(".loc 0 {} {}", start_loc.line, start_loc.column),
                    &annotation.to_string(),
                );
            }
        } else {
            let inst = self.l.method.inst(inst_ref);
            self.emit_code(format!("# No annotation available for inst {}", inst));
        }
    }

    fn emit_succeeding_phis(&mut self, block_ref: BlockRef) {
        // println!("Handle phis for {}:{}", self.l.method.name.inner, block_ref);
        for_each_successor(&self.l.method, block_ref, |succ| {
            let mut par_copies_reg: HashSet<(usize, usize)> = HashSet::new();
            let mut par_copies_mem: HashSet<(usize, usize)> = HashSet::new();
            for inst_ref in self.l.method.block(succ).insts.iter() {
                match self.l.method.inst(*inst_ref) {
                    Inst::Phi(map) => {
                        let var = map[&block_ref];
                        if self.l.reg.contains_key(inst_ref) {
                            par_copies_reg.insert((self.l.reg[&var], self.l.reg[inst_ref]));
                        }
                    }
                    Inst::PhiMem { src, dst } => {
                        par_copies_mem.insert((src[&block_ref].0, dst.0));
                    }
                    _ => break,
                }
            }
            if !par_copies_reg.is_empty() || !par_copies_mem.is_empty() {
                self.emit_code(format!(
                    "# Phi reg: {:?} mem: {:?}",
                    par_copies_reg, par_copies_mem
                ));
            }
            self.emit_par_reg_copies(par_copies_reg);
            self.emit_par_mem_copies(par_copies_mem);
        });
    }

    fn emit_terminator(&mut self, block_ref: BlockRef) {
        self.emit_code(format!(
            "# Terminating block {}",
            self.block_label(block_ref)
        ));
        match &self.l.method.block(block_ref).term {
            Terminator::Return(ret) => {
                if self.l.method.return_ty != Type::Void && ret.is_none() {
                    // method finished without returning anything, but it should have. exit with -2
                    self.emit_code("leaq no_return_value_msg(%rip), %rdi");
                    self.emit_code("call printf");
                    self.emit_code("movq $-2, %rdi");
                    self.emit_code("call exit");
                } else {
                    if let Some(ret) = ret {
                        if let Some(annotation) = self.l.method.get_inst_annotation(ret) {
                            for span in annotation.spans() {
                                self.emit_code(format!(
                                    ".loc 0 {} {}",
                                    span.start().line,
                                    span.start().column
                                ));
                            }
                        }
                        self.emit_code(format!("movq {}, %rax", self.reg(*ret)));
                    }
                    self.emit_code(format!(
                        ".loc 0 {} {}",
                        self.l.method.span.end().line,
                        self.l.method.span.end().column - 1 // exclusive
                    ));
                    if self.l.method.name.inner.as_ref() == "main" {
                        assert!(ret.is_none());
                        // return 0;
                        self.emit_code("movq $0, %rax");
                    }
                    self.emit_epilogue();
                }
            }
            Terminator::Jump(target) => {
                self.emit_code(format!("jmp {}", self.block_label(*target)));
            }
            Terminator::CondJump {
                cond,
                true_,
                false_,
            } => {
                self.emit_code(format!("cmpq $0, {}", self.reg(*cond)));
                self.emit_code(format!("je {}", self.block_label(*false_)));
                self.emit_code(format!("jmp {}", self.block_label(*true_)));
            }
        }
    }

    pub fn assemble_method(mut self) {
        let method_name = &self.l.method.name.inner;
        self.emit_label(method_name);
        self.emit_prologue();
        let rev_postorder = reverse_postorder(&self.l.method);

        for block_ref in rev_postorder.iter().cloned() {
            self.emit_block_label(block_ref);
            let insts = &self.l.method.block(block_ref).insts;
            for (i, inst_ref) in insts.iter().enumerate() {
                self.emit_inst_annotation(*inst_ref);
                let inst = self.l.method.inst(*inst_ref);
                macro_rules! skip_non_side_effective {
                    () => {
                        // Reg allocator did not assign a register to this
                        // instruction because it's result is dead.
                        if !self.l.reg.contains_key(inst_ref) {
                            continue;
                        }
                    };
                }
                match inst {
                    Inst::Phi(_) | Inst::PhiMem { .. } => continue, // They are taken care of elsewhere!
                    Inst::Copy(src) => {
                        skip_non_side_effective!();
                        self.emit_code(format!(
                            "movq {}, {}",
                            self.arg(*inst_ref, *src),
                            self.reg(inst_ref)
                        ));
                    }
                    Inst::Add(lhs, rhs) | Inst::Sub(lhs, rhs) | Inst::Mul(lhs, rhs) => {
                        skip_non_side_effective!();
                        let asm_inst = match inst {
                            Inst::Add(_, _) => "addq",
                            Inst::Sub(_, _) => "subq",
                            Inst::Mul(_, _) => "imulq",
                            _ => unreachable!(),
                        };
                        let dst_reg = self.reg(inst_ref);
                        match (self.arg(*inst_ref, *lhs), self.arg(*inst_ref, *rhs)) {
                            (AsmArg::Imm(l), AsmArg::Imm(r)) => {
                                // This really should have been handled by constant propagation.
                                let v = match inst {
                                    Inst::Add(_, _) => l + r,
                                    Inst::Sub(_, _) => l - r,
                                    Inst::Mul(_, _) => l * r,
                                    _ => unreachable!(),
                                };
                                self.emit_code(format!("movq ${}, {}", v, dst_reg));
                            }
                            (AsmArg::Imm(l), AsmArg::Reg(r)) => {
                                // TODO: imul has special instructions for immediate operands
                                if r != dst_reg {
                                    self.emit_code(format!("movq {}, {}", r, dst_reg));
                                }
                                self.emit_code(format!("{} ${}, {}", asm_inst, l, dst_reg));
                                if let Inst::Sub(_, _) = inst {
                                    self.emit_code(format!("negq {}", dst_reg));
                                }
                            }
                            (AsmArg::Reg(l), AsmArg::Imm(r)) => {
                                // TODO: imul has special instructions for immediate operands
                                if l != dst_reg {
                                    self.emit_code(format!("movq {}, {}", l, dst_reg));
                                }
                                self.emit_code(format!("{} ${}, {}", asm_inst, r, dst_reg));
                            }
                            (AsmArg::Reg(l), AsmArg::Reg(r)) => {
                                if l == dst_reg {
                                    self.emit_code(format!("{} {}, {}", asm_inst, r, dst_reg));
                                } else if r == dst_reg {
                                    self.emit_code(format!("{} {}, {}", asm_inst, l, dst_reg));
                                    if let Inst::Sub(_, _) = inst {
                                        self.emit_code(format!("negq {}", dst_reg));
                                    }
                                } else {
                                    self.emit_code(format!("movq {}, {}", l, dst_reg));
                                    self.emit_code(format!("{} {}, {}", asm_inst, r, dst_reg));
                                }
                            }
                            _ => unimplemented!(),
                        }
                    }
                    Inst::Div(lhs, rhs) | Inst::Mod(lhs, rhs) => {
                        skip_non_side_effective!();
                        // println!("{:?}", self.l.reg);
                        self.emit_code(format!("movq {}, %rax", self.reg(lhs)));
                        self.emit_code("cqto"); // Godbolt does it
                        self.emit_code(format!("idivq {}", self.reg(rhs)));
                        // TODO: idivq taints rdx and rax!
                        self.emit_code(format!(
                            "movq {}, {}",
                            match inst {
                                Inst::Div(_, _) => "%rax",
                                Inst::Mod(_, _) => "%rdx",
                                _ => unreachable!(),
                            },
                            self.reg(inst_ref)
                        ));
                    }
                    Inst::Neg(var) => {
                        skip_non_side_effective!();
                        if self.l.reg[var] != self.l.reg[inst_ref] {
                            self.emit_code(format!(
                                "movq {}, {}",
                                self.reg(var),
                                self.reg(inst_ref)
                            ));
                        }
                        self.emit_code(format!("negq {}", self.reg(inst_ref)));
                    }
                    Inst::Not(var) => {
                        skip_non_side_effective!();
                        self.emit_code(format!("cmpq $0, {}", self.reg(var)));
                        self.emit_code("sete %al");
                        self.emit_code(format!("movzbq %al, {}", self.reg(inst_ref)));
                    }
                    Inst::Eq(lhs, rhs)
                    | Inst::Neq(lhs, rhs)
                    | Inst::Less(lhs, rhs)
                    | Inst::LessEq(lhs, rhs) => {
                        skip_non_side_effective!();
                        let inst_name = match inst {
                            Inst::Eq(_, _) => "sete",
                            Inst::Neq(_, _) => "setne",
                            Inst::Less(_, _) => "setl",
                            Inst::LessEq(_, _) => "setle",
                            _ => unreachable!(),
                        };
                        self.emit_code(format!("cmpq {}, {}", self.reg(rhs), self.reg(lhs)));
                        self.emit_code(format!("{} %al", inst_name));
                        self.emit_code(format!("movzbq %al, {}", self.reg(inst_ref)));
                    }
                    Inst::LoadConst(c) => {
                        skip_non_side_effective!();
                        self.asm.load_int_or_bool_const(c, self.reg(inst_ref));
                    }
                    Inst::Load(addr) => {
                        skip_non_side_effective!();
                        match addr {
                            Address::Global(name) => {
                                self.emit_code(format!(
                                    "movq {}(%rip), {}",
                                    name,
                                    self.reg(inst_ref)
                                ));
                            }
                            Address::Local(stack_slot) => {
                                self.emit_code(format!(
                                    "movq {}(%rbp), {}",
                                    self.stack_slot_to_offset[stack_slot],
                                    self.reg(inst_ref)
                                ));
                            }
                        }
                    }
                    Inst::Store { addr, value } => match addr {
                        Address::Global(name) => {
                            self.emit_code(format!("movq {}, {}(%rip)", self.reg(value), name));
                        }
                        Address::Local(stack_slot) => {
                            self.emit_code(format!(
                                "movq {}, {}(%rbp)",
                                self.reg(value),
                                self.stack_slot_to_offset[stack_slot]
                            ));
                        }
                    },
                    Inst::LoadArray { addr, index } => {
                        skip_non_side_effective!();
                        // Do bound check first
                        let (length, elem_size) =
                            match self.asm.program.infer_address_type(&self.l.method, addr) {
                                Type::Array { length, base } => (*length, base.size() as i64),
                                _ => unreachable!(),
                            };
                        self.emit_bounds_check(*inst_ref, *index, length);
                        let dst_reg = self.reg(inst_ref);
                        match (addr, self.arg(*inst_ref, *index)) {
                            (Address::Global(name), AsmArg::Reg(reg)) => {
                                self.emit_code(format!(
                                    "movq {}(, {}, {}), {}",
                                    name, reg, elem_size, dst_reg
                                ));
                            }
                            (Address::Global(name), AsmArg::Imm(i)) => {
                                let sym_name = format!("{}.{}", name, i);
                                let offset = i * elem_size;
                                self.emit_code(format!(".set {}, {} + {}", sym_name, name, offset));
                                // (,1) is a syntactic exception in AT&T syntax
                                self.emit_code(format!("movq {}(,1), {}", sym_name, dst_reg));
                            }
                            (Address::Local(stack_slot), AsmArg::Reg(reg)) => {
                                let offset = self.stack_slot_to_offset[stack_slot];
                                self.emit_code(format!(
                                    "movq {}(%rbp, {}, {}), {}",
                                    offset, reg, elem_size, dst_reg
                                ));
                            }
                            (Address::Local(stack_slot), AsmArg::Imm(i)) => {
                                let offset = self.stack_slot_to_offset[stack_slot] + i * elem_size;
                                self.emit_code(format!("movq {}(%rbp), {}", offset, dst_reg));
                            }
                            _ => unreachable!(),
                        }
                    }
                    Inst::StoreArray { addr, index, value } => {
                        let (length, elem_size) =
                            match self.asm.program.infer_address_type(&self.l.method, addr) {
                                Type::Array { length, base } => (*length, base.size() as i64),
                                _ => unreachable!(),
                            };
                        self.emit_bounds_check(*inst_ref, *index, length);
                        let value = self.arg(*inst_ref, *value);
                        match (addr, self.arg(*inst_ref, *index)) {
                            (Address::Global(name), AsmArg::Reg(reg)) => {
                                self.emit_code(format!(
                                    "movq {}, {}(, {}, {})",
                                    value, name, reg, elem_size
                                ));
                            }
                            (Address::Global(name), AsmArg::Imm(i)) => {
                                let sym_name = format!("{}.{}", name, i);
                                let offset = i * elem_size;
                                self.emit_code(format!(".set {}, {} + {}", sym_name, name, offset));
                                self.emit_code(format!("movq {}, {}(,1)", value, sym_name));
                            }
                            (Address::Local(stack_slot), AsmArg::Reg(reg)) => {
                                self.emit_code(format!(
                                    "movq {}, {}(%rbp, {}, {})",
                                    value, self.stack_slot_to_offset[stack_slot], reg, elem_size
                                ));
                            }
                            (Address::Local(stack_slot), AsmArg::Imm(i)) => {
                                let offset = self.stack_slot_to_offset[stack_slot] + i * elem_size;
                                self.emit_code(format!("movq {}, {}(%rbp)", value, offset));
                            }
                            _ => unreachable!(),
                        }
                    }
                    Inst::Initialize { stack_slot, value } => {
                        self.emit_local_initialize(value, self.stack_slot_to_offset[&stack_slot])
                    }
                    Inst::LoadStringLiteral(s) => {
                        skip_non_side_effective!();
                        let str_name = format!("str_{}", self.asm.data.len());
                        self.emit_data_label(&str_name);
                        self.emit_data_code(format!(".string {:?}", s));
                        self.emit_code(format!("leaq {}(%rip), {}", str_name, self.reg(inst_ref)));
                    }
                    Inst::Call { .. } => {
                        let next_pt = if i == insts.len() - 1 {
                            ProgPt::BeforeTerm(block_ref)
                        } else {
                            ProgPt::BeforeInst(insts[i + 1])
                        };
                        self.emit_call(*inst_ref, next_pt);
                    }
                    Inst::Illegal => todo!(),
                }
            }
            // Handle phis
            self.emit_succeeding_phis(block_ref);
            self.emit_terminator(block_ref);
        }
        self.flush_bounds_check();
    }

    fn emit_par_reg_copies(&mut self, par_copies: HashSet<(usize, usize)>) {
        if !par_copies.is_empty() {
            for step in serialize_copies(par_copies, None) {
                match step {
                    SerializedStep::Copy { from, to } => {
                        self.emit_code(format!("movq {}, {}", self.regs[from], self.regs[to]))
                    }
                    SerializedStep::Swap(a, b) => {
                        self.emit_code(format!("xchg {}, {}", self.regs[a], self.regs[b]))
                    }
                }
            }
        }
    }

    fn emit_par_mem_copies(&mut self, par_copies: HashSet<(usize, usize)>) {
        if !par_copies.is_empty() {
            for step in serialize_copies(par_copies, None) {
                match step {
                    SerializedStep::Copy { from, to } => {
                        let from = self.stack_slot_to_offset[&StackSlotRef(from)];
                        let to = self.stack_slot_to_offset[&StackSlotRef(to)];
                        self.emit_code(format!("movq {}(%rbp), %rax", from));
                        self.emit_code(format!("movq %rax, {}(%rbp)", to));
                    }
                    SerializedStep::Swap(a, b) => {
                        // Push pop
                        let a = self.stack_slot_to_offset[&StackSlotRef(a)];
                        let b = self.stack_slot_to_offset[&StackSlotRef(b)];
                        self.emit_code(format!("pushq {}(%rbp)", a));
                        self.emit_code(format!("pushq {}(%rbp)", b));
                        self.emit_code(format!("popq {}(%rbp)", a));
                        self.emit_code(format!("popq {}(%rbp)", b));
                    }
                }
            }
        }
    }

    fn emit_call(&mut self, inst_ref: InstRef, next_pt: ProgPt) {
        let Inst::Call {
            method: callee_name,
            args,
        } = self.l.method.inst(inst_ref)
        else {
            unreachable!();
        };
        let saving_regs = self.l.live_at[&next_pt]
            .iter()
            .filter_map(|v| self.l.reg.get(v))
            .filter(|v| CALLER_SAVE_REGS.contains(&self.regs[**v]))
            .collect::<BTreeSet<_>>();
        for reg in saving_regs.iter() {
            self.emit_code(format!("pushq {}", self.regs[**reg]));
        }

        let mut stack_space_for_args = 0;
        let n_remaining_args = args.len().saturating_sub(6);
        if (n_remaining_args + saving_regs.len()) % 2 == 1 {
            // Align stack to 16 bytes
            self.emit_code("subq $8, %rsp".to_string());
            stack_space_for_args += 8;
        }
        for arg_ref in args.iter().skip(6).rev() {
            match self.arg(inst_ref, *arg_ref) {
                arg @ (AsmArg::Reg(_) | AsmArg::Stack(_)) => {
                    self.emit_code(format!("pushq {}", arg));
                }
                // If immediate fits in 32 bits, use $imm
                AsmArg::Imm(imm) => {
                    if imm <= i32::MAX as i64 && imm >= i32::MIN as i64 {
                        self.emit_code(format!("pushq ${}", imm));
                    } else {
                        // Use rax as a temporary register
                        self.emit_code(format!("movq ${}, %rax", imm));
                        self.emit_code("pushq %rax");
                    }
                }
            }
            stack_space_for_args += 8;
        }

        let mut par_copies = HashSet::new();
        let mut ser_copies = vec![];
        for (arg_idx, arg_ref) in args.iter().enumerate().take(6) {
            let arg = self.arg(inst_ref, *arg_ref);
            let dst_reg = ARG_REGS[arg_idx];
            match arg {
                AsmArg::Reg(arg_reg) if ARG_REGS.contains(&arg_reg) => {
                    if let Some(dst_reg_idx) = self.regs.iter().position(|r| *r == dst_reg) {
                        let arg_reg_idx = self.regs.iter().position(|r| *r == arg_reg).unwrap();
                        par_copies.insert((arg_reg_idx, dst_reg_idx));
                    } else {
                        ser_copies.push((arg, dst_reg));
                    }
                }
                _ => ser_copies.push((arg, dst_reg)),
            }
        }
        if !par_copies.is_empty() {
            self.emit_code(format!("# Parallel argument copy: {:?}", par_copies));
            self.emit_par_reg_copies(par_copies);
        }
        for (arg, dst_reg) in ser_copies {
            self.emit_code(format!("movq {}, {}", arg, dst_reg,));
        }
        self.emit_code(format!("call {}", callee_name));
        if stack_space_for_args > 0 {
            self.emit_code(format!("addq ${}, %rsp", stack_space_for_args));
        }
        let returns_value = match self.asm.program.methods.get(&callee_name.to_string()) {
            Some(method) => method.return_ty != Type::Void,
            None => true,
        };
        for reg in saving_regs.iter().rev() {
            self.emit_code(format!("popq {}", self.regs[**reg]));
        }
        if returns_value && self.l.reg.contains_key(&inst_ref) {
            self.emit_code(format!("movq %rax, {}", self.reg(inst_ref)));
        }
    }

    fn arg(&self, inst_ref: InstRef, arg_ref: InstRef) -> AsmArg {
        if self.l.nm_args.is_materialized(inst_ref, arg_ref) {
            AsmArg::Reg(self.reg(arg_ref))
        } else {
            match self.l.method.inst(arg_ref) {
                Inst::LoadConst(c) => match c {
                    Const::Int(val) => AsmArg::Imm(*val),
                    Const::Bool(val) => AsmArg::Imm(*val as i64),
                    _ => unreachable!(),
                },
                _ => {
                    let spill_slot = self
                        .l
                        .spill_slots
                        .get(&arg_ref)
                        .expect("spill slot not found");
                    let offset = self.stack_slot_to_offset[spill_slot];
                    AsmArg::Stack(offset)
                }
            }
        }
    }

    fn get_bound_check_fail_label(&self, index: &AsmArg, length: usize, line: usize) -> String {
        format!(
            "{}.bound_check_fail.{}.{}.{}",
            &self.name,
            &index.to_string()[1..], // Remove the % or $ sign
            length,
            line
        )
    }

    /// Checks if %rax is in [0, length) and panics if not
    fn emit_bounds_check(&mut self, inst_ref: InstRef, val: InstRef, length: usize) {
        let line = self
            .l
            .method
            .get_inst_annotation(&val)
            .and_then(|a| a.spans().first().cloned())
            .map(|s| s.start().line)
            .unwrap_or(0); // TODO: better error handling
        let index = self.arg(inst_ref, val);
        let fail_branch = self.get_bound_check_fail_label(&index, length, line);
        match index {
            AsmArg::Reg(reg) => {
                self.emit_code(format!("cmpq ${}, {}", length - 1, reg));
                self.emit_code(format!("ja {}", fail_branch)); // Unsigned comparison
                self.pending_bounds_check.insert(PendingBoundsCheck {
                    index,
                    length,
                    line,
                });
            }
            AsmArg::Imm(i) => {
                if i < 0 || i >= length as i64 {
                    self.emit_code(format!("jmp {}", fail_branch));
                    self.pending_bounds_check.insert(PendingBoundsCheck {
                        index,
                        length,
                        line,
                    });
                }
            }
            _ => unreachable!(),
        }
    }

    fn flush_bounds_check(&mut self) {
        for PendingBoundsCheck {
            index,
            length,
            line,
        } in std::mem::take(&mut self.pending_bounds_check)
        {
            // first argument is the format string, second is the line number, third is arr.len, fourth is the index
            let fail_branch = self.get_bound_check_fail_label(&index, length, line);
            self.emit_label(&fail_branch);
            self.emit_code(format!("movq {}, %rcx", index));
            self.emit_code(format!("movq ${}, %rsi", line));
            self.emit_code(format!("movq ${}, %rdx", length));
            self.emit_code("jmp bounds_check.fail");
        }
    }

    fn emit_local_initialize(&mut self, c: &Const, mut stack_offset: i64) {
        match c {
            Const::Int(_) | Const::Bool(_) => {
                self.asm
                    .load_int_or_bool_const(c, &format!("{}(%rbp)", stack_offset));
            }
            Const::Array(arr_vals) => {
                for val in arr_vals.iter() {
                    self.asm
                        .load_int_or_bool_const(val, &format!("{}(%rbp)", stack_offset));
                    stack_offset += val.size() as i64;
                }
            }
            Const::Repeat(val, n) => match &**val {
                Const::Int(0) | Const::Bool(false) => {
                    // TODO: use rep stosq
                    // Use memset to zero out the memory
                    for reg in CALLER_SAVE_REGS.iter() {
                        self.emit_code(format!("pushq {}", reg));
                    }
                    self.emit_code("subq $8, %rsp");
                    self.emit_code(format!("leaq {}(%rbp), %rdi", stack_offset));
                    self.emit_code("movq $0, %rsi");
                    self.emit_code(format!("movq ${}, %rdx", n * val.size()));
                    self.emit_code("call memset");
                    self.emit_code("addq $8, %rsp");
                    for reg in CALLER_SAVE_REGS.iter().rev() {
                        self.emit_code(format!("popq {}", reg));
                    }
                }
                _ => {
                    for _ in 0..*n {
                        self.asm
                            .load_int_or_bool_const(val, &format!("{}(%rbp)", stack_offset));
                        stack_offset += val.size() as i64;
                    }
                }
            },
        }
    }
}
