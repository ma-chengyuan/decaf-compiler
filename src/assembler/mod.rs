use std::collections::{BTreeSet, HashMap, HashSet};

use crate::{
    assembler::par_copy::{serialize_copies, SerializedStep},
    inter::{
        constant::Const,
        ir::{
            Address, Annotation, BlockRef, GlobalVar, Inst, InstRef, Method, ProgPt, Program,
            StackSlotRef, Terminator,
        },
        types::Type,
    },
    opt::{dom::Dominance, for_each_successor, reverse_postorder},
};

use self::{regalloc::RegAllocator, spill::Spiller};

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

    // Filled in by the spiller
    /// A mapping from spilled variables to their spill slots.
    pub spill_slots: HashMap<InstRef, StackSlotRef>,
    /// For large calls, some arguments may be passed in memory.
    pub mem_args: HashMap<InstRef, HashSet<InstRef>>,

    // Filled in by the register allocator
    pub live_at: HashMap<ProgPt, im::HashSet<InstRef>>,
    pub reg: HashMap<InstRef, usize>,
}

/// Use callee-saved registers for now
// pub const REGS: [&str; 3] = ["%r12", "%r13", "%r14"];
// pub const REGS: [&str; 4] = ["%r12", "%r13", "%r14", "%r15"];
pub const REGS: [&str; 5] = ["%r12", "%r13", "%r14", "%r15", "%rbx"];

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
        self.code.push(format!("    {}     # {}", code, annotation));
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
            let mut lowered = Spiller::new(&self.program, method, REGS.len()).spill();
            RegAllocator::new(&self.program, &mut lowered).allocate();
            self.assemble_lowered_method(&lowered);
        }

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

    fn assemble_lowered_method(&mut self, l: &LoweredMethod) {
        self.emit_label(&l.method.name.inner);
        let arg_registers = ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"];

        // Compute stack spaces
        let mut stack_space = 0i64;
        // Everything has a home on the stack -- for now?
        let mut stack_slot_to_offset: HashMap<StackSlotRef, i64> = HashMap::new();
        for (stack_slot_ref, stack_slot) in l.method.iter_slack_slots() {
            stack_space += stack_slot.ty.size() as i64;
            stack_slot_to_offset.insert(stack_slot_ref, -stack_space);
        }
        let mut block_ref_to_label: Vec<String> = vec![Default::default(); l.method.n_blocks()];
        for block_ref in l.method.iter_block_refs() {
            block_ref_to_label[block_ref.0] =
                format!("{}_method_{}", block_ref, l.method.name.inner);
        }
        let tainted_callee_saved_regs = l
            .reg
            .values()
            .map(|&r| REGS[r])
            .filter(|&r| ["%rbx", "%r12", "%r13", "%r14", "%r15"].contains(&r))
            .collect::<BTreeSet<_>>();
        // Align stack space to 16 bytes
        stack_space = (stack_space + 15) & !15;
        if tainted_callee_saved_regs.len() % 2 == 1 {
            // Extra 8 bytes to ensure stack is aligned to 16 bytes after
            // pushing all tainted callee-saved registers
            stack_space += 8;
        }

        self.emit_code(format!(
            ".loc 0 {} {}",
            l.method.span.start().line,
            l.method.span.start().column
        ));
        self.emit_code("push %rbp".to_string());
        self.emit_code("movq %rsp, %rbp".to_string());
        self.emit_code(format!("subq ${}, %rsp", stack_space));

        // Save all callee-saved registers
        for reg in tainted_callee_saved_regs.iter() {
            self.emit_code(format!("pushq {}", reg));
        }

        {
            let n_args = l.method.params.len();
            for (arg_idx, arg_slot_iter) in
                l.method.iter_slack_slots().enumerate().take(n_args).take(6)
            {
                self.emit_code(format!(
                    "movq {}, {}(%rbp)",
                    arg_registers[arg_idx], stack_slot_to_offset[&arg_slot_iter.0]
                ));
            }
            let mut stack_offset = 16; // return address is 8 bytes. saved rbp is also 8 bytes.
            for (arg_slot_ref, arg_slot) in l.method.iter_slack_slots().take(n_args).skip(6) {
                self.emit_code(format!("movq {}(%rbp), %rax", stack_offset));
                stack_offset += arg_slot.ty.size() as i64;
                self.emit_code(format!(
                    "movq %rax, {}(%rbp)",
                    stack_slot_to_offset[&arg_slot_ref]
                ));
            }
        }
        let rev_postorder = reverse_postorder(&l.method);

        macro_rules! reg {
            ($x:expr) => {
                REGS[l.reg[$x]]
            };
        }
        for block_ref in rev_postorder.iter().cloned() {
            if let Some(block_annotation) = l.method.get_block_annotation(&block_ref) {
                self.emit_annotated_label(
                    &block_ref_to_label[block_ref.0],
                    &block_annotation.to_string(),
                );
            } else {
                self.emit_label(&block_ref_to_label[block_ref.0]);
            }
            for inst_ref in l.method.block(block_ref).insts.iter() {
                let inst = l.method.inst(*inst_ref);
                if let Some(annotation) = l.method.get_inst_annotation(inst_ref) {
                    for span in annotation.spans() {
                        let start_loc = span.start().to_owned();
                        self.emit_annotated_code(
                            format!(".loc 0 {} {}", start_loc.line, start_loc.column),
                            &annotation.to_string(),
                        );
                    }
                } else {
                    self.emit_code(format!("# No annotation available for inst {}", inst));
                }

                macro_rules! skip_non_side_effective {
                    () => {
                        // Reg allocator did not assign a register to this
                        // instruction because it's result is dead.
                        if !l.reg.contains_key(inst_ref) {
                            continue;
                        }
                    };
                }
                match inst {
                    Inst::Phi(_) | Inst::PhiMem { .. } => continue, // They are taken care of elsewhere!
                    Inst::Copy(src) => {
                        skip_non_side_effective!();
                        self.emit_code(format!("movq {}, {}", reg![src], reg![inst_ref]));
                    }
                    Inst::Add(lhs, rhs) | Inst::Sub(lhs, rhs) | Inst::Mul(lhs, rhs) => {
                        skip_non_side_effective!();
                        let cmd = match inst {
                            Inst::Add(_, _) => "add",
                            Inst::Sub(_, _) => "sub",
                            Inst::Mul(_, _) => "imul",
                            _ => unreachable!(),
                        };
                        if l.reg[lhs] == l.reg[inst_ref] {
                            self.emit_code(format!("{}q {}, {}", cmd, reg![rhs], reg![inst_ref]));
                        } else if l.reg[rhs] == l.reg[inst_ref] {
                            self.emit_code(format!("{}q {}, {}", cmd, reg![lhs], reg![inst_ref]));
                            if let Inst::Sub(_, _) = inst {
                                // Make up for the fact that we swapped the operands
                                self.emit_code(format!("negq {}", reg![inst_ref]));
                            }
                        } else {
                            self.emit_code(format!("movq {}, {}", reg![lhs], reg![inst_ref]));
                            self.emit_code(format!("{}q {}, {}", cmd, reg![rhs], reg![inst_ref]));
                        }
                    }
                    Inst::Div(lhs, rhs) | Inst::Mod(lhs, rhs) => {
                        skip_non_side_effective!();
                        // println!("{:?}", l.reg);
                        self.emit_code(format!("movq {}, %rax", reg![lhs]));
                        self.emit_code("cqto"); // Godbolt does it
                        self.emit_code(format!("idivq {}", reg![rhs]));
                        // TODO: idivq taints rdx and rax!
                        self.emit_code(format!(
                            "movq {}, {}",
                            match inst {
                                Inst::Div(_, _) => "%rax",
                                Inst::Mod(_, _) => "%rdx",
                                _ => unreachable!(),
                            },
                            reg![inst_ref]
                        ));
                    }
                    Inst::Neg(var) => {
                        skip_non_side_effective!();
                        if l.reg[var] != l.reg[inst_ref] {
                            self.emit_code(format!("movq {}, {}", reg![var], reg![inst_ref]));
                        }
                        self.emit_code(format!("negq {}", reg![inst_ref]));
                    }
                    Inst::Not(var) => {
                        skip_non_side_effective!();
                        self.emit_code(format!("cmpq $0, {}", reg![var]));
                        self.emit_code("sete %al");
                        self.emit_code(format!("movzbq %al, {}", reg![inst_ref]));
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
                        self.emit_code(format!("cmpq {}, {}", reg![rhs], reg![lhs]));
                        self.emit_code(format!("{} %al", inst_name));
                        self.emit_code(format!("movzbq %al, {}", reg![inst_ref]));
                    }
                    Inst::LoadConst(c) => {
                        skip_non_side_effective!();
                        self.load_int_or_bool_const(c, reg![inst_ref]);
                    }
                    Inst::Load(addr) => {
                        skip_non_side_effective!();
                        match addr {
                            Address::Global(name) => {
                                self.emit_code(format!("movq {}(%rip), {}", name, reg![inst_ref]));
                            }
                            Address::Local(stack_slot) => {
                                self.emit_code(format!(
                                    "movq {}(%rbp), {}",
                                    stack_slot_to_offset[stack_slot],
                                    reg![inst_ref]
                                ));
                            }
                        }
                    }
                    Inst::Store { addr, value } => match addr {
                        Address::Global(name) => {
                            self.emit_code(format!("movq {}, {}(%rip)", reg![value], name));
                        }
                        Address::Local(stack_slot) => {
                            self.emit_code(format!(
                                "movq {}, {}(%rbp)",
                                reg![value],
                                stack_slot_to_offset[stack_slot]
                            ));
                        }
                    },
                    Inst::LoadArray { addr, index } => {
                        skip_non_side_effective!();
                        // Do bound check first
                        let (length, elem_size) =
                            match self.program.infer_address_type(&l.method, addr) {
                                Type::Array { length, base } => (*length, base.size()),
                                _ => unreachable!(),
                            };
                        self.emit_bounds_check(
                            reg![index],
                            length,
                            l.method.get_inst_annotation(index),
                        );
                        match addr {
                            Address::Global(name) => {
                                self.emit_code(format!(
                                    "movq {}(, {}, {}), {}",
                                    name,
                                    reg![index],
                                    elem_size,
                                    reg![inst_ref]
                                ));
                            }
                            Address::Local(stack_slot) => {
                                self.emit_code(format!(
                                    "movq {}(%rbp, {}, {}), {}",
                                    stack_slot_to_offset[stack_slot],
                                    reg![index],
                                    elem_size,
                                    reg![inst_ref]
                                ));
                            }
                        }
                    }
                    Inst::StoreArray { addr, index, value } => {
                        let (length, elem_size) =
                            match self.program.infer_address_type(&l.method, addr) {
                                Type::Array { length, base } => (*length, base.size()),
                                _ => unreachable!(),
                            };
                        self.emit_bounds_check(
                            reg![index],
                            length,
                            l.method.get_inst_annotation(index),
                        );
                        match addr {
                            Address::Global(name) => {
                                self.emit_code(format!(
                                    "movq {}, {}(, {}, {})",
                                    reg![value],
                                    name,
                                    reg![index],
                                    elem_size
                                ));
                            }
                            Address::Local(stack_slot) => {
                                self.emit_code(format!(
                                    "movq {}, {}(%rbp, {}, {})",
                                    reg![value],
                                    stack_slot_to_offset[stack_slot],
                                    reg![index],
                                    elem_size
                                ));
                            }
                        }
                    }
                    Inst::Initialize { stack_slot, value } => {
                        self.emit_local_initialize(value, stack_slot_to_offset[&stack_slot])
                    }
                    Inst::LoadStringLiteral(s) => {
                        skip_non_side_effective!();
                        let str_name = format!("str_{}", self.data.len());
                        self.emit_data_label(&str_name);
                        self.emit_data_code(format!(".string {:?}", s));
                        self.emit_code(format!("leaq {}(%rip), {}", str_name, reg![inst_ref]));
                    }
                    Inst::Call {
                        method: callee_name,
                        args,
                    } => {
                        let get_arg = |arg_ref: &InstRef| {
                            if l.mem_args
                                .get(inst_ref)
                                .map_or(false, |mem| mem.contains(arg_ref))
                            {
                                let stack_slot = l.spill_slots[arg_ref];
                                format!("{}(%rbp)", stack_slot_to_offset[&stack_slot])
                            } else {
                                reg![arg_ref].to_string()
                            }
                        };
                        for (arg_idx, arg_ref) in args.iter().enumerate().take(6) {
                            self.emit_code(format!(
                                "movq {}, {}",
                                get_arg(arg_ref),
                                arg_registers[arg_idx]
                            ));
                        }
                        let n_remaining_args = args.len().saturating_sub(6);
                        let mut stack_space_for_args = 0;
                        if n_remaining_args % 2 == 1 {
                            // Align stack to 16 bytes
                            self.emit_code("subq $8, %rsp".to_string());
                            stack_space_for_args += 8;
                        }
                        for arg_ref in args.iter().skip(6).rev() {
                            self.emit_code(format!("pushq {}", get_arg(arg_ref)));
                            stack_space_for_args += 8;
                        }
                        self.emit_code(format!("call {}", callee_name));
                        if stack_space_for_args > 0 {
                            self.emit_code(format!("addq ${}, %rsp", stack_space_for_args));
                        }
                        let returns_value = match self.program.methods.get(&callee_name.to_string())
                        {
                            Some(method) => method.return_ty != Type::Void,
                            None => true,
                        };
                        if returns_value && l.reg.contains_key(inst_ref) {
                            self.emit_code(format!("movq %rax, {}", reg![inst_ref]));
                        }
                    }
                    Inst::Illegal => todo!(),
                }
            }
            // Handle phis
            // println!("Handle phis for {}:{}", l.method.name.inner, block_ref);
            for_each_successor(&l.method, block_ref, |succ| {
                let mut par_copies_reg: HashSet<(usize, usize)> = HashSet::new();
                let mut par_copies_mem: HashSet<(usize, usize)> = HashSet::new();
                for inst_ref in l.method.block(succ).insts.iter() {
                    match l.method.inst(*inst_ref) {
                        Inst::Phi(map) => {
                            let var = map[&block_ref];
                            if l.reg.contains_key(inst_ref) {
                                par_copies_reg.insert((l.reg[&var], l.reg[inst_ref]));
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
                if !par_copies_reg.is_empty() {
                    for step in serialize_copies(par_copies_reg, None) {
                        match step {
                            SerializedStep::Copy { from, to } => {
                                self.emit_code(format!("mov {}, {}", REGS[from], REGS[to]))
                            }
                            SerializedStep::Swap(a, b) => {
                                self.emit_code(format!("xchg {}, {}", REGS[a], REGS[b]))
                            }
                        }
                    }
                }
                if !par_copies_mem.is_empty() {
                    for step in serialize_copies(par_copies_mem, None) {
                        match step {
                            SerializedStep::Copy { from, to } => {
                                let from = stack_slot_to_offset[&StackSlotRef(from)];
                                let to = stack_slot_to_offset[&StackSlotRef(to)];
                                self.emit_code(format!("movq {}(%rbp), %rax", from));
                                self.emit_code(format!("movq %rax, {}(%rbp)", to));
                            }
                            SerializedStep::Swap(a, b) => {
                                // Push pop
                                let a = stack_slot_to_offset[&StackSlotRef(a)];
                                let b = stack_slot_to_offset[&StackSlotRef(b)];
                                self.emit_code(format!("pushq {}(%rbp)", a));
                                self.emit_code(format!("pushq {}(%rbp)", b));
                                self.emit_code(format!("popq {}(%rbp)", a));
                                self.emit_code(format!("popq {}(%rbp)", b));
                            }
                        }
                    }
                }
            });
            self.emit_code(format!(
                "# Terminating block {}",
                block_ref_to_label[block_ref.0]
            ));
            match &l.method.block(block_ref).term {
                Terminator::Return(ret) => {
                    if l.method.return_ty != Type::Void && ret.is_none() {
                        // method finished without returning anything, but it should have. exit with -2
                        self.emit_code("leaq no_return_value_msg(%rip), %rdi");
                        self.emit_code("call printf");
                        self.emit_code("movq $-2, %rdi");
                        self.emit_code("call exit");
                    } else {
                        if let Some(ret) = ret {
                            if let Some(annotation) = l.method.get_inst_annotation(ret) {
                                for span in annotation.spans() {
                                    self.emit_code(format!(
                                        ".loc 0 {} {}",
                                        span.start().line,
                                        span.start().column
                                    ));
                                }
                            }
                            self.emit_code(format!("movq {}, %rax", reg![ret]));
                        }
                        self.emit_code(format!(
                            ".loc 0 {} {}",
                            l.method.span.end().line,
                            l.method.span.end().column - 1 // exclusive
                        ));
                        if l.method.name.inner.as_ref() == "main" {
                            assert!(ret.is_none());
                            // return 0;
                            self.emit_code("movq $0, %rax");
                        }
                        // Restore all callee-saved registers
                        for reg in tainted_callee_saved_regs.iter().rev() {
                            self.emit_code(format!("popq {}", reg));
                        }
                        // Restore stack frame
                        self.emit_code("leave");
                        self.emit_code("ret");
                    }
                }
                Terminator::Jump(target) => {
                    self.emit_code(format!("jmp {}", block_ref_to_label[target.0]));
                }
                Terminator::CondJump {
                    cond,
                    true_,
                    false_,
                } => {
                    self.emit_code(format!("cmpq $0, {}", reg![cond]));
                    self.emit_code(format!("je {}", block_ref_to_label[false_.0]));
                    self.emit_code(format!("jmp {}", block_ref_to_label[true_.0]));
                }
            }
        }
    }

    /// Checks if %rax is in [0, length) and panics if not
    fn emit_bounds_check(
        &mut self,
        reg: &str,
        length: usize,
        inst_annotation: Option<&Annotation>,
    ) {
        let fail_branch = format!("bound_check_fail_{}", self.code.len());
        let pass_branch = format!("bound_check_pass_{}", self.code.len());
        self.emit_code(format!("cmpq $0, {}", reg));
        self.emit_code(format!("jl {}", fail_branch));
        self.emit_code(format!("cmpq ${}, {}", length, reg));
        self.emit_code(format!("jl {}", pass_branch));
        self.emit_label(&fail_branch);
        // print an error message.
        // first argument is the format string, second is the line number, third is arr.len, fourth is the index
        self.emit_code(format!("movq {}, %rcx", reg));
        self.emit_code("leaq index_out_of_bounds_msg(%rip), %rdi");
        self.emit_code(format!(
            "movq ${}, %rsi",
            inst_annotation
                .and_then(|a| a.spans().first().cloned())
                .map(|s| s.start().line)
                .unwrap_or(0) // TODO: better error handling
        ));
        self.emit_code(format!("movq ${}, %rdx", length));
        self.emit_code("call printf");
        // Call exit(-1)
        self.emit_code("movq $-1, %rdi");
        self.emit_code("call exit");
        self.emit_label(&pass_branch);
    }

    fn emit_local_initialize(&mut self, c: &Const, mut stack_offset: i64) {
        match c {
            Const::Int(_) | Const::Bool(_) => {
                self.load_int_or_bool_const(c, &format!("{}(%rbp)", stack_offset));
            }
            Const::Array(arr_vals) => {
                for val in arr_vals.iter() {
                    self.load_int_or_bool_const(val, &format!("{}(%rbp)", stack_offset));
                    stack_offset += val.size() as i64;
                }
            }
            Const::Repeat(val, n) => match &**val {
                Const::Int(0) | Const::Bool(false) => {
                    // Use memset to zero out the memory
                    for reg in ["%rdi", "%rsi", "%rdx"].iter() {
                        self.emit_code(format!("pushq {}", reg));
                    }
                    self.emit_code("subq $8, %rsp");
                    self.emit_code(format!("leaq {}(%rbp), %rdi", stack_offset));
                    self.emit_code("movq $0, %rsi");
                    self.emit_code(format!("movq ${}, %rdx", n * val.size()));
                    self.emit_code("call memset");
                    self.emit_code("addq $8, %rsp");
                    for reg in ["%rdi", "%rsi", "%rdx"].iter().rev() {
                        self.emit_code(format!("popq {}", reg));
                    }
                }
                _ => {
                    for _ in 0..*n {
                        self.load_int_or_bool_const(val, &format!("{}(%rbp)", stack_offset));
                        stack_offset += val.size() as i64;
                    }
                }
            },
        }
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
