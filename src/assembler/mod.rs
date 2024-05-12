#![allow(clippy::non_canonical_partial_ord_impl)]

use core::fmt;
use std::{
    cell::RefCell,
    collections::{BTreeSet, HashMap, HashSet},
    rc::Rc,
};

use derivative::Derivative;
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
        for_each_successor,
        loop_utils::LoopAnalysis,
        predecessors, reverse_postorder, split_critical_edges,
    },
    scan::location::Location,
    utils::cli::Optimization,
};

use self::{
    arr_nm::ArrayAccessOffsetNonMaterializer, imm_nm::ImmediateNonMaterializer,
    regalloc::RegAllocator, spill::Spiller, term_nm::TerminatorNonMaterializer,
};

pub mod arr_nm;
#[cfg(feature = "ilp")]
pub mod coalesce;
pub mod imm_nm;
pub mod par_copy;
pub mod peephole;
pub mod regalloc;
pub mod spill;
pub mod term_nm;

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
    /// Loop analysis information.
    pub loops: LoopAnalysis,

    /// Non-materialized arguments. An argument is not materialized if it does
    /// not reside in a register when the instruction using the argument is
    /// executed. An argument can be non-materialized for two reasons.
    /// - For a large call, there's no way to store all of its argument in
    ///   registers.
    /// - For constants can usually just be encoded as immediates and do not
    ///   require a separate register.
    pub nm_args: HashMap<InstRef, HashSet<InstRef>>,

    /// Non-materialized terminator conditions. Similar to `nm_args`, but for
    /// terminators. In x86-64, a conditional jump need not be implemented by
    /// first evaluating the condition as boolean, then jumping based on the
    /// result. Instead, the condition can be directly encoded in the jump
    /// instruction.
    pub nm_terms: HashMap<BlockRef, (Inst, HashSet<InstRef>)>,

    // Filled in by the spiller
    /// A mapping from spilled variables to their spill slots.
    pub spill_slots: HashMap<InstRef, StackSlotRef>,

    // Filled in by the register allocator
    pub live_at: HashMap<ProgPt, im::HashSet<InstRef>>,
    pub reg: HashMap<InstRef, usize>,

    /// For array loads and stores, an additional integer offset can be absorbed
    /// into the instruction. This helps with loops where a[x], a[x+1], a[x+2],
    /// etc. are used. The value x+1, x+2 may not need to be materialized into
    /// registers at all. Absorption also helps with array bound check fusion.
    pub array_offsets: HashMap<InstRef, i64>,
}

impl LoweredMethod {
    fn new(method: &Method) -> Self {
        let method = split_critical_edges(method);
        let dom = compute_dominance(&method);
        let dom_tree = dom.dominator_tree();
        let predecessors = predecessors(&method);
        let loops = LoopAnalysis::new(&method);
        LoweredMethod {
            method,
            dom,
            dom_tree,
            predecessors,
            loops,

            max_reg: 0,
            spill_slots: HashMap::new(),
            nm_args: HashMap::new(),
            nm_terms: HashMap::new(),
            live_at: HashMap::new(),
            reg: HashMap::new(),
            array_offsets: HashMap::new(),
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
const CALLEE_SAVE_REGS: [&str; 6] = ["%r12", "%r13", "%r14", "%r15", "%rbx", "%rbp"];
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
    offset: i64,
}

pub struct Assembler {
    program: Program,
    // corresponds to .data
    data: Vec<String>,
    // corresponds to .text
    code: Vec<String>,

    optimizations: HashSet<Optimization>,
}

impl Assembler {
    pub fn new(program: Program, optimizations: &[Optimization]) -> Self {
        let mut optimizations: HashSet<_> = optimizations.iter().cloned().collect();
        if optimizations.remove(&Optimization::All) {
            optimizations.extend([Optimization::OmitFramePointer]);
        }
        Self {
            program,
            data: Vec::new(),
            code: Vec::new(),
            optimizations,
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

    #[cfg(feature = "ilp")]
    fn coalesce(l: &mut LoweredMethod, regs: &[&'static str]) {
        coalesce::Coalescer::new_reg(l, regs).solve_and_apply(l);
    }

    #[cfg(not(feature = "ilp"))]
    fn coalesce(_l: &mut LoweredMethod, regs: &[&'static str]) {}

    pub fn assemble_lowered(&mut self, file_name: &str) -> String {
        // todo: remove the .clone()
        for global in self.program.globals.clone().values() {
            self.assemble_global(global);
        }

        for method in self.program.methods.clone().values() {
            let mut lowered = LoweredMethod::new(method);
            ImmediateNonMaterializer::new(&mut lowered).run();
            ArrayAccessOffsetNonMaterializer::new(&mut lowered).run();
            TerminatorNonMaterializer::new(&mut lowered).run();
            let all_regs = {
                let omit_frame_pointer =
                    self.optimizations.contains(&Optimization::OmitFramePointer);
                // Don't use %rbp as a register if omit_frame_pointer is disabled.
                REGS.iter()
                    .copied()
                    .filter(|r| *r != "%rbp" || omit_frame_pointer)
                    .collect::<Vec<_>>()
            };
            let max_reg = all_regs.len();
            // For debugging. Smaller max_reg pushes the spiller to limit where
            // more bugs are likely to be found.
            // let max_reg = 3;

            let all_regs = &all_regs[..max_reg];
            Spiller::new(&self.program, &mut lowered, max_reg).spill();
            RegAllocator::new(&self.program, &mut lowered).allocate();
            let ordered_regs = MethodAssembler::pre_order_regs(&lowered, all_regs);
            Self::coalesce(&mut lowered, &ordered_regs);
            MethodAssembler::new(self, &lowered, ordered_regs).assemble_method();
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

        // Peephole optimizations
        self.adjust_cmp_jmp_order();
        self.remove_unnecessary_jmps();
        self.remove_unnecessary_labels();
        self.remove_unreachable_code();
        self.remove_unnecessary_jmps();
        self.remove_self_movs();
        self.replace_mov_0_with_xor();

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

#[derive(Derivative)]
#[derivative(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[derivative(PartialOrd = "feature_allow_slow_enum")]
#[derivative(Ord = "feature_allow_slow_enum")]
enum AsmArg {
    Reg(&'static str),
    Imm(i64),
    Stack {
        slot_ref: StackSlotRef,
        #[derivative(Debug = "ignore")]
        #[derivative(PartialEq = "ignore")]
        #[derivative(PartialOrd = "ignore")]
        #[derivative(Ord = "ignore")]
        resolver: Rc<RefCell<StackSlotAddressResolver>>,
    },
}

impl fmt::Display for AsmArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AsmArg::Reg(reg) => write!(f, "{}", reg),
            AsmArg::Imm(imm) => write!(f, "${}", imm),
            AsmArg::Stack { slot_ref, resolver } => {
                write!(f, "{}", resolver.borrow().resolve(*slot_ref, 0))
            }
        }
    }
}

#[derive(Debug, Clone, Default)]
struct StackSlotAddressResolver {
    omit_frame_pointer: bool,
    /// Mapping from stack slots to their offsets from %rbp
    stack_slot_to_bp_offset: HashMap<StackSlotRef, i64>,
    /// %rbp - %rsp
    rbp_minus_rsp: i64,
}

impl StackSlotAddressResolver {
    fn resolve(&self, stack_slot_ref: StackSlotRef, offset: i64) -> String {
        let offset = self.stack_slot_to_bp_offset[&stack_slot_ref] + offset;
        if !self.omit_frame_pointer {
            format!("{}(%rbp)", offset)
        } else {
            format!("{}(%rsp)", self.rbp_minus_rsp + offset)
        }
    }
}

pub struct MethodAssembler<'a> {
    asm: &'a mut Assembler,
    l: &'a LoweredMethod,
    name: &'a str,

    regs: Vec<&'static str>,
    stack_slot_resolver: Rc<RefCell<StackSlotAddressResolver>>,
    tainted_callee_saved_regs: BTreeSet<&'static str>,
    pending_bounds_check: BTreeSet<PendingBoundsCheck>,
    arg_loading_insts: HashSet<InstRef>,
}

impl<'a> MethodAssembler<'a> {
    fn pre_order_regs(l: &'a LoweredMethod, all_regs: &[&'static str]) -> Vec<&'static str> {
        // if this method doesn't call any other functions, prefer caller-saved registers over callee-saved registers.
        let mut calls_other_functions = false;
        for (_, inst) in l.method.iter_insts() {
            if let Inst::Call { .. } = inst {
                calls_other_functions = true;
            }
        }
        let mut regs = all_regs.to_vec();
        if calls_other_functions {
            // Prefer callee-saved over caller-saved
            // reg in CALLEE_SAVE_REGS will have key 0 and will be sorted before
            // reg not in CALLEE_SAVE_REGS.
            regs.sort_by_key(|&r| (!CALLEE_SAVE_REGS.contains(&r)) as i32);
        } else {
            // Prefer caller-saved over callee-saved
            regs.sort_by_key(|&r| (!CALLER_SAVE_REGS.contains(&r)) as i32);
        }
        regs
    }

    fn new(asm: &'a mut Assembler, l: &'a LoweredMethod, regs: Vec<&'static str>) -> Self {
        // crate::utils::show_graphviz(&l.method.dump_graphviz());
        let stack_slot_resolver = StackSlotAddressResolver {
            omit_frame_pointer: asm.optimizations.contains(&Optimization::OmitFramePointer),
            ..Default::default()
        };
        Self {
            asm,
            name: &l.method.name.inner,
            stack_slot_resolver: Rc::new(RefCell::new(stack_slot_resolver)),
            pending_bounds_check: BTreeSet::new(),
            tainted_callee_saved_regs: BTreeSet::new(),
            arg_loading_insts: HashSet::new(),
            regs,
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

    fn emit_push(&mut self, arg: &AsmArg) {
        // "The PUSH ESP instruction pushes the value of the ESP register as it
        // existed before the instruction was executed. If a PUSH instruction
        // uses a memory operand in which the ESP register is used for computing
        // the operand address, the address of the operand is computed before
        // the ESP register is decremented."
        match arg {
            AsmArg::Reg(_) | AsmArg::Stack { .. } => {
                self.emit_code(format!("pushq {}", arg));
            }
            // If immediate fits in 32 bits, use $imm
            AsmArg::Imm(imm) => {
                if *imm <= i32::MAX as i64 && *imm >= i32::MIN as i64 {
                    self.emit_code(format!("pushq {}", arg));
                } else {
                    // Use rax as a temporary register
                    self.emit_code(format!("movabsq ${}, %rax", imm));
                    self.emit_code("pushq %rax");
                }
            }
        }
        self.stack_slot_resolver.borrow_mut().rbp_minus_rsp += 8;
    }

    fn emit_pop(&mut self, arg: &AsmArg) {
        // If the ESP register is used as a base register for addressing a
        // destination operand in memory, the POP instruction computes the
        // effective address of the operand after it increments the ESP
        // register.
        self.stack_slot_resolver.borrow_mut().rbp_minus_rsp -= 8;
        self.emit_code(format!("popq {}", arg));
    }

    fn emit_sp_adjust(&mut self, offset: i64) {
        match offset.cmp(&0) {
            std::cmp::Ordering::Greater => self.emit_code(format!("addq ${}, %rsp", offset)),
            std::cmp::Ordering::Less => self.emit_code(format!("subq ${}, %rsp", -offset)),
            std::cmp::Ordering::Equal => {}
        }
        self.stack_slot_resolver.borrow_mut().rbp_minus_rsp -= offset;
    }

    fn emit_prologue(&mut self) {
        // Compute stack spaces
        let mut stack_space = 0i64;
        let n_args = self.l.method.params.len();
        let n_reg_args = n_args.min(6);

        // In our IR, the first n_args slots are reserved for arguments.
        // If we stick to this convention, this means we'll have to move all
        // arguments from the registers to the stack at in the prologue. This is
        // slow. On the other hand, the SSA-converted IR should have already
        // placed all argument-loading instructions at the beginning of the
        // method. If we detect that this is the case, we can skip the slow part
        // and attempt direct register-to-register moves.
        let fast_args = match identify_fast_arg_insts(self.l) {
            Some(arg_loading_insts) => {
                self.arg_loading_insts = arg_loading_insts;
                true
            }
            None => false,
        };

        let mut resolver = self.stack_slot_resolver.borrow_mut();
        for (i, (stack_slot_ref, stack_slot)) in self.l.method.iter_slack_slots().enumerate() {
            if i < n_args && i >= 6 {
                // Arguments 6 and above are on the stack already. They will be taken care of later.
                continue;
            }
            if fast_args && i < n_reg_args {
                // In the fast path, we can directly move the arguments from the
                // argument registers to the stack slots. No need to allocate
                // stack space for them.
                continue;
            }
            stack_space += stack_slot.ty.size() as i64;
            resolver
                .stack_slot_to_bp_offset
                .insert(stack_slot_ref, -stack_space);
        }
        let omit_frame_pointer = resolver.omit_frame_pointer;
        std::mem::drop(resolver);
        self.tainted_callee_saved_regs = self
            .l
            .reg
            .values()
            .map(|&r| self.regs[r])
            .filter(|&r| CALLEE_SAVE_REGS.contains(&r))
            .collect::<BTreeSet<_>>();
        self.emit_code(format!(
            ".loc 0 {} {}",
            self.l.method.span.start().line,
            self.l.method.span.start().column
        ));
        if !omit_frame_pointer {
            self.emit_code("pushq %rbp");
            self.emit_code("movq %rsp, %rbp".to_string());
        }
        stack_space = if (self.tainted_callee_saved_regs.len() % 2 == 1) ^ omit_frame_pointer {
            // Round up to nearest 16k + 8
            ((stack_space + 8 + 15) & !15) - 8
        } else {
            // Round up to nearest 16k
            (stack_space + 15) & !15
        };
        self.emit_sp_adjust(-stack_space);

        // Save all callee-saved registers
        for reg in self.tainted_callee_saved_regs.clone() {
            self.emit_push(&AsmArg::Reg(reg));
        }

        if fast_args {
            let mut par_copies = HashSet::new();
            let mut ser_copies = Vec::new();
            // All argument loading instructions must have results in distinct
            // registers (for those with registers assigned). This is because
            // all live arguments must be live at the end of the argument
            // loading sequence.
            for inst_ref in &self.arg_loading_insts {
                if let Some(dst_reg_id) = self.l.reg.get(inst_ref) {
                    // If the result of an argument-loading instruction is
                    // assigned a register.
                    let dst_reg = self.regs[*dst_reg_id];
                    let src_reg = match self.l.method.inst(*inst_ref) {
                        Inst::Load(Address::Local(stack_slot)) => ARG_REGS[stack_slot.0],
                        _ => unreachable!(),
                    };
                    if let Some(src_reg_id) = self.regs.iter().position(|&r| r == src_reg) {
                        par_copies.insert((src_reg_id, *dst_reg_id));
                    } else {
                        ser_copies.push((src_reg, dst_reg));
                    }
                }
            }
            self.emit_par_reg_copies(par_copies);
            for (src, dst) in ser_copies {
                self.emit_code(format!("movq {}, {}", src, dst));
            }
        } else {
            let method = &self.l.method;
            for (arg_idx, arg_slot_iter) in method.iter_slack_slots().enumerate().take(n_reg_args) {
                self.emit_code(format!(
                    "movq {}, {}",
                    ARG_REGS[arg_idx],
                    self.stack_slot_resolver
                        .borrow()
                        .resolve(arg_slot_iter.0, 0)
                ));
            }
        }

        let mut stack_offset = if omit_frame_pointer { 8 } else { 16 };
        let mut resolver = self.stack_slot_resolver.borrow_mut();
        for (arg_slot_ref, arg_slot) in self.l.method.iter_slack_slots().take(n_args).skip(6) {
            resolver
                .stack_slot_to_bp_offset
                .insert(arg_slot_ref, stack_offset);
            stack_offset += arg_slot.ty.size() as i64;
        }
    }

    fn emit_epilogue(&mut self) {
        // Restore all callee-saved registers
        let rbp_minus_rsp = self.stack_slot_resolver.borrow().rbp_minus_rsp;
        for reg in self.tainted_callee_saved_regs.clone().into_iter().rev() {
            self.emit_pop(&AsmArg::Reg(reg));
        }
        // Restore stack frame
        let omit_frame_pointer = self.stack_slot_resolver.borrow().omit_frame_pointer;
        if !omit_frame_pointer {
            self.emit_code("leave");
        } else {
            let rbp_minus_rsp = self.stack_slot_resolver.borrow().rbp_minus_rsp;
            self.emit_sp_adjust(rbp_minus_rsp);
        }
        self.emit_code("ret");
        // Reset rbp_minus_rsp to the value before the prologue so code gen for
        // other blocks can move on.
        self.stack_slot_resolver.borrow_mut().rbp_minus_rsp = rbp_minus_rsp;
    }

    fn emit_block_label(&mut self, block_ref: BlockRef) {
        if let Some(block_annotation) = self.l.method.get_block_annotation(&block_ref) {
            self.emit_annotated_label(&self.block_label(block_ref), &block_annotation.to_string());
        } else {
            self.emit_label(&self.block_label(block_ref));
        }
    }

    fn reg(&self, inst_ref: impl std::borrow::Borrow<InstRef>) -> &'static str {
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
                                let Location { line, column, .. } = span.start();
                                self.emit_code(format!(".loc 0 {} {}", line, column));
                            }
                        }
                        self.emit_code(format!("movq {}, %rax", self.reg(*ret)));
                    }
                    let Location { line, column, .. } = self.l.method.span.end();
                    self.emit_code(format!(".loc 0 {} {}", line, column - 1));
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
            } => match self.l.nm_terms.get(&block_ref) {
                None => {
                    self.emit_code(format!("cmpq $0, {}", self.reg(*cond)));
                    self.emit_code(format!("je {}", self.block_label(*false_)));
                    self.emit_code(format!("jmp {}", self.block_label(*true_)));
                }
                Some((cond, nm)) => {
                    let (lhs, rhs, jmp) = match cond {
                        Inst::Eq(lhs, rhs) => (lhs, rhs, "je"),
                        Inst::Neq(lhs, rhs) => (lhs, rhs, "jne"),
                        Inst::Less(lhs, rhs) => (lhs, rhs, "jl"),
                        Inst::LessEq(lhs, rhs) => (lhs, rhs, "jle"),
                        Inst::Not(var) => {
                            self.emit_code(format!("cmpq $0, {}", self.reg(*var)));
                            self.emit_code(format!("je {}", self.block_label(*true_)));
                            self.emit_code(format!("jmp {}", self.block_label(*false_)));
                            return;
                        }
                        _ => unreachable!(),
                    };
                    let lhs = self.arg_helper(*lhs, !nm.contains(lhs));
                    let rhs = self.arg_helper(*rhs, !nm.contains(rhs));
                    match (lhs, rhs) {
                        (AsmArg::Imm(lhs), AsmArg::Imm(rhs)) => {
                            // Should have been handled by constant propagation
                            let v = match cond {
                                Inst::Eq(_, _) => lhs == rhs,
                                Inst::Neq(_, _) => lhs != rhs,
                                Inst::Less(_, _) => lhs < rhs,
                                Inst::LessEq(_, _) => lhs <= rhs,
                                _ => unreachable!(),
                            };
                            let target = if v { *true_ } else { *false_ };
                            self.emit_code(format!("jmp {}", self.block_label(target)));
                        }
                        (
                            mut lhs @ (AsmArg::Imm(_) | AsmArg::Reg(_)),
                            mut rhs @ (AsmArg::Imm(_) | AsmArg::Reg(_)),
                        ) => {
                            let mut jmp = jmp.to_string();
                            if let AsmArg::Imm(_) = lhs {
                                std::mem::swap(&mut lhs, &mut rhs);
                                jmp = jmp.replace('l', "g");
                            }
                            self.emit_code(format!("cmpq {}, {}", rhs, lhs));
                            self.emit_code(format!("{} {}", jmp, self.block_label(*true_)));
                            self.emit_code(format!("jmp {}", self.block_label(*false_)));
                        }
                        _ => unreachable!(),
                    }
                }
            },
        }
    }

    pub fn assemble_method(mut self) {
        let method_name = &self.l.method.name.inner;
        self.emit_label(method_name);
        self.emit_prologue();
        let rev_postorder = reverse_postorder(&self.l.method);

        for block_ref in rev_postorder.iter().cloned() {
            self.emit_block_label(block_ref);
            let rbp_minus_rsp_before = self.stack_slot_resolver.borrow().rbp_minus_rsp;
            let insts = &self.l.method.block(block_ref).insts;
            // Keeps the verified bounds of each array access index so far.
            let mut bounds: HashMap<InstRef, (i64, i64)> = HashMap::new();
            for (i, inst_ref) in insts.iter().enumerate() {
                if self.arg_loading_insts.contains(inst_ref) {
                    // Skip argument loading instructions. They have been
                    // handled by the prologue.
                    continue;
                }
                self.emit_inst_annotation(*inst_ref);
                let inst = self.l.method.inst(*inst_ref);
                if !inst.has_side_effects() && !self.l.reg.contains_key(inst_ref) {
                    // If an instruction is not side-effective, and its result
                    // does not have a register assigned, it's dead.
                    continue;
                }
                match inst {
                    Inst::Phi(_) | Inst::PhiMem { .. } => continue, // They are taken care of elsewhere!
                    Inst::Copy(src) => match self.arg(*inst_ref, *src) {
                        AsmArg::Imm(x) if x < i32::MIN as i64 || x > i32::MAX as i64 => {
                            self.emit_code(format!("movabsq ${}, {}", x, self.reg(inst_ref)));
                        }
                        arg => {
                            self.emit_code(format!("movq {}, {}", arg, self.reg(inst_ref)));
                        }
                    },
                    Inst::Add(_, _) | Inst::Sub(_, _) | Inst::Mul(_, _) => {
                        self.emit_add_sub_mul(*inst_ref);
                    }
                    Inst::Div(_, _) => self.emit_div(*inst_ref),
                    Inst::Mod(lhs, rhs) => {
                        self.emit_code(format!("movq {}, %rax", self.reg(lhs)));
                        self.emit_code("cqto"); // Sign-extend %rax into %rdx
                        self.emit_code(format!("idivq {}", self.reg(rhs)));
                        self.emit_code(format!("movq %rdx, {}", self.reg(inst_ref)));
                    }
                    Inst::Neg(var) => {
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
                        self.emit_code(format!("cmpq $0, {}", self.reg(var)));
                        self.emit_code("sete %al");
                        self.emit_code(format!("movzbq %al, {}", self.reg(inst_ref)));
                    }
                    Inst::Eq(lhs, rhs)
                    | Inst::Neq(lhs, rhs)
                    | Inst::Less(lhs, rhs)
                    | Inst::LessEq(lhs, rhs) => {
                        match (self.arg(*inst_ref, *lhs), self.arg(*inst_ref, *rhs)) {
                            (AsmArg::Imm(lhs), AsmArg::Imm(rhs)) => {
                                // Again constant propagation should have taken care of this
                                let cond = match inst {
                                    Inst::Eq(_, _) => lhs == rhs,
                                    Inst::Neq(_, _) => lhs != rhs,
                                    Inst::Less(_, _) => lhs < rhs,
                                    Inst::LessEq(_, _) => lhs <= rhs,
                                    _ => unreachable!(),
                                } as i64;
                                self.emit_code(format!("movq ${}, {}", cond, self.reg(inst_ref)));
                            }
                            (
                                mut lhs @ (AsmArg::Imm(_) | AsmArg::Reg(_)),
                                mut rhs @ (AsmArg::Imm(_) | AsmArg::Reg(_)),
                            ) => {
                                let mut inst_name = match inst {
                                    Inst::Eq(_, _) => "sete",
                                    Inst::Neq(_, _) => "setne",
                                    Inst::Less(_, _) => "setl",
                                    Inst::LessEq(_, _) => "setle",
                                    _ => unreachable!(),
                                }
                                .to_string();
                                if let AsmArg::Imm(_) = lhs {
                                    std::mem::swap(&mut lhs, &mut rhs);
                                    inst_name = inst_name.replace('l', "g");
                                }
                                self.emit_code(format!("cmpq {}, {}", rhs, lhs));
                                self.emit_code(format!("{} %al", inst_name));
                                self.emit_code(format!("movzbq %al, {}", self.reg(inst_ref)));
                            }
                            _ => unreachable!(),
                        }
                    }
                    Inst::LoadConst(c) => {
                        self.asm.load_int_or_bool_const(c, self.reg(inst_ref));
                    }
                    Inst::Load(addr) => match addr {
                        Address::Global(name) => {
                            self.emit_code(format!("movq {}(%rip), {}", name, self.reg(inst_ref)));
                        }
                        Address::Local(stack_slot) => {
                            self.emit_code(format!(
                                "movq {}, {}",
                                self.stack_slot_resolver.borrow().resolve(*stack_slot, 0),
                                self.reg(inst_ref)
                            ));
                        }
                    },
                    Inst::Store { addr, value } => match addr {
                        Address::Global(name) => {
                            self.emit_code(format!("movq {}, {}(%rip)", self.reg(value), name));
                        }
                        Address::Local(stack_slot) => {
                            self.emit_code(format!(
                                "movq {}, {}",
                                self.reg(value),
                                self.stack_slot_resolver.borrow().resolve(*stack_slot, 0)
                            ));
                        }
                    },
                    Inst::LoadArray { addr, index } => {
                        // Do bound check first
                        let (length, elem_size) =
                            match self.asm.program.infer_address_type(&self.l.method, addr) {
                                Type::Array { length, base } => (*length, base.size() as i64),
                                _ => unreachable!(),
                            };
                        self.emit_bounds_check(
                            *inst_ref,
                            *index,
                            length,
                            block_ref,
                            i,
                            &mut bounds,
                        );
                        let offset = self.l.array_offsets.get(inst_ref).copied().unwrap_or(0);
                        let index = self.arg(*inst_ref, *index);
                        let addr = self.emit_address(addr, &index, elem_size, offset);
                        self.emit_code(format!("movq {}, {}", addr, self.reg(inst_ref)));
                    }
                    Inst::StoreArray { addr, index, value } => {
                        let (length, elem_size) =
                            match self.asm.program.infer_address_type(&self.l.method, addr) {
                                Type::Array { length, base } => (*length, base.size() as i64),
                                _ => unreachable!(),
                            };
                        self.emit_bounds_check(
                            *inst_ref,
                            *index,
                            length,
                            block_ref,
                            i,
                            &mut bounds,
                        );
                        let value = self.arg(*inst_ref, *value);
                        let offset = self.l.array_offsets.get(inst_ref).copied().unwrap_or(0);
                        let index = self.arg(*inst_ref, *index);
                        let addr = self.emit_address(addr, &index, elem_size, offset);
                        match value {
                            AsmArg::Imm(x) if x < i32::MIN as i64 || x > i32::MAX as i64 => {
                                self.emit_code(format!("movabsq ${}, %rax", x));
                                self.emit_code(format!("movq %rax, {}", addr));
                            }
                            value => {
                                self.emit_code(format!("movq {}, {}", value, addr));
                            }
                        }
                    }
                    Inst::Initialize { stack_slot, value } => {
                        self.emit_local_initialize(value, *stack_slot)
                    }
                    Inst::LoadStringLiteral(s) => {
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
            let rbp_minus_rsp_after = self.stack_slot_resolver.borrow().rbp_minus_rsp;
            assert_eq!(rbp_minus_rsp_before, rbp_minus_rsp_after);
        }
        self.flush_bounds_check();
    }

    fn emit_address(
        &mut self,
        addr: &Address,
        index: &AsmArg,
        elem_size: i64,
        offset: i64,
    ) -> String {
        match (addr, index) {
            (Address::Global(name), AsmArg::Reg(reg)) => {
                if offset == 0 {
                    format!("{}(, {}, {})", name, reg, elem_size)
                } else {
                    let sym_name = format!("{}.{}", name, offset).replace('-', "_");
                    let offset = offset * elem_size;
                    self.emit_code(format!(".set {}, {} + {}", sym_name, name, offset));
                    format!("{}(, {}, {})", sym_name, reg, elem_size)
                }
            }
            (Address::Global(name), AsmArg::Imm(i)) => {
                let sym_name = format!("{}.{}", name, i + offset).replace('-', "_");
                let offset = (i + offset) * elem_size;
                self.emit_code(format!(".set {}, {} + {}", sym_name, name, offset));
                format!("{}(,1)", sym_name)
            }
            (Address::Local(stack_slot), AsmArg::Reg(reg)) => {
                let mut resolved = self
                    .stack_slot_resolver
                    .borrow()
                    .resolve(*stack_slot, offset * elem_size);
                resolved.pop(); // Remove the ')'
                resolved.push_str(&format!(", {}, {})", reg, elem_size));
                resolved
            }
            (Address::Local(stack_slot), AsmArg::Imm(i)) => self
                .stack_slot_resolver
                .borrow()
                .resolve(*stack_slot, (i + offset) * elem_size),
            _ => unreachable!(),
        }
    }

    fn emit_add_sub_mul(&mut self, inst_ref: InstRef) {
        let inst = self.l.method.inst(inst_ref);
        let (lhs, rhs, asm_inst) = match inst {
            Inst::Add(lhs, rhs) => (lhs, rhs, "addq"),
            Inst::Sub(lhs, rhs) => (lhs, rhs, "subq"),
            Inst::Mul(lhs, rhs) => (lhs, rhs, "imulq"),
            _ => unreachable!(),
        };
        let dst_reg = self.reg(inst_ref);
        match (self.arg(inst_ref, *lhs), self.arg(inst_ref, *rhs)) {
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
                if r != dst_reg {
                    if i32::MIN as i64 <= l && l <= i32::MAX as i64 && asm_inst == "addq" {
                        self.emit_code(format!("leaq {}({}), {}", l, r, dst_reg));
                        return;
                    }
                    if i32::MIN as i64 <= l && l <= i32::MAX as i64 && asm_inst == "imulq" {
                        // Use the three-operand form of imulq
                        self.emit_code(format!("imulq ${}, {}, {}", l, r, dst_reg));
                        return;
                    }
                    self.emit_code(format!("movq {}, {}", r, dst_reg));
                }
                self.emit_code(format!("{} ${}, {}", asm_inst, l, dst_reg));
                if let Inst::Sub(_, _) = inst {
                    self.emit_code(format!("negq {}", dst_reg));
                }
            }
            (AsmArg::Reg(l), AsmArg::Imm(r)) => {
                if l != dst_reg {
                    if i32::MIN as i64 <= r && r <= i32::MAX as i64 && asm_inst == "addq" {
                        self.emit_code(format!("leaq {}({}), {}", r, l, dst_reg));
                        return;
                    }
                    if i32::MIN as i64 <= -r && -r <= i32::MAX as i64 && asm_inst == "subq" {
                        self.emit_code(format!("leaq {}({}), {}", -r, l, dst_reg));
                        return;
                    }
                    if i32::MIN as i64 <= r && r <= i32::MAX as i64 && asm_inst == "imulq" {
                        // Use the three-operand form of imulq
                        self.emit_code(format!("imulq ${}, {}, {}", r, l, dst_reg));
                        return;
                    }
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
                    if asm_inst == "addq" {
                        self.emit_code(format!("leaq ({}, {}), {}", l, r, dst_reg));
                        return;
                    }
                    self.emit_code(format!("movq {}, {}", l, dst_reg));
                    self.emit_code(format!("{} {}, {}", asm_inst, r, dst_reg));
                }
            }
            _ => unimplemented!(),
        }
    }

    fn emit_div(&mut self, inst_ref: InstRef) {
        let Inst::Div(lhs, rhs) = self.l.method.inst(inst_ref) else {
            unreachable!();
        };
        let dst_reg = self.reg(inst_ref);
        match (self.arg(inst_ref, *lhs), self.arg(inst_ref, *rhs)) {
            (AsmArg::Imm(a), AsmArg::Imm(b)) => {
                self.emit_code(format!("movq {}, {}", a / b, dst_reg));
            }
            (lhs @ (AsmArg::Imm(_) | AsmArg::Reg(_)), rhs @ AsmArg::Reg(_)) => {
                self.emit_code(format!("movq {}, %rax", lhs));
                self.emit_code("cqto"); // Sign-extend %rax into %rdx
                self.emit_code(format!("idivq {}", rhs));
                self.emit_code(format!("movq %rax, {}", dst_reg));
            }
            (lhs @ AsmArg::Reg(_), AsmArg::Imm(d)) => {
                let lhs_reg = format!("{}", lhs);
                match d {
                    0 => {} // UB
                    1 | -1 => {
                        if lhs_reg != dst_reg {
                            self.emit_code(format!("movq {}, {}", lhs_reg, dst_reg));
                        }
                        if d == -1 {
                            self.emit_code(format!("negq {}", dst_reg));
                        }
                    }
                    d if d & (d - 1) == 0 => {
                        // d is a power of 2
                        let shift = d.trailing_zeros();
                        if lhs_reg != dst_reg {
                            self.emit_code(format!("movq {}, {}", lhs_reg, dst_reg));
                        }
                        self.emit_code(format!("sarq ${}, {}", shift, dst_reg));
                    }
                    d => {
                        // See "Division by Invariant Integers using
                        // Multiplication", by Granlund and Montgomery, sec. 5.
                        use num_bigint::BigInt;

                        let d_abs = d.abs();
                        let log2_d_ceil = 64 - (d_abs - 1).leading_zeros();
                        let l = log2_d_ceil.max(1);
                        let m = 1 + (BigInt::from(1) << (63 + l)) / d_abs;
                        let m_ = i64::try_from(m - (BigInt::from(1) << 64)).unwrap();

                        self.emit_code(format!("movabsq ${}, %rax", m_));
                        self.emit_code(format!("imulq {}", lhs_reg));
                        self.emit_code(format!("addq {}, %rdx", lhs_reg));
                        if l - 1 > 0 {
                            self.emit_code(format!("sarq ${}, %rdx", l - 1));
                        }
                        if lhs_reg != dst_reg {
                            self.emit_code(format!("movq {}, {}", lhs_reg, dst_reg));
                        }
                        self.emit_code(format!("shrq $63, {}", dst_reg));
                        self.emit_code(format!("addq %rdx, {}", dst_reg));
                        if d < 0 {
                            self.emit_code(format!("negq {}", dst_reg));
                        }
                    }
                }
            }
            _ => unreachable!(),
        }
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
                        let resolver = self.stack_slot_resolver.borrow();
                        let from = resolver.resolve(StackSlotRef(from), 0);
                        let to = resolver.resolve(StackSlotRef(to), 0);
                        std::mem::drop(resolver);
                        self.emit_code(format!("movq {}, %rax", from));
                        self.emit_code(format!("movq %rax, {}", to));
                    }
                    SerializedStep::Swap(a, b) => {
                        // Push pop
                        let a = AsmArg::Stack {
                            slot_ref: StackSlotRef(a),
                            resolver: self.stack_slot_resolver.clone(),
                        };
                        let b = AsmArg::Stack {
                            slot_ref: StackSlotRef(b),
                            resolver: self.stack_slot_resolver.clone(),
                        };
                        self.emit_push(&a);
                        self.emit_push(&b);
                        self.emit_pop(&a);
                        self.emit_pop(&b);
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
            .filter(|v| **v != inst_ref)
            .filter_map(|v| self.l.reg.get(v))
            .filter(|v| CALLER_SAVE_REGS.contains(&self.regs[**v]))
            .collect::<BTreeSet<_>>();
        for reg in saving_regs.iter() {
            self.emit_push(&AsmArg::Reg(self.regs[**reg]));
        }

        let mut stack_space_for_args = 0;
        let n_remaining_args = args.len().saturating_sub(6);
        if (n_remaining_args + saving_regs.len()) % 2 == 1 {
            // Align stack to 16 bytes
            self.emit_sp_adjust(-8);
            stack_space_for_args += 8;
        }
        for arg_ref in args.iter().skip(6).rev() {
            self.emit_push(&self.arg(inst_ref, *arg_ref));
            stack_space_for_args += 8;
        }

        let mut par_copies = HashSet::new();
        let mut pre_ser_copies = vec![];
        let mut post_ser_copies = vec![];
        for (arg_idx, arg_ref) in args.iter().enumerate().take(6) {
            let arg = self.arg(inst_ref, *arg_ref);
            let dst_reg = ARG_REGS[arg_idx];
            match arg {
                AsmArg::Reg(arg_reg) if ARG_REGS.contains(&arg_reg) => {
                    if let Some(dst_reg_idx) = self.regs.iter().position(|r| *r == dst_reg) {
                        let arg_reg_idx = self.regs.iter().position(|r| *r == arg_reg).unwrap();
                        par_copies.insert((arg_reg_idx, dst_reg_idx));
                    } else {
                        // arg_reg is used for argument passing, but the
                        // destination register is not used by our register
                        // allocator. In this case the copy should be arranged
                        // before the parallel copy sequence so the value of
                        // arg_reg is not overwritten. Overwriting dst_reg is
                        // fine, because it's not used by our allocator.
                        pre_ser_copies.push((arg, dst_reg));
                    }
                }
                // An immediate, a memory operand, or a non-argument register.
                // They will not be overwritten by the parallel copy sequence
                // anyways. So we arrange them to be copied after the parallel
                // copy sequence.
                _ => post_ser_copies.push((arg, dst_reg)),
            }
        }
        for (arg, dst_reg) in pre_ser_copies {
            self.emit_code(format!("movq {}, {}", arg, dst_reg,));
        }
        if !par_copies.is_empty() {
            self.emit_code(format!("# Parallel argument copy: {:?}", par_copies));
            self.emit_par_reg_copies(par_copies);
        }
        for (arg, dst_reg) in post_ser_copies {
            self.emit_code(format!("movq {}, {}", arg, dst_reg,));
        }
        self.emit_code(format!("call {}", callee_name));
        if stack_space_for_args > 0 {
            self.emit_sp_adjust(stack_space_for_args);
        }
        let returns_value = match self.asm.program.methods.get(&callee_name.to_string()) {
            Some(method) => method.return_ty != Type::Void,
            None => true,
        };
        for reg in saving_regs.iter().rev() {
            self.emit_pop(&AsmArg::Reg(self.regs[**reg]));
        }
        if returns_value && self.l.reg.contains_key(&inst_ref) {
            self.emit_code(format!("movq %rax, {}", self.reg(inst_ref)));
        }
    }

    fn arg_helper(&self, arg_ref: InstRef, materialized: bool) -> AsmArg {
        if materialized {
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
                    AsmArg::Stack {
                        slot_ref: *spill_slot,
                        resolver: self.stack_slot_resolver.clone(),
                    }
                }
            }
        }
    }

    fn arg(&self, inst_ref: InstRef, arg_ref: InstRef) -> AsmArg {
        self.arg_helper(arg_ref, self.l.nm_args.is_materialized(inst_ref, arg_ref))
    }

    fn get_bound_check_fail_label(&self, check: &PendingBoundsCheck) -> String {
        format!(
            "{}.bound_check_fail.{}.{}.{}.{}",
            &self.name,
            &check.index.to_string()[1..].replace('-', "_"), // Remove the % or $ sign
            check.offset.to_string().replace('-', "_"),
            check.length,
            check.line
        )
    }

    /// Checks if %rax is in [0, length) and panics if not
    fn emit_bounds_check(
        &mut self,
        inst_ref: InstRef,
        index_ref: InstRef,
        length: usize,
        block_ref: BlockRef,
        inst_idx: usize,
        bounds: &mut HashMap<InstRef, (i64, i64)>,
    ) {
        let line = self
            .l
            .method
            .get_inst_annotation(&index_ref)
            .and_then(|a| a.spans().first().cloned())
            .map(|s| s.start().line)
            .unwrap_or(0); // TODO: better error handling
        let index_arg = self.arg(inst_ref, index_ref);
        let offset = self.l.array_offsets.get(&inst_ref).copied().unwrap_or(0);
        let check = PendingBoundsCheck {
            index: index_arg.clone(),
            length,
            line,
            offset,
        };
        let fail_branch = self.get_bound_check_fail_label(&check);
        match index_arg {
            AsmArg::Reg(reg) => {
                let (min, max) = bounds
                    .get(&index_ref)
                    .cloned()
                    .unwrap_or((i64::MIN, i64::MAX));
                let mut req_bound = (-offset, length as i64 - 1 - offset);
                // Bound check fusion
                for inst_ref in &self.l.method.block(block_ref).insts[inst_idx + 1..] {
                    match self.l.method.inst(*inst_ref) {
                        Inst::LoadArray { addr, index } | Inst::StoreArray { addr, index, .. }
                            if *index == index_ref =>
                        {
                            let offset = self.l.array_offsets.get(inst_ref).copied().unwrap_or(0);
                            let length =
                                match self.asm.program.infer_address_type(&self.l.method, addr) {
                                    Type::Array { length, .. } => *length,
                                    _ => unreachable!(),
                                };
                            // Tighten the bounds
                            req_bound = (
                                req_bound.0.max(0 - offset),
                                req_bound.1.min(length as i64 - 1 - offset),
                            );
                            // println!("  scanning through {} {:?}", inst_ref, req_bound);
                        }
                        // Don't fuse bounds check beyond calls. Calls may be
                        // side effective and fusion across calls could cause a
                        // branch check failure that would have happened after
                        // the call to happen before. If the call is side
                        // effective then we've changed the observable behavior
                        // of the program.
                        Inst::Call { .. } => break,
                        _ => continue,
                    }
                }
                // if self.name == "main" {
                //     println!(
                //         "{}.{}: [{}] {:?} {:?}",
                //         block_ref,
                //         inst_ref,
                //         index_ref,
                //         req_bound,
                //         (min, max)
                //     );
                // }

                let (req_min, req_max) = req_bound;
                let min_in_bounds = min >= req_min;
                let max_in_bounds = max <= req_max;
                if min_in_bounds && max_in_bounds {
                    return; // The index is already known to be in bounds, no need to check again.
                }
                if max_in_bounds {
                    // Only need to check below, i.e., if reg >= req_min
                    self.emit_code(format!("cmpq ${}, {}", req_min, reg));
                    self.emit_code(format!("jl {}", fail_branch));
                } else if min_in_bounds {
                    // Only need to check above, i.e., if reg <= req_max
                    self.emit_code(format!("cmpq ${}, {}", req_max, reg));
                    self.emit_code(format!("jg {}", fail_branch));
                } else {
                    // Double check both bounds, i.e., if reg in [req_min, req_max]
                    if req_min == 0 {
                        self.emit_code(format!("cmpq ${}, {}", req_max, reg));
                    } else {
                        self.emit_code(format!("leaq {}({}), %rax", -req_min, reg));
                        self.emit_code(format!("cmpq ${}, %rax", req_max - req_min));
                    }
                    self.emit_code(format!("ja {}", fail_branch)); // Unsigned comparison
                }
                self.pending_bounds_check.insert(check);
                bounds.insert(index_ref, (min.max(req_min), max.min(req_max)));
            }
            AsmArg::Imm(i) => {
                let i = i + offset;
                if i < 0 || i >= length as i64 {
                    self.emit_code(format!("jmp {}", fail_branch));
                    self.pending_bounds_check.insert(check);
                }
            }
            _ => unreachable!(),
        }
    }

    fn flush_bounds_check(&mut self) {
        for check in std::mem::take(&mut self.pending_bounds_check) {
            // first argument is the format string, second is the line number, third is arr.len, fourth is the index
            let fail_branch = self.get_bound_check_fail_label(&check);
            self.emit_label(&fail_branch);
            self.emit_code(format!("movq {}, %rcx", check.index));
            if check.offset != 0 {
                self.emit_code(format!("addq ${}, %rcx", check.offset));
            }
            self.emit_code(format!("movq ${}, %rsi", check.line));
            self.emit_code(format!("movq ${}, %rdx", check.length));
            self.emit_code("jmp bounds_check.fail");
        }
    }

    fn emit_local_initialize(&mut self, c: &Const, stack_slot_ref: StackSlotRef) {
        match c {
            Const::Int(_) | Const::Bool(_) => {
                self.asm.load_int_or_bool_const(
                    c,
                    &self.stack_slot_resolver.borrow().resolve(stack_slot_ref, 0),
                );
            }
            Const::Array(arr_vals) => {
                let mut offset = 0;
                for val in arr_vals.iter() {
                    self.asm.load_int_or_bool_const(
                        val,
                        &self
                            .stack_slot_resolver
                            .borrow()
                            .resolve(stack_slot_ref, offset),
                    );
                    offset += val.size() as i64;
                }
            }
            Const::Repeat(val, n) => match &**val {
                Const::Int(0) | Const::Bool(false) => {
                    // TODO: use rep stosq
                    // Use memset to zero out the memory
                    for reg in CALLER_SAVE_REGS.iter() {
                        self.emit_push(&AsmArg::Reg(reg));
                    }
                    if CALLER_SAVE_REGS.len() % 2 == 1 {
                        self.emit_sp_adjust(-8);
                    }
                    self.emit_code(format!(
                        "leaq {}, %rdi",
                        self.stack_slot_resolver.borrow().resolve(stack_slot_ref, 0)
                    ));
                    self.emit_code("movq $0, %rsi");
                    self.emit_code(format!("movq ${}, %rdx", n * val.size()));
                    self.emit_code("call memset");
                    if CALLER_SAVE_REGS.len() % 2 == 1 {
                        self.emit_sp_adjust(8);
                    }
                    for reg in CALLER_SAVE_REGS.iter().rev() {
                        self.emit_pop(&AsmArg::Reg(reg));
                    }
                }
                _ => {
                    let mut offset = 0;
                    for _ in 0..*n {
                        self.asm.load_int_or_bool_const(
                            val,
                            &self
                                .stack_slot_resolver
                                .borrow()
                                .resolve(stack_slot_ref, offset),
                        );
                        offset += val.size() as i64;
                    }
                }
            },
        }
    }
}

fn identify_fast_arg_insts(l: &LoweredMethod) -> Option<HashSet<InstRef>> {
    let n_args = l.method.params.len();
    let n_reg_args = n_args.min(6);
    let mut arg_loading_insts = HashSet::new();
    for inst_ref in l.method.block(l.method.entry).insts.iter() {
        match l.method.inst(*inst_ref) {
            Inst::Load(Address::Local(stack_slot)) if stack_slot.0 < n_reg_args => {
                arg_loading_insts.insert(*inst_ref);
            }
            _ => break,
        }
    }
    // Then, make sure that these stack slots are not used in any other way.
    for (inst_ref, inst) in l.method.iter_insts() {
        if arg_loading_insts.contains(&inst_ref) {
            continue;
        }
        if matches!(
            inst,
            Inst::Load(Address::Local(stack_slot)) | Inst::Store { addr: Address::Local(stack_slot), .. }
            if stack_slot.0 < n_reg_args
        ) {
            return None;
        }
    }
    Some(arg_loading_insts)
}

// Test the fast division algorithm
// pub fn test_div(d: i64) {
//     use num_bigint::BigInt;
//     use rand::prelude::*;

//     let d_abs = d.abs();
//     let log2_d_ceil = 64 - (d_abs - 1).leading_zeros();
//     let l = log2_d_ceil.max(1);
//     let m = 1 + (BigInt::from(1) << (63 + l)) / d_abs;
//     let m_ = i64::try_from(m - (BigInt::from(1) << 64)).unwrap();

//     let mulsh = |n: i64| i64::try_from((BigInt::from(m_) * n) >> 64).unwrap();

//     let mut rng = ChaCha20Rng::seed_from_u64(61106035);
//     if d > 0 {
//         for _ in 0..1000000 {
//             let n = rng.gen_range(i64::MIN..=i64::MAX);
//             let q0 = n + mulsh(n);
//             let q = (q0 >> (l - 1)) - (n >> 63);
//             assert!(q == n / d, "n: {}, q: {}, q0: {}", n, q, q0);
//         }
//     } else {
//         for _ in 0..1000000 {
//             let n = rng.gen_range(i64::MIN..=i64::MAX);
//             let q0 = n + mulsh(n);
//             let q = (q0 >> (l - 1)) - (n >> 63);
//             assert!(-q == n / d, "n: {}, q: {}, q0: {}", n, q, q0);
//         }
//     }
// }
