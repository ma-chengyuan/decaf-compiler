use std::collections::HashMap;

use crate::inter::{
    constant::Const,
    ir::{
        Address, Annotation, GlobalVar, Inst, InstRef, Method, Program, StackSlotRef, Terminator,
    },
    types::{Type, BOOL_SIZE, INT_SIZE},
};

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

    /// Compiles the given program and returns the corresponding assembly code
    pub fn assemble(&mut self) -> String {
        // todo: remove the .clone()
        for global in self.program.globals.clone().values() {
            self.assemble_global(global);
        }

        // todo: remove the .clone()
        for method in self.program.methods.clone().values() {
            self.assemble_method(method);
        }

        self.emit_data_label("index_out_of_bounds_msg");
        self.emit_data_code(".string \"Error: index out of bounds on line %d. Array length is %d; queried index is %d.\\n\"");

        let mut output = String::from(".file 0 \"myfile.dcf\"\n.data\n");
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

    fn assemble_method(&mut self, method: &Method) {
        self.emit_label(&method.name.inner);
        let arg_registers = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"];

        // Compute stack spaces
        let mut stack_space = 0i64;
        // Everything has a home on the stack -- for now?
        let mut stack_slot_to_offset: HashMap<StackSlotRef, i64> = HashMap::new();
        for (stack_slot_ref, stack_slot) in method.iter_slack_slots() {
            stack_space += stack_slot.ty.size() as i64;
            stack_slot_to_offset.insert(stack_slot_ref, -stack_space);
        }
        let mut inst_to_offset: HashMap<InstRef, i64> = HashMap::new();

        // Declare as macro to work around borrow checker
        // Can't use regular functions because it would borrow self.program.globals
        macro_rules! address_to_ty {
            ($addr:expr) => {
                (match $addr {
                    Address::Local(stack_slot) => &method.stack_slot(*stack_slot).ty,
                    Address::Global(name) => &self.program.globals[&name.to_string()].ty,
                })
            };
        }

        macro_rules! block_ref_to_label {
            ($block_ref:expr) => {
                format!("{}_method_{}", $block_ref, method.name.inner)
            };
        }

        for (inst_ref, inst) in method.iter_insts() {
            let size = match inst {
                Inst::Add(_, _)
                | Inst::Sub(_, _)
                | Inst::Mul(_, _)
                | Inst::Div(_, _)
                | Inst::Mod(_, _)
                | Inst::Neg(_) => INT_SIZE,
                Inst::Eq(_, _)
                | Inst::Neq(_, _)
                | Inst::Less(_, _)
                | Inst::LessEq(_, _)
                | Inst::Not(_) => BOOL_SIZE,
                Inst::Load(addr) => address_to_ty!(addr).size(),
                Inst::LoadArray { addr, .. } => match address_to_ty!(addr) {
                    Type::Array { base, .. } => base.size(),
                    _ => unreachable!(),
                },
                Inst::LoadConst(c) => c.size(),
                Inst::LoadStringLiteral(_) => INT_SIZE,
                Inst::Call { method, .. } => self
                    .program
                    .methods
                    .get(&method.to_string())
                    .map(|m| m.return_ty.size())
                    .unwrap_or(INT_SIZE),
                // No IR is allowed to depend on the return value of these instructions
                Inst::Store { .. } | Inst::StoreArray { .. } | Inst::Initialize { .. } => 0,
                Inst::Phi(_) => unimplemented!("Phi nodes not supported in assembly"),
                Inst::Illegal => unreachable!(),
            };
            stack_space += size as i64;
            // todo: should this line go here or at the top of the for loop?
            inst_to_offset.insert(inst_ref, -stack_space);
        }
        // Align stack space to 16 bytes
        stack_space = (stack_space + 15) & !15;

        self.emit_code(format!("enterq ${}, $0", stack_space));
        // Save all callee-saved registers
        for reg in &["rbx", "rbp", "r12", "r13", "r14", "r15"] {
            self.emit_code(format!("pushq %{}", reg));
        }

        // parameters 1..n are mapped to the first n stack slots by our IR builder
        {
            let n_args = method.params.len();
            for (arg_idx, arg_slot_iter) in
                method.iter_slack_slots().enumerate().take(n_args).take(6)
            {
                self.emit_code(format!(
                    "movq %{}, {}(%rbp)",
                    arg_registers[arg_idx], stack_slot_to_offset[&arg_slot_iter.0]
                ));
            }
            let mut stack_offset = 16; // return address is 8 bytes. saved rbp is also 8 bytes.
            for (arg_slot_ref, arg_slot) in method.iter_slack_slots().skip(6) {
                self.emit_code(format!("movq {}(%rbp), %rax", stack_offset));
                stack_offset += arg_slot.ty.size() as i64;
                self.emit_code(format!(
                    "movq %rax, {}(%rbp)",
                    stack_slot_to_offset[&arg_slot_ref]
                ));
            }
        }

        let get_inst_ref_location = |iref: InstRef| format!("{}(%rbp)", inst_to_offset[&iref]);

        // The entry block is assumed to be the first block in the method for now
        assert!(method.entry == method.iter_blocks().next().unwrap().0);
        for (block_ref, block) in method.iter_blocks() {
            let annotation_comment = match method.get_block_annotation(&block_ref) {
                Some(annotation) => annotation.to_string(),
                None => "No annotation available".to_string(),
            };
            self.emit_annotated_label(&block_ref_to_label!(block_ref), &annotation_comment);

            for (inst_ref, inst) in block.insts.iter().map(|iref| (*iref, method.inst(*iref))) {
                if let Some(annotation) = method.get_inst_annotation(&inst_ref) {
                    let start_loc = annotation.span.clone().unwrap().start().to_owned();
                    self.emit_annotated_code(
                        format!(".loc 0 {} {}", start_loc.line, start_loc.column),
                        &annotation.to_string(),
                    );
                } else {
                    self.emit_code(format!("# No annotation available for inst {}", inst_ref));
                }
                match inst {
                    Inst::Add(lhs, rhs) | Inst::Sub(lhs, rhs) | Inst::Mul(lhs, rhs) => {
                        let inst_name = match inst {
                            Inst::Add(_, _) => "add",
                            Inst::Sub(_, _) => "sub",
                            Inst::Mul(_, _) => "imul",
                            _ => unreachable!(),
                        };
                        self.emit_code(format!("movq {}, %rax", get_inst_ref_location(*lhs)));
                        self.emit_code(format!(
                            "{}q {}, %rax",
                            inst_name,
                            get_inst_ref_location(*rhs)
                        ));
                        self.emit_code(format!("movq %rax, {}", get_inst_ref_location(inst_ref)));
                    }
                    Inst::Div(lhs, rhs) | Inst::Mod(lhs, rhs) => {
                        self.emit_code(format!("movq {}, %rax", get_inst_ref_location(*lhs)));
                        self.emit_code("cqto"); // Godbolt does it
                        self.emit_code(format!("idivq {}", get_inst_ref_location(*rhs)));

                        // Behavior depends on whether div or mod
                        self.emit_code(format!(
                            "movq %{}, {}",
                            match inst {
                                Inst::Div(_, _) => "rax",
                                Inst::Mod(_, _) => "rdx",
                                _ => unreachable!(),
                            },
                            get_inst_ref_location(inst_ref)
                        ));
                    }
                    Inst::Neg(var) => {
                        self.emit_code(format!("movq {}, %rax", get_inst_ref_location(*var)));
                        self.emit_code("negq %rax");
                        self.emit_code(format!("movq %rax, {}", get_inst_ref_location(inst_ref)));
                    }
                    Inst::Not(var) => {
                        self.emit_code(format!("cmpq $0, {}", get_inst_ref_location(*var)));
                        self.emit_code("sete %al");
                        self.emit_code(format!("movzbq %al, %rax"));
                        self.emit_code(format!("movq %rax, {}", get_inst_ref_location(inst_ref)));
                    }
                    Inst::Eq(lhs, rhs) => {
                        self.emit_code(format!("movq {}, %rax", get_inst_ref_location(*rhs)));
                        self.emit_code(format!("cmpq %rax, {}", get_inst_ref_location(*lhs)));
                        self.emit_code("sete %al");
                        self.emit_code(format!("movzbq %al, %rax"));
                        self.emit_code(format!("movq %rax, {}", get_inst_ref_location(inst_ref)));
                    }
                    Inst::Neq(lhs, rhs) => {
                        self.emit_code(format!("movq {}, %rax", get_inst_ref_location(*rhs)));
                        self.emit_code(format!("cmpq %rax, {}", get_inst_ref_location(*lhs)));
                        self.emit_code("setne %al");
                        self.emit_code(format!("movzbq %al, %rax"));
                        self.emit_code(format!("movq %rax, {}", get_inst_ref_location(inst_ref)));
                    }
                    Inst::Less(lhs, rhs) => {
                        self.emit_code(format!("movq {}, %rax", get_inst_ref_location(*rhs)));
                        self.emit_code(format!("cmpq %rax, {}", get_inst_ref_location(*lhs)));
                        self.emit_code("setl %al");
                        self.emit_code(format!("movzbq %al, %rax"));
                        self.emit_code(format!("movq %rax, {}", get_inst_ref_location(inst_ref)));
                    }
                    Inst::LessEq(lhs, rhs) => {
                        self.emit_code(format!("movq {}, %rax", get_inst_ref_location(*rhs)));
                        self.emit_code(format!("cmpq %rax, {}", get_inst_ref_location(*lhs)));
                        self.emit_code("setle %al");
                        self.emit_code(format!("movzbq %al, %rax"));
                        self.emit_code(format!("movq %rax, {}", get_inst_ref_location(inst_ref)));
                    }
                    Inst::LoadConst(value) => {
                        self.load_int_or_bool_const(value, &get_inst_ref_location(inst_ref));
                    }
                    Inst::Load(addr) => {
                        match addr {
                            Address::Global(name) => {
                                self.emit_code(format!("movq {}(%rip), %rax", name));
                            }
                            Address::Local(stack_slot) => {
                                self.emit_code(format!(
                                    "movq {}(%rbp), %rax",
                                    stack_slot_to_offset[stack_slot]
                                ));
                            }
                        }
                        self.emit_code(format!("movq %rax, {}", get_inst_ref_location(inst_ref)));
                    }
                    Inst::Store { addr, value } => {
                        self.emit_code(format!("movq {}, %rax", get_inst_ref_location(*value)));
                        match addr {
                            Address::Global(name) => {
                                self.emit_code(format!("movq %rax, {}(%rip)", name));
                            }
                            Address::Local(stack_slot) => {
                                self.emit_code(format!(
                                    "movq %rax, {}(%rbp)",
                                    stack_slot_to_offset[stack_slot]
                                ));
                            }
                        }
                    }
                    Inst::LoadArray { addr, index } => {
                        // Do bound check first
                        self.emit_code(format!("movq {}, %rax", get_inst_ref_location(*index)));
                        let (length, elem_size) = match address_to_ty!(addr) {
                            Type::Array { length, base } => (*length, base.size()),
                            _ => unreachable!(),
                        };
                        self.emit_bounds_check(length, method.get_inst_annotation(index).unwrap());
                        match addr {
                            Address::Global(name) => {
                                self.emit_code(format!(
                                    "movq {}(, %rax, {}), %rax",
                                    name, elem_size
                                ));
                            }
                            Address::Local(stack_slot) => {
                                self.emit_code(format!(
                                    "movq {}(%rbp, %rax, {}), %rax",
                                    stack_slot_to_offset[stack_slot], elem_size
                                ));
                            }
                        }
                        self.emit_code(format!("movq %rax, {}", get_inst_ref_location(inst_ref)));
                    }
                    Inst::StoreArray { addr, index, value } => {
                        self.emit_code(format!("movq {}, %rax", get_inst_ref_location(*index)));
                        let (length, elem_size) = match address_to_ty!(addr) {
                            Type::Array { length, base } => (*length, base.size()),
                            _ => unreachable!(),
                        };
                        self.emit_bounds_check(length, method.get_inst_annotation(index).unwrap());
                        self.emit_code(format!("movq {}, %rcx", get_inst_ref_location(*value)));
                        match addr {
                            Address::Global(name) => {
                                self.emit_code(format!(
                                    "movq %rcx, {}(, %rax, {})",
                                    name, elem_size
                                ));
                            }
                            Address::Local(stack_slot) => {
                                self.emit_code(format!(
                                    "movq %rcx, {}(%rbp, %rax, {})",
                                    stack_slot_to_offset[stack_slot], elem_size
                                ));
                            }
                        }
                    }
                    Inst::Initialize { stack_slot, value } => match value {
                        Const::Int(_) | Const::Bool(_) => {
                            self.load_int_or_bool_const(
                                value,
                                &format!("{}(%rbp)", stack_slot_to_offset[stack_slot]),
                            );
                        }
                        Const::Array(arr_vals) => {
                            let mut stack_slot = stack_slot_to_offset[stack_slot];
                            for val in arr_vals.iter() {
                                self.load_int_or_bool_const(val, &format!("{}(%rbp)", stack_slot));
                                stack_slot += val.size() as i64;
                            }
                        }
                    },
                    Inst::Call {
                        method: callee_name,
                        args,
                    } => {
                        for (arg_idx, arg_ref) in args.iter().enumerate().take(6) {
                            self.emit_code(format!(
                                "movq {}, %{}",
                                get_inst_ref_location(*arg_ref),
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
                            self.emit_code(format!("pushq {}", get_inst_ref_location(*arg_ref)));
                            stack_space_for_args += 8;
                        }
                        self.emit_code(format!("call {}", callee_name));
                        if stack_space_for_args > 0 {
                            self.emit_code(format!("addq ${}, %rsp", stack_space_for_args));
                        }
                        let tmp = get_inst_ref_location(inst_ref);
                        self.emit_code(format!("movq %rax, {}", tmp));
                    }
                    Inst::LoadStringLiteral(s) => {
                        let str_name = format!("str_{}", self.data.len());
                        self.emit_data_label(&str_name);
                        self.emit_data_code(format!(".string {:?}", s));
                        self.emit_code(format!("leaq {}(%rip), %rax", str_name));
                        self.emit_code(format!("movq %rax, {}", get_inst_ref_location(inst_ref)));
                    }
                    Inst::Phi(_) => unimplemented!("Phi nodes not supported in assembly"),
                    Inst::Illegal => unreachable!(),
                }
            }

            self.emit_code(format!(
                "# Terminating block {}",
                block_ref_to_label!(block_ref)
            ));
            match &block.term {
                Terminator::Return(ret) => {
                    if let Some(ret) = ret {
                        self.emit_code(format!("movq {}, %rax", get_inst_ref_location(*ret)));
                    }

                    if method.name.inner.as_ref() == "main" {
                        assert!(ret.is_none());
                        // return 0;
                        self.emit_code("movq $0, %rax");
                    }

                    // Restore all callee-saved registers
                    for reg in ["rbx", "rbp", "r12", "r13", "r14", "r15"].iter().rev() {
                        self.emit_code(format!("popq %{}", reg));
                    }
                    // Restore stack frame
                    self.emit_code("leave");
                    self.emit_code("ret");
                }
                Terminator::Jump(target) => {
                    self.emit_code(format!("jmp {}", block_ref_to_label!(target)));
                }
                Terminator::CondJump {
                    cond,
                    true_,
                    false_,
                } => {
                    self.emit_code(format!("cmpq $0, {}", get_inst_ref_location(*cond)));
                    self.emit_code(format!("je {}", block_ref_to_label!(false_)));
                    self.emit_code(format!("jmp {}", block_ref_to_label!(true_)));
                }
            }
        }
    }

    /// Checks if %rax is in [0, length) and panics if not
    fn emit_bounds_check(&mut self, length: usize, inst_annotation: &Annotation) {
        let fail_branch = format!("bound_check_fail_{}", self.code.len());
        let pass_branch = format!("bound_check_pass_{}", self.code.len());
        self.emit_code("cmpq $0, %rax");
        self.emit_code(format!("jl {}", fail_branch));
        self.emit_code(format!("cmpq ${}, %rax", length));
        self.emit_code(format!("jl {}", pass_branch));
        self.emit_label(&fail_branch);
        // print an error message.
        // first argument is the format string, second is the line number, third is arr.len, fourth is the index
        self.emit_code("leaq index_out_of_bounds_msg(%rip), %rdi");
        self.emit_code(format!(
            "movq ${}, %rsi",
            inst_annotation.span.clone().unwrap().start().line
        ));
        self.emit_code(format!("movq ${}, %rdx", length));
        self.emit_code("movq %rax, %rcx");
        self.emit_code("call printf");
        // Call exit(-1)
        self.emit_code("movq $-1, %rdi");
        self.emit_code("call exit");
        self.emit_label(&pass_branch);
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
