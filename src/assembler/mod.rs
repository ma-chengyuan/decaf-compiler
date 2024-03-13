use std::collections::HashMap;

use crate::inter::{
    constant::Const,
    ir::{Address, GlobalVar, Inst, InstRef, Method, Program, StackSlotRef},
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

    fn emit_label(&mut self, label: &str) {
        self.code.push(format!("{}:", label));
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

        let mut output = String::from(".data\n");
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

        let get_inst_ref_location = |iref: InstRef| format!("{}(%rbp)", inst_to_offset[&iref]);

        for (inst_ref, inst) in method.iter_insts() {
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
                Inst::Neg(var) | Inst::Not(var) => {
                    self.emit_code(format!("movq {}, %rax", get_inst_ref_location(*var)));
                    self.emit_code(format!(
                        "{}q %rax",
                        match inst {
                            Inst::Neg(_) => "neg",
                            Inst::Not(_) => "not",
                            _ => unreachable!(),
                        }
                    ));
                    self.emit_code(format!("movq %rax, {}", get_inst_ref_location(inst_ref)));
                }
                Inst::Eq(lhs, rhs) => {
                    self.emit_code(format!(
                        "cmpq {}, {}",
                        get_inst_ref_location(*lhs),
                        get_inst_ref_location(*rhs)
                    ));
                    self.emit_code("sete %al");
                    self.emit_code(format!("movzbq %al, {}", get_inst_ref_location(inst_ref)));
                }
                Inst::Neq(lhs, rhs) => {
                    self.emit_code(format!(
                        "cmpq {}, {}",
                        get_inst_ref_location(*lhs),
                        get_inst_ref_location(*rhs)
                    ));
                    self.emit_code("setne %al");
                    self.emit_code(format!("movzbq %al, {}", get_inst_ref_location(inst_ref)));
                }
                Inst::Less(lhs, rhs) => {
                    self.emit_code(format!(
                        "cmpq {}, {}",
                        get_inst_ref_location(*lhs),
                        get_inst_ref_location(*rhs)
                    ));
                    self.emit_code("setl %al");
                    self.emit_code(format!("movzbq %al, {}", get_inst_ref_location(inst_ref)));
                }
                Inst::LessEq(lhs, rhs) => {
                    self.emit_code(format!(
                        "cmpq {}, {}",
                        get_inst_ref_location(*lhs),
                        get_inst_ref_location(*rhs)
                    ));
                    self.emit_code("setle %al");
                    self.emit_code(format!("movzbq %al, {}", get_inst_ref_location(inst_ref)));
                }
                Inst::LoadConst(value) => {
                    self.load_int_or_bool_const(value, &get_inst_ref_location(inst_ref));
                }

                Inst::Call {
                    method: callee_name,
                    args,
                } => {
                    let arg_registers = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"];
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
                    self.emit_data_code(".align 16");
                    self.emit_code(format!("leaq {}(%rip), %rax", str_name));
                    self.emit_code(format!("movq %rax, {}", get_inst_ref_location(inst_ref)));
                }
                Inst::LoadArray { addr, index } => {
                    // Do bound check first
                    self.emit_code(format!("movq {}, %rax", get_inst_ref_location(*index)));
                    let (length, elem_size) = match address_to_ty!(addr) {
                        Type::Array { length, base } => (*length, base.size()),
                        _ => unreachable!(),
                    };
                    self.emit_bounds_check(length);
                    match addr {
                        Address::Global(name) => {
                            self.emit_code(format!(
                                "movq {}(%rip, %rax, {}), %rax",
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
                    self.emit_bounds_check(length);
                    self.emit_code(format!("movq {}, %rcx", get_inst_ref_location(*value)));
                    match addr {
                        Address::Global(name) => {
                            self.emit_code(format!(
                                "movq %rcx, {}(%rip, %rax, {})",
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
                x => todo!("{:?}", x),
            }
        }

        if method.name.inner.as_ref() == "main" {
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

    /// Checks if %rax is in [0, length) and panics if not
    fn emit_bounds_check(&mut self, length: usize) {
        let fail_branch = format!("bound_check_fail_{}", self.code.len());
        let pass_branch = format!("bound_check_pass_{}", self.code.len());
        self.emit_code("cmpq $0, %rax");
        self.emit_code(format!("jl {}", fail_branch));
        self.emit_code(format!("cmpq ${}, %rax", length));
        self.emit_code(format!("jl {}", pass_branch));
        self.emit_label(&fail_branch);
        // Call exit(-1)
        self.emit_code("movq $-1, %rdi");
        // TODO: use a more descriptive error message
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
