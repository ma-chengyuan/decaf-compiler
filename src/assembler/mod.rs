use std::collections::HashMap;

use crate::inter::{
    constant::Const,
    ir::{Address, GlobalVar, Inst, InstRef, Method, Program, StackSlotRef},
    types::{PrimitiveType, Type, BOOL_SIZE, INT_SIZE},
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
        self.data.push(format!("    {}\n", code));
    }

    fn emit_data_label(&mut self, label: &str) {
        self.data.push(format!("{}:\n", label));
    }

    /// Emit a line of assembly to the code section
    fn emit_code<T: std::fmt::Display>(&mut self, code: T) {
        self.code.push(format!("    {}\n", code));
    }

    fn emit_label(&mut self, label: &str) {
        self.code.push(format!("{}:\n", label));
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
            stack_slot_to_offset.insert(stack_slot_ref, -stack_space);
            stack_space += stack_slot.ty.size() as i64;
        }
        let mut inst_to_offset: HashMap<InstRef, i64> = HashMap::new();
        for (inst_ref, inst) in method.iter_insts() {
            inst_to_offset.insert(inst_ref, -stack_space);
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
                Inst::Load(addr) => match addr {
                    Address::Local(stack_slot) => method.stack_slot(*stack_slot).ty.size(),
                    Address::Global(name) => self.program.globals[&name.to_string()].ty.size(),
                },
                Inst::LoadArray { addr, .. } => match addr {
                    Address::Local(stack_slot) => match &method.stack_slot(*stack_slot).ty {
                        Type::Array { base, .. } => base.size(),
                        _ => unreachable!(),
                    },
                    Address::Global(name) => match &self.program.globals[&name.to_string()].ty {
                        Type::Array { base, .. } => base.size(),
                        _ => unreachable!(),
                    },
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
        }
        // Align stack space to 16 bytes
        stack_space = (stack_space + 15) & !15;

        self.emit_code(format!("enterq ${}, $0", stack_space));
        // Save all callee-saved registers
        for reg in &["rbx", "rbp", "r12", "r13", "r14", "r15"] {
            self.emit_code(format!("pushq %{}", reg));
        }

        // for (block_idx, bloc)

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
                    match value {
                        Const::Int(v) => {
                            if *v <= i32::MAX as i64 && *v >= i32::MIN as i64 {
                                // Value fits within 32 bits, use movq
                                self.emit_code(format!(
                                    "movq ${}, {}",
                                    v,
                                    get_inst_ref_location(inst_ref)
                                ));
                            } else {
                                // Value requires more than 32 bits, use movabsq
                                self.emit_code(format!(
                                    "movabsq ${}, {}",
                                    v,
                                    get_inst_ref_location(inst_ref)
                                ));
                            }
                        }
                        Const::Bool(b) => {
                            // Boolean values always fit within 32 bits
                            let val = if *b { 1 } else { 0 };
                            self.emit_code(format!(
                                "movq ${}, {}",
                                val,
                                get_inst_ref_location(inst_ref)
                            ));
                        }
                        _ => unreachable!(),
                    }
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
                    self.emit_code(format!("leaq {}(%rip), %r10", str_name));
                    // todo: avoid using %r10 (leaq doesn't let you use two memory locations)
                    self.emit_code(format!("movq %r10, {}", get_inst_ref_location(inst_ref)));
                }
                _ => todo!(),
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

    fn assemble_global(&mut self, var: &GlobalVar) {
        match var.ty {
            Type::Void => unreachable!(),
            Type::Primitive(PrimitiveType::Int) => {
                let Const::Int(val) = var.init else {
                    unreachable!();
                };
                self.emit_data_code(format!(".quad {}", val));
            }
            Type::Primitive(PrimitiveType::Bool) => {
                let Const::Bool(val) = var.init else {
                    unreachable!();
                };
                self.emit_data_code(format!(".quad {}", if val { 1 } else { 0 }));
            }
            Type::Array { ref base, length } => {
                let Const::Array(ref val) = var.init else {
                    unreachable!();
                };
                for value in val.iter() {
                    let outval: i64 = match value {
                        Const::Int(v) => *v,
                        Const::Bool(b) => {
                            if *b {
                                1i64
                            } else {
                                0i64
                            }
                        }
                        Const::Array(arr) => unreachable!(),
                    };
                    self.emit_data_code(format!(".quad {}", outval));
                }
            }
            Type::Invalid => unreachable!(),
        }
        self.emit_data_code(".align 16");
    }
}
