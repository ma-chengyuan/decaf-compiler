use std::collections::HashMap;

use crate::inter::{
    constant::Const,
    ir::{Address, GlobalVar, Inst, InstRef, Method, Program, StackSlotRef},
    types::{PrimitiveType, Type, BOOL_SIZE, INT_SIZE},
};

pub struct Assembler {
    program: Program,
}

impl Assembler {
    pub fn new(program: Program) -> Self {
        Self { program }
    }

    pub fn assemble(&self) -> String {
        let mut output = String::new();
        output.push_str("; Globals\n");
        output.push_str(".data\n");
        for global in self.program.globals.values() {
            let global_code = self.assemble_global(global);
            output.push_str(global_code.as_str());
        }
        output.push_str("\nn; Methods\n");
        output.push_str(".text\n");
        output.push_str(".globl main\n");
        for method in self.program.methods.values() {
            let method_code = self.assemble_method(method);
            output.push_str(method_code.as_str());
        }
        output
    }

    fn assemble_method(&self, method: &Method) -> String {
        let mut output = format!("{}:\n", method.name.inner);

        // Compute stack spacesl
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
        output.push_str(format!("    enterq ${}, $0\n", stack_space).as_str());
        // Save all callee-saved registers
        for reg in &["rbx", "rbp", "r12", "r13", "r14", "r15"] {
            output.push_str(format!("    pushq %{}\n", reg).as_str());
        }

        // for (block_idx, bloc)

        let get_inst_ref_location = |iref| format!("{}(%rbp)", inst_to_offset[iref]);

        for (inst_ref, inst) in method.iter_insts() {
            let ins_offset = inst_to_offset[&inst_ref];
            match inst {
                Inst::Add(lhs, rhs) | Inst::Sub(lhs, rhs) | Inst::Mul(lhs, rhs) => {
                    let inst_name = match inst {
                        Inst::Add(_, _) => "add",
                        Inst::Sub(_, _) => "sub",
                        Inst::Mul(_, _) => "imul",
                        _ => unreachable!(),
                    };
                    output.push_str(
                        format!("    movq {}, %rax\n", get_inst_ref_location(lhs)).as_str(),
                    );
                    output.push_str(
                        format!("    {}q {}, %rax\n", inst_name, get_inst_ref_location(rhs))
                            .as_str(),
                    );
                    output.push_str(
                        format!("    movq %rax, {}\n", get_inst_ref_location(&inst_ref)).as_str(),
                    );
                }
                Inst::Div(lhs, rhs) | Inst::Mod(lhs, rhs) => {
                    output.push_str(
                        format!("    movq {}, %rax\n", get_inst_ref_location(lhs)).as_str(),
                    );
                    output.push_str(format!("    cqto\n").as_str()); // Godbolt does it
                    output.push_str(format!("    idivq {}\n", get_inst_ref_location(rhs)).as_str());

                    // Behavior depends on whether div or mod

                    output.push_str(
                        format!(
                            "    movq %{}, {}\n",
                            match inst {
                                Inst::Div(_, _) => "rax",
                                Inst::Mod(_, _) => "rdx",
                                _ => unreachable!(),
                            },
                            get_inst_ref_location(&inst_ref)
                        )
                        .as_str(),
                    );
                }
                Inst::Neg(var) | Inst::Not(var) => {
                    output.push_str(
                        format!("    movq {}, %rax\n", get_inst_ref_location(var)).as_str(),
                    );
                    output.push_str(
                        format!(
                            "    {}q %rax\n",
                            match inst {
                                Inst::Neg(_) => "neg",
                                Inst::Not(_) => "not",
                                _ => unreachable!(),
                            }
                        )
                        .as_str(),
                    );
                    output.push_str(
                        format!("    movq %rax, {}\n", get_inst_ref_location(&inst_ref)).as_str(),
                    );
                }
                Inst::Eq(lhs, rhs) => {
                    output.push_str(
                        format!("    cmpq {}, {}\n", get_inst_ref_location(lhs), get_inst_ref_location(rhs)).as_str(),
                    );
                    output.push_str(
                        format!("    sete %al\n").as_str(),
                    );
                    output.push_str(
                        format!("    movzbq %al, {}\n", get_inst_ref_location(&inst_ref)).as_str(),
                    );
                }
                Inst::Neq(lhs, rhs) => {
                    output.push_str(
                        format!("    cmpq {}, {}\n", get_inst_ref_location(lhs), get_inst_ref_location(rhs)).as_str(),
                    );
                    output.push_str(
                        format!("    setne %al\n").as_str(),
                    );
                    output.push_str(
                        format!("    movzbq %al, {}\n", get_inst_ref_location(&inst_ref)).as_str(),
                    );
                }
                Inst::Less(lhs, rhs) => {
                    output.push_str(
                        format!("    cmpq {}, {}\n", get_inst_ref_location(lhs), get_inst_ref_location(rhs)).as_str(),
                    );
                    output.push_str(
                        format!("    setl %al\n").as_str(),
                    );
                    output.push_str(
                        format!("    movzbq %al, {}\n", get_inst_ref_location(&inst_ref)).as_str(),
                    );
                }
                Inst::LessEq(lhs, rhs) => {
                    output.push_str(
                        format!("    cmpq {}, {}\n", get_inst_ref_location(lhs), get_inst_ref_location(rhs)).as_str(),
                    );
                    output.push_str(
                        format!("    setle %al\n").as_str(),
                    );
                    output.push_str(
                        format!("    movzbq %al, {}\n", get_inst_ref_location(&inst_ref)).as_str(),
                    );
                }

                Inst::Call {
                    method: callee_name,
                    args,
                } => {
                    let arg_registers = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"];
                    for (arg_idx, arg_ref) in args.iter().enumerate() {
                        output.push_str(
                            format!(
                                "    movq {}, {}\n",
                                get_inst_ref_location(arg_ref),
                                arg_registers[arg_idx]
                            )
                            .as_str(),
                        );
                    }
                    output.push_str(format!("    call {}", callee_name).as_str());
                }
                _ => todo!(),
            }
        }

        output.push_str("ret\n");
        output
    }

    fn assemble_global(&self, var: &GlobalVar) -> String {
        let mut output = format!("{}:\n", var.name.inner);
        match var.ty {
            Type::Void => unreachable!(),
            Type::Primitive(PrimitiveType::Int) => {
                let Const::Int(val) = var.init else {
                    unreachable!();
                };
                output.push_str(format!("   .quad {}\n", val).as_str());
            }
            Type::Primitive(PrimitiveType::Bool) => {
                let Const::Bool(val) = var.init else {
                    unreachable!();
                };
                output.push_str(format!("   .quad {}\n", if val { "1" } else { "0" }).as_str());
            }
            Type::Array { base, length } => {
                let Const::Array(ref val) = var.init else {
                    unreachable!();
                };
                for value in val.iter() {
                    let outval: i64 = match value {
                        Const::Int(v) => v,
                        Const::Bool(b) => {
                            if b {
                                1i64
                            } else {
                                0i64
                            }
                        }
                        Const::Array(arr) => unreachable!(),
                    };
                    output.push_str(format!("   .quad {}\n", outval).as_str());
                }
            }
            Type::Invalid => unreachable!(),
        }
        output.push_str("    .align 16");
        output
    }
}
