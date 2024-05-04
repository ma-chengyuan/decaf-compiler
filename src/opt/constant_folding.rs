use std::{backtrace, collections::HashMap};

use crate::inter::{
    constant::Const,
    ir::{Inst, Method},
};

pub fn fold_constants(method: &mut Method) {
    let dom = crate::opt::dom::compute_dominance(method);
    let mut constant_instructions = HashMap::new();

    for block in dom.preorder(method.entry) {
        for inst in method.block(block).insts.clone() {
            let mut const_result = None;
            match method.inst_mut(inst) {
                Inst::LoadConst(value) => {
                    const_result = Some(value.clone());
                }
                Inst::Copy(copied_inst) => {
                    const_result = constant_instructions.get(copied_inst).cloned();
                }
                Inst::Add(a, b)
                | Inst::Sub(a, b)
                | Inst::Mul(a, b)
                | Inst::Div(a, b)
                | Inst::Mod(a, b) => {
                    if let (Some(a), Some(b)) =
                        (constant_instructions.get(a), constant_instructions.get(b))
                    {
                        if let (Const::Int(a), Const::Int(b)) = (a, b) {
                            const_result = Some(Const::Int(match method.inst(inst) {
                                Inst::Add(..) => a + b,
                                Inst::Sub(..) => a - b,
                                Inst::Mul(..) => a * b,
                                Inst::Div(..) => a / b,
                                Inst::Mod(..) => a % b,
                                _ => unreachable!(),
                            }));
                        } else {
                            unreachable!()
                        }
                    }
                }
                Inst::Not(a) => {
                    if let Some(a) = constant_instructions.get(a) {
                        if let Const::Bool(a) = a {
                            const_result = Some(Const::Bool(!a));
                        } else {
                            unreachable!()
                        }
                    }
                }
                Inst::Neg(a) => {
                    if let Some(a) = constant_instructions.get(a) {
                        if let Const::Int(a) = a {
                            const_result = Some(Const::Int(-a));
                        } else {
                            unreachable!()
                        }
                    }
                }
                Inst::Less(a, b) | Inst::LessEq(a, b) => {
                    if let (Some(a), Some(b)) =
                        (constant_instructions.get(a), constant_instructions.get(b))
                    {
                        if let (Const::Int(a), Const::Int(b)) = (a, b) {
                            const_result = Some(Const::Bool(match method.inst(inst) {
                                Inst::Less(..) => a < b,
                                Inst::LessEq(..) => a <= b,
                                _ => unreachable!(),
                            }));
                        } else {
                            unreachable!()
                        }
                    }
                }
                Inst::Eq(a, b) | Inst::Neq(a, b) => {
                    if let (Some(a), Some(b)) =
                        (constant_instructions.get(a), constant_instructions.get(b))
                    {
                        const_result = Some(Const::Bool(match method.inst(inst) {
                            Inst::Eq(..) => a == b,
                            Inst::Neq(..) => a != b,
                            _ => unreachable!(),
                        }))
                    }
                }
                _ => {}
            }
            if let Some(result) = const_result {
                *method.inst_mut(inst) = Inst::LoadConst(result.clone());
                constant_instructions.insert(inst, result);
            }
        }
    }
}
