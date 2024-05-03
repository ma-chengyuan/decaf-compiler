use std::collections::HashMap;

use crate::inter::{
    constant::Const,
    ir::{Inst, Method},
};

pub fn fold_constants(method: &mut Method) {
    let dom = crate::opt::dom::compute_dominance(method);
    let mut constant_instructions = HashMap::new();

    for block in dom.preorder(method.entry) {
        for inst in method.block(block).insts.clone() {
            match method.inst_mut(inst) {
                Inst::LoadConst(value) => {
                    constant_instructions.insert(inst, value.clone());
                }
                Inst::Copy(copied_inst) => {
                    if let Some(val) = constant_instructions.get(copied_inst) {
                        constant_instructions.insert(inst, val.clone());
                    }
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
                            let result = match method.inst(inst) {
                                Inst::Add(..) => a + b,
                                Inst::Sub(..) => a - b,
                                Inst::Mul(..) => a * b,
                                Inst::Div(..) => a / b,
                                Inst::Mod(..) => a % b,
                                _ => unreachable!(),
                            };
                            *method.inst_mut(inst) = Inst::LoadConst(Const::Int(result));
                            constant_instructions.insert(inst, Const::Int(result));
                        } else {
                            panic!("expected add/sub/mul/div/mod instruction arguments to both be integers");
                        }
                    }
                }
                _ => {}
            }
        }
    }
}
