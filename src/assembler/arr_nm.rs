//! Array access offset non-materializer.
//!
//!

use crate::inter::{
    constant::Const,
    ir::{Inst, InstRef},
};

use super::LoweredMethod;

pub struct ArrayAccessOffsetNonMaterializer<'a> {
    l: &'a mut LoweredMethod,
}

impl<'a> ArrayAccessOffsetNonMaterializer<'a> {
    pub fn new(l: &'a mut LoweredMethod) -> Self {
        ArrayAccessOffsetNonMaterializer { l }
    }

    pub fn run(mut self) {
        let LoweredMethod {
            method,
            array_offsets,
            ..
        } = &mut self.l;

        // Don's absorb absurdly large offsets.
        let should_absorb = |offset: i64| (-4096..=4096).contains(&offset);
        for inst_ref in (0..method.n_insts()).map(InstRef) {
            match method.inst(inst_ref) {
                Inst::LoadArray { index, .. } | Inst::StoreArray { index, .. } => {
                    let mut modified_index: Option<InstRef> = None;
                    match method.inst(*index) {
                        Inst::Add(lhs, rhs) => {
                            if let Inst::LoadConst(Const::Int(offset)) = method.inst(*rhs) {
                                if should_absorb(*offset) {
                                    array_offsets.insert(inst_ref, *offset);
                                    modified_index = Some(*lhs);
                                }
                            } else if let Inst::LoadConst(Const::Int(offset)) = method.inst(*lhs) {
                                if should_absorb(*offset) {
                                    array_offsets.insert(inst_ref, *offset);
                                    modified_index = Some(*rhs);
                                }
                            }
                        }
                        Inst::Sub(lhs, rhs) => {
                            if let Inst::LoadConst(Const::Int(offset)) = method.inst(*rhs) {
                                if should_absorb(-offset) {
                                    array_offsets.insert(inst_ref, -offset);
                                    modified_index = Some(*lhs);
                                }
                            }
                        }
                        _ => {}
                    }
                    if let Some(modified_index) = modified_index {
                        // println!(
                        //     "Non-materializing array access offset in {}: {}+{}",
                        //     inst_ref, modified_index, array_offsets[&inst_ref]
                        // );
                        match method.inst_mut(inst_ref) {
                            Inst::LoadArray { index, .. } | Inst::StoreArray { index, .. } => {
                                *index = modified_index;
                            }
                            _ => unreachable!(),
                        }
                    }
                }
                _ => {}
            }
        }
    }
}
