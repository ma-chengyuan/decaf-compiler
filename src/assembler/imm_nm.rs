//! Immediate non-materializer.
//!
//! Our IR does not encode immediates directly, but instead uses a separate
//! LoadConst instruction. This means that constants are by default all
//! materialized into registers. But why place a constant in a register when it
//! can be encoded as an immediate? This module performs this optimization.

use std::collections::HashSet;

use crate::{
    inter::{constant::Const, ir::Inst},
    utils::cli::Optimization,
};

use super::{LoweredMethod, NonMaterializedArgMapExt};

pub struct ImmediateNonMaterializer<'a> {
    l: &'a mut LoweredMethod,
    opts: &'a HashSet<Optimization>,
}

impl<'a> ImmediateNonMaterializer<'a> {
    pub fn new(l: &'a mut LoweredMethod, opts: &'a HashSet<Optimization>) -> Self {
        ImmediateNonMaterializer { l, opts }
    }

    pub fn run(mut self) {
        let LoweredMethod {
            method, nm_args, ..
        } = &mut self.l;

        let is_const = |inst_ref| matches!(method.inst(inst_ref), Inst::LoadConst(_));
        let is_const_32 = |inst_ref| match method.inst(inst_ref) {
            Inst::LoadConst(Const::Int(i)) => i32::MIN as i64 <= *i && *i <= i32::MAX as i64,
            Inst::LoadConst(Const::Bool(_)) => true,
            _ => false,
        };
        let is_const_index = |inst_ref| match method.inst(inst_ref) {
            Inst::LoadConst(Const::Int(i)) => {
                (i32::MIN as i64) / 8 <= *i && *i <= (i32::MAX as i64) / 8
            }
            Inst::LoadConst(Const::Bool(_)) => true,
            _ => false,
        };

        for (inst_ref, inst) in method.iter_insts() {
            macro_rules! unmaterialize_if {
                ($pred:ident($arg:expr)) => {
                    if nm_args.is_materialized(inst_ref, $arg) && $pred($arg) {
                        // println!("unmaterializing {} in {}", $arg, inst_ref);
                        nm_args.entry(inst_ref).or_default().insert($arg);
                    }
                };
            }
            match inst {
                Inst::Copy(src) => unmaterialize_if!(is_const(*src)),
                Inst::Add(lhs, rhs)
                | Inst::Sub(lhs, rhs)
                | Inst::Mul(lhs, rhs)
                | Inst::Mod(lhs, rhs)
                | Inst::Eq(lhs, rhs)
                | Inst::Neq(lhs, rhs)
                | Inst::Less(lhs, rhs)
                | Inst::LessEq(lhs, rhs) => {
                    unmaterialize_if!(is_const_32(*lhs));
                    unmaterialize_if!(is_const_32(*rhs));
                }
                Inst::Div(lhs, rhs) => {
                    unmaterialize_if!(is_const_32(*lhs));
                    if self
                        .opts
                        .contains(&Optimization::ConstDivisorStrengthReduction)
                    {
                        unmaterialize_if!(is_const_32(*rhs));
                    }
                }
                Inst::LoadArray { index, .. } => {
                    unmaterialize_if!(is_const_index(*index));
                }
                Inst::StoreArray { index, value, .. } => {
                    unmaterialize_if!(is_const_index(*index));
                    unmaterialize_if!(is_const(*value));
                }
                Inst::Call { args, .. } => {
                    for arg_ref in args {
                        unmaterialize_if!(is_const(*arg_ref));
                    }
                }
                // TODO: handle other instructions
                _ => {}
            }
        }
    }
}
