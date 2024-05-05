//! Terminator Non-materializer

use crate::inter::ir::{Inst, Terminator};

use super::LoweredMethod;

pub struct TerminatorNonMaterializer<'a> {
    l: &'a mut LoweredMethod,
}

impl<'a> TerminatorNonMaterializer<'a> {
    pub fn new(l: &'a mut LoweredMethod) -> Self {
        TerminatorNonMaterializer { l }
    }

    pub fn run(self) {
        // if self.l.method.name.inner.as_ref() == "partition" {
        //     return;
        // }

        for block_ref in self.l.method.iter_block_refs() {
            let block = self.l.method.block(block_ref);
            let Terminator::CondJump { cond: cond_ref, .. } = block.term else {
                continue;
            };
            if !matches!(
                self.l.method.inst(cond_ref),
                Inst::Not(_)
                    | Inst::Eq(_, _)
                    | Inst::Neq(_, _)
                    | Inst::Less(_, _)
                    | Inst::LessEq(_, _)
            ) {
                continue;
            }
            let mut materialize = true;
            for inst_ref in block.insts.iter().rev() {
                if *inst_ref == cond_ref {
                    // Only choose not to materialize a conditional jump if it's
                    // the last instruction preceding the terminator -- that is
                    // if we ignore stores.
                    materialize = false;
                    break;
                }
                match self.l.method.inst(*inst_ref) {
                    // Stores are fine as mov does not modify any flags.
                    Inst::Store { .. } => continue,
                    // Other instructions may modify flags, so we must materialize.
                    _ => break,
                }
            }
            if !materialize {
                let inst = self.l.method.inst(cond_ref).clone();
                let nm = self.l.nm_args.entry(cond_ref).or_default().clone();
                self.l.nm_terms.insert(block_ref, (inst, nm));
            }
        }
    }
}
