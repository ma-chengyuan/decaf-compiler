use std::collections::HashSet;

use crate::inter::ir::{Inst, InstRef, Method};

enum Values {
    Zero,
    One(InstRef),
    Many,
}

fn update_values(old: Values, new: &InstRef) -> Values {
    match old {
        Values::Zero => Values::One(*new),
        Values::One(prev) if prev == *new => Values::One(prev),
        _ => Values::Many,
    }
}

pub fn propagate_copies(method: &mut Method) {
    let dom = crate::opt::dom::compute_dominance(method);
    let mut orig = method.iter_insts().map(|(i, _)| i).collect::<Vec<_>>();

    let mut another_iteration = true;
    while another_iteration {
        another_iteration = false;
        // For SSA, all non-phi uses of a variable must be dominated by the definition.
        // Therefore, iterating in preorder of the dominator tree is sufficient.
        for block in dom.preorder(method.entry) {
            let mut removed = HashSet::new();
            for inst in method.block(block).insts.clone() {
                match method.inst_mut(inst) {
                    Inst::Copy(src) => {
                        orig[inst.0] = orig[src.0];
                        removed.insert(inst);
                    }
                    Inst::Phi(map) => {
                        if let Values::One(src) = map.values().fold(Values::Zero, update_values) {
                            orig[inst.0] = orig[src.0];
                            removed.insert(inst);
                        }
                    }
                    inst => inst.for_each_inst_ref(|inst_ref| *inst_ref = orig[inst_ref.0]),
                }
            }
            let block = method.block_mut(block);
            block.insts.retain(|inst| !removed.contains(inst));
            let term = &mut block.term;
            term.for_each_inst_ref(|inst_ref| *inst_ref = orig[inst_ref.0]);
        }
        for block in method.iter_block_refs() {
            for inst in method.block(block).insts.clone() {
                let Inst::Phi(map) = method.inst_mut(inst) else {
                    break; // All phis are at the beginning of the block, so break at first non-phi.
                };
                let mut vals = Values::Zero;
                for val in map.values_mut() {
                    *val = orig[val.0];
                    vals = update_values(vals, val);
                }
                if let Values::One(_) = vals {
                    // All values are the same, the phi is essentially a copy.
                    // Better run another iteration to remove the phi.
                    another_iteration = true;
                }
            }
        }
    }
    method.remove_unreachable()
}
