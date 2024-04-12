use crate::inter::ir::{Inst, InstRef, Method};

/// Eliminates dead code from a method.
///
/// Assumes that the method is in SSA form, and all unreachable blocks and
/// instructions has been removed by `remove_unreachable`.
pub fn eliminate_dead_code(method: &mut Method) {
    let mut useful = vec![false; method.n_insts()];

    for block_ref in method.iter_block_refs() {
        method.block_mut(block_ref).term.for_each_inst_ref(|inst| {
            // Mark all instructions in the terminator as useful, since they are reachable.
            useful[inst.0] = true;
        });
    }

    for (inst_ref, inst) in method.iter_insts() {
        if let Inst::Call { .. }
        | Inst::Store { .. }
        | Inst::StoreArray { .. }
        | Inst::Initialize { .. } = inst
        {
            // These instructions have side effects and must not be removed.
            useful[inst_ref.0] = true;
        }
    }

    let mut worklist = (0..method.n_insts())
        .filter(|i| useful[*i])
        .map(InstRef)
        .collect::<Vec<_>>();
    while let Some(inst_ref) = worklist.pop() {
        let inst = method.inst_mut(inst_ref);
        inst.for_each_inst_ref(|inst_ref| {
            if !useful[inst_ref.0] {
                useful[inst_ref.0] = true;
                worklist.push(*inst_ref);
            }
        });
    }

    for block_ref in method.iter_block_refs() {
        method
            .block_mut(block_ref)
            .insts
            .retain(|inst_ref| useful[inst_ref.0]);
    }

    method.remove_unreachable() // Actually removes unreachable dead instructions.
}
