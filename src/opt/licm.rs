//! Loop invariant code motion

use std::collections::HashSet;

use crate::inter::ir::{Address, BlockRef, Inst, InstRef, Method};

use super::{copy_prop::propagate_copies, loop_utils::LoopAnalysis};

pub fn loop_invariant_code_motion(method: &mut Method) {
    let mut loops = LoopAnalysis::new(method);

    let mut headers = method
        .iter_block_refs()
        .filter(|b| loops.is_header(*b))
        .map(|b| (b, loops.get_loop(b).unwrap().clone()))
        .collect::<Vec<_>>();
    if headers.is_empty() {
        return;
    }
    // Start with larger loops, and then smaller.
    // If we start with deeply nested loops, then a computation may be moved multiple times.
    headers.sort_by_cached_key(|(_, l)| l.borrow().depth());

    let mut inst_to_block = vec![BlockRef(0); method.n_insts()];
    for (block_ref, block) in method.iter_blocks() {
        for inst_ref in block.insts.iter() {
            inst_to_block[inst_ref.0] = block_ref;
        }
    }

    for (header_ref, loop_) in headers {
        let mut to_move: Vec<InstRef> = vec![];
        let body = &loop_.borrow().body;

        let mut has_calls = false;
        let mut tainted: HashSet<Address> = HashSet::new();
        for block_ref in body.iter() {
            for inst_ref in method.block(*block_ref).insts.iter().copied() {
                let inst = method.inst(inst_ref);
                match inst {
                    Inst::Call { .. } => has_calls = true,
                    Inst::Store { addr, .. } | Inst::StoreArray { addr, .. } => {
                        tainted.insert(addr.clone());
                    }
                    Inst::Initialize { stack_slot, .. } => {
                        tainted.insert(Address::Local(*stack_slot));
                    }
                    _ => {}
                };
            }
        }

        for block_ref in body.iter() {
            // TODO: Not every block is worth checking. If a block is in a rare
            // branch within the loop, hoisting instructions from it may not be
            // beneficial.
            for inst_ref in method.block(*block_ref).insts.clone() {
                let inst = method.inst(inst_ref);
                if inst.has_side_effects() {
                    // Do not move instructions with side effects.
                    continue;
                }
                match inst {
                    // Do not move phi instructions.
                    Inst::Phi(_) => continue,
                    // Do not move copy instructions. They are cheap.
                    Inst::Copy(_) => continue,
                    Inst::Load(addr) | Inst::LoadArray { addr, .. } => {
                        if matches!(addr, Address::Global(_)) && has_calls {
                            // Do not move global loads if there are calls in the loop.
                            // Calls may change the value of the global.
                            continue;
                        }
                        if tainted.contains(addr) {
                            // Do not move loads from tainted addresses.
                            continue;
                        }
                    }
                    _ => {}
                };
                let mut invariant = true;
                method.inst_mut(inst_ref).for_each_inst_ref(|arg_ref| {
                    let arg_block_ref = inst_to_block[arg_ref.0];
                    if body.contains(&arg_block_ref) {
                        invariant = false;
                    }
                });
                if invariant {
                    to_move.push(inst_ref);
                }
            }
        }
        if to_move.is_empty() {
            continue;
        }
        let pre_header_ref = loops.get_or_insert_pre_header(method, header_ref);
        if method.n_insts() > inst_to_block.len() {
            // Adding preheader may introduce new phi instructions. Add them to the list.
            // This step is actually not necessary, but it is a good practice.
            inst_to_block.resize(method.n_insts(), pre_header_ref);
        }
        for inst_ref in to_move {
            let moved_inst_ref = method.next_inst(pre_header_ref, method.inst(inst_ref).clone());
            *method.inst_mut(inst_ref) = Inst::Copy(moved_inst_ref);
        }
    }

    // Propagate copies to remove redundant copies.
    propagate_copies(method);
}
