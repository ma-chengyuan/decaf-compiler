#![allow(dead_code)]
use std::collections::{HashMap, HashSet};

use crate::{
    inter::{
        ir::{Address, BlockRef, Inst, InstRef, Method, Program, StackSlotRef, Terminator},
        types::Type,
    },
    opt::{dom::compute_dominance, for_each_successor},
    utils::make_internal_ident,
};

use super::predecessors;

struct ScalarLiveness {
    in_: Vec<HashSet<StackSlotRef>>,
    out: Vec<HashSet<StackSlotRef>>,
}

fn analyze_liveness(method: &Method) -> ScalarLiveness {
    // out[b]: the set of stack slots that are live at the end of block b.
    let mut out: Vec<HashSet<StackSlotRef>> = vec![HashSet::new(); method.n_blocks()];
    // in[b]: the set of stack slots that are live at the beginning of block b.
    let mut in_: Vec<HashSet<StackSlotRef>> = vec![HashSet::new(); method.n_blocks()];
    let rev_postorder = crate::opt::reverse_postorder(method);
    let mut changed = true;
    while changed {
        changed = false;
        for block in rev_postorder.iter().rev() {
            let mut new_out: HashSet<StackSlotRef> = HashSet::new();
            for_each_successor(method, *block, |succ| new_out.extend(in_[succ.0].iter()));
            if new_out != out[block.0] {
                changed = true;
                out[block.0] = new_out.clone();
            }
            let mut new_in = new_out;
            for inst in method.block(*block).insts.iter().rev() {
                match method.inst(*inst) {
                    Inst::Load(Address::Local(target)) => {
                        new_in.insert(*target);
                    }
                    Inst::Store {
                        addr: Address::Local(target),
                        ..
                    }
                    | Inst::Initialize {
                        stack_slot: target, ..
                    } => {
                        new_in.remove(target);
                    }
                    _ => {}
                }
            }
            if new_in != in_[block.0] {
                changed = true;
                in_[block.0] = new_in;
            }
        }
    }
    ScalarLiveness { in_, out }
}

impl ScalarLiveness {
    fn is_live_in(&self, block: BlockRef, slot: StackSlotRef) -> bool {
        self.in_[block.0].contains(&slot)
    }

    fn is_live_out(&self, block: BlockRef, slot: StackSlotRef) -> bool {
        self.out[block.0].contains(&slot)
    }
}

/// Convert a method into SSA form.
///
/// Finds all scalar stack slots, treat them as variables, and apply the SSA
/// construction algorithm by Cytron et al. to convert them into SSA form.
pub fn construct_ssa(method: &Method) -> Method {
    // Step 0: liveness analysis -- no need to insert phis for a variable if it is
    // not going to be used down the line.
    let live = analyze_liveness(method);

    let dom = compute_dominance(method);
    let mut phis: Vec<HashMap<StackSlotRef, InstRef>> = vec![HashMap::new(); method.n_blocks()];
    let mut new_method = method.clone();
    // [slot_ref] = true if the slot should be lifted into SSA form.
    let mut lifting = vec![false; method.n_stack_slots()];

    // Step 1: Insert phi functions
    for (slot_ref, slot) in method.iter_slack_slots() {
        if !matches!(slot.ty, Type::Primitive(_)) {
            // Only lift primitive types into SSA form because only they fit
            // into hardware registers.
            continue;
        }

        lifting[slot_ref.0] = true;
        // Phis will need to be inserted at the dominance frontier closures of
        // the blocks that contain stores
        let mut blocks_with_store = method
            .iter_blocks()
            .filter_map(|(block_ref, block)| {
                let store = block.insts.iter().find(|inst| {
                    matches!(method.inst(**inst), Inst::Store {
                        addr: Address::Local(target),
                        ..
                    }
                    | Inst::Initialize { // Initialize is a store too!
                        stack_slot: target, ..
                    } if *target == slot_ref)
                });
                store.map(|_| block_ref)
            })
            .collect::<Vec<_>>();
        if slot_ref.0 < method.params.len() && !blocks_with_store.contains(&method.entry) {
            // Stack slots that are function parameters are always live
            blocks_with_store.push(method.entry);
        }
        let mut worklist = blocks_with_store.clone();
        let mut visited = blocks_with_store.iter().cloned().collect::<HashSet<_>>();
        while let Some(block) = worklist.pop() {
            for frontier in dom.dominance_frontier(block) {
                if live.is_live_in(*frontier, slot_ref) {
                    phis[frontier.0].entry(slot_ref).or_insert_with(|| {
                        let phi =
                            new_method.next_inst_prepend(*frontier, Inst::Phi(HashMap::new()));
                        let annotation = new_method.annotate_inst_mut(phi);
                        annotation.ident = Some(slot.name.clone());
                        // annotation.span = Some(slot.name.span.clone());
                        phi
                    });
                }
                if !visited.contains(frontier) {
                    visited.insert(*frontier);
                    worklist.push(*frontier);
                }
            }
        }
    }

    // Step 2: rename variables
    let mut visited = vec![false; method.n_blocks()];
    let mut initial_arg_loads = HashSet::new();

    fn lookup_value(
        var: StackSlotRef,
        stack: &[HashMap<StackSlotRef, (BlockRef, InstRef)>],
    ) -> (BlockRef, InstRef) {
        for map in stack.iter().rev() {
            if let Some((block, inst)) = map.get(&var) {
                return (*block, *inst);
            }
        }
        unreachable!("variable {} not found in stack", var);
    }

    fn rename_variables(
        method: &mut Method,
        block: BlockRef,
        visited: &mut [bool], // visited[block.0] = true if block has been visited
        phis: &[HashMap<StackSlotRef, InstRef>], // phis[block.0] = map from stack slot to phi at block
        current_values: &mut Vec<HashMap<StackSlotRef, (BlockRef, InstRef)>>,
        initial_arg_loads: &HashSet<InstRef>,
        lifting: &[bool],
    ) {
        for (var, phi) in phis[block.0].iter() {
            let (current_value_block, current_value_inst) = lookup_value(*var, current_values);
            let Inst::Phi(map) = method.inst_mut(*phi) else {
                unreachable!()
            };
            map.insert(current_value_block, current_value_inst);
            current_values
                .last_mut()
                .unwrap()
                .insert(*var, (block, *phi));
        }
        if visited[block.0] {
            return;
        }
        visited[block.0] = true;

        let mut removed = HashSet::new();
        for inst_ref in method.block(block).insts.clone() {
            let inst = method.inst_mut(inst_ref);
            match inst {
                Inst::Load(Address::Local(target))
                    if lifting[target.0] && !initial_arg_loads.contains(&inst_ref) =>
                {
                    let (_, value_inst) = lookup_value(*target, current_values);
                    *inst = Inst::Copy(value_inst);
                }
                Inst::Store {
                    value,
                    addr: Address::Local(target),
                } if lifting[target.0] => {
                    current_values
                        .last_mut()
                        .unwrap()
                        .insert(*target, (block, *value));
                    removed.insert(inst_ref);
                }
                Inst::Initialize { stack_slot, value } if lifting[stack_slot.0] => {
                    let stack_slot = *stack_slot;
                    current_values
                        .last_mut()
                        .unwrap()
                        .insert(stack_slot, (block, inst_ref));
                    *inst = Inst::LoadConst(value.clone());
                    method.annotate_inst_mut(inst_ref).ident =
                        Some(method.stack_slot(stack_slot).name.clone());
                }
                _ => {}
            }
        }
        method
            .block_mut(block)
            .insts
            .retain(|inst_ref| !removed.contains(inst_ref));
        match method.block(block).term {
            Terminator::Return(_) => {}
            Terminator::Jump(target) => rename_variables(
                method,
                target,
                visited,
                phis,
                current_values,
                initial_arg_loads,
                lifting,
            ),
            Terminator::CondJump { true_, false_, .. } => {
                current_values.push(HashMap::new());
                rename_variables(
                    method,
                    true_,
                    visited,
                    phis,
                    current_values,
                    initial_arg_loads,
                    lifting,
                );
                let _ = current_values.pop();
                current_values.push(HashMap::new());
                rename_variables(
                    method,
                    false_,
                    visited,
                    phis,
                    current_values,
                    initial_arg_loads,
                    lifting,
                );
                let _ = current_values.pop();
            }
        }
    }

    let mut current_values = vec![HashMap::new()];
    for (stack_slot_ref, slot) in method.iter_slack_slots().take(method.params.len()) {
        let new_inst = new_method
            .next_inst_prepend(new_method.entry, Inst::Load(Address::Local(stack_slot_ref)));
        let annotation = new_method.annotate_inst_mut(new_inst);
        annotation.ident = Some(slot.name.clone());
        // annotation.span = Some(slot.name.span.clone());

        initial_arg_loads.insert(new_inst);
        current_values
            .last_mut()
            .unwrap()
            .insert(stack_slot_ref, (new_method.entry, new_inst));
    }

    rename_variables(
        &mut new_method,
        method.entry,
        &mut visited,
        &phis,
        &mut current_values,
        &initial_arg_loads,
        &lifting,
    );
    new_method.remove_unreachable();
    new_method.remove_unused_stack_slots();
    normalize_phi(&mut new_method);

    // Step 3: "normalize" phi functions
    new_method
}

/// Phi functions inserted by the dominance frontier algorithm as above may not
/// be quite right. Consider the following CFG:
/// ```
/// block_1:
///   %1 <- ...
///   goto block_2 or block_3
/// block_2:
///   ...
///   goto block_5
/// block_3:
///   ...
///   goto block_5
/// block_4:
///   %2 <- ...
///   goto block_5
/// block_5:
///   %3 <- phi { block_1: %1, block_4: %2 } ; <- note this phi function!
/// ````
/// The phi function in block_5 is technically correct, in that value %1 should
/// be used if control flow comes from block_1, but note that there is not a
/// direct edge from block_1 to block_5. Instead block_5 has two incoming edges
/// from block_2 and block_3, both dominated by block_1. It would be more
/// convenient if the phi function is rewritten as:
/// ```
///   %3 <- phi { block_2: %1, block_3: %1, block_4: %2 }
/// ```
/// This is what we mean by "normalizing" phi functions.
fn normalize_phi(method: &mut Method) {
    let dom = compute_dominance(method);
    let predecessors = predecessors(method);
    for block in method.iter_block_refs() {
        for inst in method.block(block).insts.clone() {
            let Inst::Phi(map) = method.inst_mut(inst) else {
                break; // All phis are at the beginning of the block, so break at first non-phi.
            };
            *map = predecessors[block.0]
                .iter()
                .map(|pred| {
                    (
                        *pred,
                        dom.dominators(*pred)
                            .find_map(|d| map.get(&d).cloned())
                            .expect("bad phi: predecessor not dominated by any existing value"),
                    )
                })
                .collect();
        }
    }
}

/// Deconstruct SSA form by removing phi functions and inserting copy
/// instructions.
pub fn destruct_ssa(program: &Program, method: &Method) -> Method {
    let mut phi_to_stack_slot = HashMap::new();
    let mut new_method = method.clone();
    for (inst_ref, inst) in method.iter_insts() {
        if let Inst::Phi(_) = inst {
            let ty = program.infer_inst_type(method, inst_ref);
            let name = method
                .get_inst_annotation(&inst_ref)
                .and_then(|a| a.ident.clone())
                .unwrap_or_else(|| make_internal_ident(&format!("phi {}", inst_ref)));
            let stack_slot = new_method.next_stack_slot(ty, name);
            phi_to_stack_slot.insert(inst_ref, stack_slot);
        }
    }

    let predecessors = predecessors(method);
    for block in method.iter_block_refs() {
        let mut phis: HashMap<BlockRef, Vec<(InstRef, StackSlotRef)>> = HashMap::new();
        for inst_ref in method.block(block).insts.iter() {
            let Inst::Phi(map) = method.inst(*inst_ref) else {
                break;
            };
            let stack_slot = phi_to_stack_slot[&inst_ref];
            for (pred, src) in map.iter() {
                phis.entry(*pred).or_default().push((*src, stack_slot));
            }
            *new_method.inst_mut(*inst_ref) = Inst::Load(Address::Local(stack_slot));
        }

        let n_preds = predecessors[block.0].len();
        for (pred, stores) in phis.iter() {
            let mut successors = HashSet::new();
            for_each_successor(method, *pred, |succ| {
                successors.insert(succ);
            });
            let critical = n_preds >= 2 && successors.len() >= 2;
            let insert_block = if !critical {
                *pred
            } else {
                let edge_block = new_method.next_block();
                new_method.block_mut(*pred).term.for_each_block_ref(|succ| {
                    if *succ == block {
                        *succ = edge_block;
                    }
                });
                new_method.block_mut(edge_block).term = Terminator::Jump(block);
                edge_block
            };
            for (from, to) in stores {
                new_method.next_inst(
                    insert_block,
                    Inst::Store {
                        addr: Address::Local(*to),
                        value: *from,
                    },
                );
            }
        }
    }
    new_method
}
