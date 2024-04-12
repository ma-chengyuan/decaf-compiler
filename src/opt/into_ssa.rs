use std::collections::{HashMap, HashSet};

use crate::{
    inter::{
        ir::{Address, BlockRef, Inst, InstRef, Method, StackSlotRef, Terminator},
        types::Type,
    },
    opt::{dom::compute_dominance, for_each_successor},
};

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

pub fn into_ssa(method: &Method) -> Method {
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
                        new_method.annotate_inst_mut(phi).ident = Some(slot.name.clone());
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

    fn visit_block(
        method: &mut Method,
        block: BlockRef,
        visited: &mut [bool],
        phis: &[HashMap<StackSlotRef, InstRef>],
        current_values: &mut Vec<HashMap<StackSlotRef, (BlockRef, InstRef)>>,
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
                Inst::Load(Address::Local(target)) if lifting[target.0] => {
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
            Terminator::Jump(target) => {
                visit_block(method, target, visited, phis, current_values, lifting)
            }
            Terminator::CondJump { true_, false_, .. } => {
                current_values.push(HashMap::new());
                visit_block(method, true_, visited, phis, current_values, lifting);
                let _ = current_values.pop();
                current_values.push(HashMap::new());
                visit_block(method, false_, visited, phis, current_values, lifting);
                let _ = current_values.pop();
            }
        }
    }

    let mut current_values = vec![HashMap::new()];
    for (stack_slot_ref, slot) in method.iter_slack_slots().take(method.params.len()) {
        let new_inst =
            new_method.next_inst_prepend(new_method.entry, Inst::LoadArg(stack_slot_ref.0));
        new_method.annotate_inst_mut(new_inst).ident = Some(slot.name.clone());
        current_values
            .last_mut()
            .unwrap()
            .insert(stack_slot_ref, (new_method.entry, new_inst));
    }
    visit_block(
        &mut new_method,
        method.entry,
        &mut visited,
        &phis,
        &mut current_values,
        &lifting,
    );
    new_method.remove_unreachable();
    new_method.remove_unused_stack_slots();

    new_method
}
