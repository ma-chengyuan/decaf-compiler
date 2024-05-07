//! Dead store elimination, but for arrays.

use std::collections::{HashMap, VecDeque};

use im::HashSet;

use crate::inter::{
    constant::Const,
    ir::{Address, BlockRef, Inst, InstRef, Method, StackSlotRef},
};

use super::{for_each_successor, predecessors, reverse_postorder};

#[derive(Debug, Clone, PartialEq, Eq, Default)]
enum Liveness {
    // Only these indices are live.
    Indices(HashSet<i64>),
    // All indices are live.
    #[default]
    All,
}

impl Liveness {
    fn merge(&mut self, another: &Self) {
        *self = match (std::mem::take(self), another) {
            (Liveness::All, _) | (_, Liveness::All) => Liveness::All,
            (Liveness::Indices(a), Liveness::Indices(b)) => Liveness::Indices(a.union(b.clone())),
        }
    }
}

struct Analyzer<'a> {
    method: &'a mut Method,
    in_: Vec<HashMap<StackSlotRef, Liveness>>,
    out: Vec<HashMap<StackSlotRef, Liveness>>,
}

impl Analyzer<'_> {
    fn update_liveness_inst(&self, inst_ref: InstRef, live: &mut HashMap<StackSlotRef, Liveness>) {
        match self.method.inst(inst_ref) {
            Inst::LoadArray {
                addr: Address::Local(slot_ref),
                index,
            } => match self.method.inst(*index) {
                Inst::LoadConst(Const::Int(s)) => match live.get_mut(slot_ref) {
                    Some(Liveness::Indices(set)) => {
                        set.insert(*s);
                    }
                    None => {
                        live.insert(*slot_ref, Liveness::Indices(HashSet::unit(*s)));
                    }
                    Some(Liveness::All) => {}
                },
                _ => {
                    live.insert(*slot_ref, Liveness::All);
                }
            },
            Inst::StoreArray {
                addr: Address::Local(slot_ref),
                index,
                ..
            } => {
                if let (Inst::LoadConst(Const::Int(s)), Some(Liveness::Indices(indices))) =
                    (self.method.inst(*index), live.get_mut(slot_ref))
                {
                    indices.remove(s);
                    if indices.is_empty() {
                        live.remove(slot_ref);
                    }
                }
            }
            Inst::Initialize { stack_slot, .. } => {
                live.remove(stack_slot);
            }
            _ => {}
        }
    }

    fn update_liveness_block(&mut self, block_ref: BlockRef) -> bool {
        let mut live: HashMap<StackSlotRef, Liveness> = HashMap::new();
        for_each_successor(self.method, block_ref, |succ| {
            for (slot_ref, liveness) in self.in_[succ.0].iter() {
                live.entry(*slot_ref)
                    .and_modify(|l| l.merge(liveness))
                    .or_insert_with(|| liveness.clone());
            }
        });
        self.out[block_ref.0] = live.clone();
        for inst_ref in self.method.block(block_ref).insts.iter().rev().copied() {
            self.update_liveness_inst(inst_ref, &mut live);
        }
        let changed = self.in_[block_ref.0] != live.clone();
        self.in_[block_ref.0] = live;
        changed
    }

    fn update_liveness(&mut self) {
        let rev_postorder = reverse_postorder(self.method);
        let mut q = VecDeque::new();
        let mut in_queue = vec![false; self.method.n_blocks()];
        let predecessors = predecessors(self.method);
        for block in rev_postorder.iter().rev().copied() {
            q.push_back(block);
            in_queue[block.0] = true;
        }
        while let Some(block) = q.pop_front() {
            in_queue[block.0] = false;
            if self.update_liveness_block(block) {
                for pred in predecessors[block.0].iter().copied() {
                    if !in_queue[pred.0] {
                        q.push_back(pred);
                        in_queue[pred.0] = true;
                    }
                }
            }
        }
    }

    fn eliminate_block(&mut self, block_ref: BlockRef) {
        let mut live = self.out[block_ref.0].clone();
        let mut removed = HashSet::new();
        for inst_ref in self.method.block(block_ref).insts.iter().rev().copied() {
            match self.method.inst(inst_ref) {
                Inst::StoreArray {
                    addr: Address::Local(slot_ref),
                    index,
                    ..
                } => {
                    let remove = match live.get(slot_ref) {
                        None => true,
                        Some(Liveness::All) => false,
                        Some(Liveness::Indices(indices)) => match self.method.inst(*index) {
                            Inst::LoadConst(Const::Int(s)) => !indices.contains(s),
                            _ => false,
                        },
                    };
                    if remove {
                        removed.insert(inst_ref);
                        continue;
                    }
                }
                Inst::Initialize { stack_slot, .. } if live.get(stack_slot).is_none() => {
                    removed.insert(inst_ref);
                    continue;
                }
                _ => {}
            }
            self.update_liveness_inst(inst_ref, &mut live);
        }
        self.method
            .block_mut(block_ref)
            .insts
            .retain(|inst_ref| !removed.contains(inst_ref));
        assert!(live == self.in_[block_ref.0]);
    }

    fn eliminate_all(&mut self) {
        for block_ref in self.method.iter_block_refs() {
            self.eliminate_block(block_ref);
        }
    }
}

pub fn eliminate_dead_array_stores(method: &mut Method) {
    let mut analyzer = Analyzer {
        in_: vec![HashMap::new(); method.n_blocks()],
        out: vec![HashMap::new(); method.n_blocks()],
        method,
    };
    analyzer.update_liveness();
    analyzer.eliminate_all();
    method.remove_unreachable();
    method.remove_unused_stack_slots();
}
