//! Redundant global / array access elimination

#![allow(dead_code)]
use std::{
    collections::{HashSet, VecDeque},
    rc::Rc,
};

use im::HashMap;

use crate::inter::{
    constant::Const,
    ir::{Address, BlockRef, Inst, InstRef, Method, StackSlotRef},
};

use super::{
    copy_prop::propagate_copies,
    dom::{compute_dominance, Dominance},
    for_each_successor, predecessors, reverse_postorder,
};

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct AvailArrayElems {
    consts: HashMap<i64, InstRef>,
    vars: HashMap<InstRef, InstRef>,
}

impl AvailArrayElems {
    fn merge(&mut self, another: &Self) {
        self.consts.retain(|k, v| another.consts.get(k) == Some(v));
        self.vars
            .retain(|k, v| another.vars.get(k).copied() == Some(*v));
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct AvailGlobalAndArrays {
    global_scalars: HashMap<Rc<str>, InstRef>,
    global_arrays: HashMap<Rc<str>, AvailArrayElems>,
    local_arrays: HashMap<StackSlotRef, AvailArrayElems>,
}

impl AvailGlobalAndArrays {
    fn merge(&mut self, another: &Self) {
        self.global_scalars
            .retain(|k, v| another.global_scalars.get(k) == Some(v));
        self.global_arrays
            .retain(|k, _| another.global_arrays.contains_key(k));
        for (k, v) in self.global_arrays.iter_mut() {
            v.merge(&another.global_arrays[k]);
        }
        self.local_arrays
            .retain(|k, _| another.local_arrays.contains_key(k));
        for (k, v) in self.local_arrays.iter_mut() {
            v.merge(&another.local_arrays[k]);
        }
    }
}

struct Analyzer<'a> {
    method: &'a mut Method,
    predecessors: Vec<HashSet<BlockRef>>,
    avail_in: Vec<AvailGlobalAndArrays>,
    avail_out: Vec<AvailGlobalAndArrays>,
    dom: Dominance,
}

impl<'a> Analyzer<'a> {
    fn update_all_blocks(&mut self) {
        let mut q = VecDeque::new();
        let mut in_queue = vec![false; self.method.n_blocks()];
        for block in reverse_postorder(self.method) {
            q.push_back(block);
            in_queue[block.0] = true;
            self.update_avail_block(block, true);
        }
        while let Some(block) = q.pop_front() {
            in_queue[block.0] = false;
            if self.update_avail_block(block, false) {
                for_each_successor(self.method, block, |succ| {
                    if !in_queue[succ.0] {
                        q.push_back(succ);
                        in_queue[succ.0] = true;
                    }
                })
            }
        }
    }

    fn update_avail_inst(&self, inst_ref: InstRef, avail: &mut AvailGlobalAndArrays) {
        match self.method.inst(inst_ref) {
            Inst::Store {
                addr: Address::Global(global),
                value,
            } => {
                avail.global_scalars.insert(global.clone(), *value);
            }
            Inst::Load(Address::Global(global)) => {
                avail
                    .global_scalars
                    .entry(global.clone())
                    .or_insert(inst_ref);
            }
            Inst::Call { .. } => {
                // Be conservative and assume that all global variables are clobbered by a call.
                avail.global_scalars.clear();
                avail.global_arrays.clear();
            }
            Inst::LoadArray { addr, index } => {
                let a = match addr {
                    Address::Global(global) => {
                        avail.global_arrays.entry(global.clone()).or_default()
                    }
                    Address::Local(slot) => avail.local_arrays.entry(*slot).or_default(),
                };
                match self.method.inst(*index) {
                    Inst::LoadConst(Const::Int(i)) => {
                        a.consts.entry(*i).or_insert(inst_ref);
                    }
                    _ => {
                        a.vars.entry(*index).or_insert(inst_ref);
                    }
                }
            }
            Inst::StoreArray { addr, index, value } => {
                let a = match addr {
                    Address::Global(global) => {
                        avail.global_arrays.entry(global.clone()).or_default()
                    }
                    Address::Local(slot) => avail.local_arrays.entry(*slot).or_default(),
                };
                match self.method.inst(*index) {
                    Inst::LoadConst(Const::Int(i)) => {
                        a.consts.insert(*i, *value);
                        a.vars.clear(); // Clear all variables since they may alias with the constant index.
                    }
                    _ => {
                        a.consts.clear(); // Clear all constants since they may alias with the variable index.
                        a.vars.clear(); // Clear all variables since they may alias with the variable index.
                        a.vars.insert(*index, *value);
                    }
                }
            }
            _ => {}
        }
    }

    fn update_avail_block(&mut self, block_ref: BlockRef, warmup: bool) -> bool {
        let mut avail = None;
        for pred in self.predecessors[block_ref.0].iter().copied() {
            if warmup && self.dom.dominates(block_ref, pred) {
                // Ignore back edges during warmup.
                continue;
            }
            let pred_avail = &self.avail_out[pred.0];
            avail = match avail {
                None => Some(pred_avail.clone()),
                Some(mut avail) => {
                    avail.merge(pred_avail);
                    Some(avail)
                }
            };
        }
        let mut avail = avail.unwrap_or_default();
        self.avail_in[block_ref.0] = avail.clone();
        for inst_ref in self.method.block(block_ref).insts.iter().copied() {
            self.update_avail_inst(inst_ref, &mut avail);
        }
        if avail == self.avail_out[block_ref.0] {
            return false;
        }
        self.avail_out[block_ref.0] = avail;
        true
    }

    fn eliminate_all_blocks(&mut self) {
        for block_ref in self.method.iter_block_refs() {
            self.eliminate_block(block_ref);
        }
    }

    fn eliminate_block(&mut self, block_ref: BlockRef) {
        let mut avail = self.avail_in[block_ref.0].clone();

        for inst_ref in self.method.block(block_ref).insts.clone() {
            let inst = self.method.inst_mut(inst_ref);
            match inst {
                Inst::Load(Address::Global(global)) => {
                    if let Some(&value) = avail.global_scalars.get(global) {
                        *inst = Inst::Copy(value);
                        continue;
                    }
                }
                Inst::LoadArray { addr, index } => {
                    let a = match addr {
                        Address::Global(global) => avail.global_arrays.get_mut(global),
                        Address::Local(slot) => avail.local_arrays.get_mut(slot),
                    };
                    if let Some(a) = a {
                        let index = *index;
                        match self.method.inst(index) {
                            Inst::LoadConst(Const::Int(i)) => {
                                if let Some(&value) = a.consts.get(i) {
                                    *self.method.inst_mut(inst_ref) = Inst::Copy(value);
                                    continue;
                                }
                            }
                            _ => {
                                if let Some(&value) = a.vars.get(&index) {
                                    *self.method.inst_mut(inst_ref) = Inst::Copy(value);
                                    continue;
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
            self.update_avail_inst(inst_ref, &mut avail);
        }
    }
}

pub fn eliminate_redundant_global_and_array_access(method: &mut Method) {
    let mut analyzer = Analyzer {
        predecessors: predecessors(method),
        dom: compute_dominance(method),
        avail_in: vec![AvailGlobalAndArrays::default(); method.n_blocks()],
        avail_out: vec![AvailGlobalAndArrays::default(); method.n_blocks()],
        method,
    };
    analyzer.update_all_blocks();
    analyzer.eliminate_all_blocks();
    propagate_copies(method);
}
