//! Data structure for Belady's spill heuristics

#![allow(dead_code)]
use std::{collections::VecDeque, fmt};

use im::HashMap;

use crate::{
    inter::ir::{BlockRef, Inst, InstRef},
    opt::for_each_successor,
};

use super::{ProgPt, Spiller};

/// A map from instruction references to distance to their last use.
///
/// This data structure differs from the ordinary `HashMap<InstRef, isize>` in
/// two ways:
///
/// - It supports O(1) cloning.
/// - It supports O(1) increment of all distances by one.
///
/// Both are tailored to how the spill heuristics is computed. The cost,
/// however, is that lookups are O(log n).
#[derive(Debug, Clone, Default)]
pub struct BeladyMap {
    base: HashMap<InstRef, isize>,
    offset: isize,
}

impl BeladyMap {
    /// Gets the distance to the last use of an instruction, or `None` if the
    /// the value is not live.
    pub fn get(&self, inst: &InstRef) -> isize {
        self.base
            .get(inst)
            .map(|v| *v + self.offset)
            .unwrap_or(isize::MAX)
    }

    /// Returns if an instruction is live.
    pub fn is_live(&self, inst: &InstRef) -> bool {
        self.base.get(inst).is_some()
    }

    /// Sets the distance to the last use of an instruction.
    pub fn insert(&mut self, inst: InstRef, distance: isize) {
        self.base.insert(inst, distance - self.offset);
    }

    /// Remove an instruction from the map.
    pub fn remove(&mut self, inst: &InstRef) {
        self.base.remove(inst);
    }

    /// Get the number of entries in the map.
    pub fn len(&self) -> usize {
        self.base.len()
    }

    /// Step one step back.
    pub fn increment_all(&mut self) {
        self.offset += 1;
    }

    /// Returns an iterator over the map.
    pub fn iter(&self) -> Iter {
        Iter {
            base: self.base.iter(),
            offset: self.offset,
        }
    }

    /// Merge another map into this one, keeping the minimum distance.
    pub fn merge_min(&mut self, other: &Self) {
        for (inst, distance) in other.iter() {
            let distance_adjusted = distance - self.offset;
            self.base
                .entry(inst)
                .and_modify(|d| *d = (*d).min(distance_adjusted))
                .or_insert(distance_adjusted);
        }
    }

    /// Convert the map to a sorted vector.
    fn to_sorted_vec(&self) -> Vec<(InstRef, isize)> {
        let mut keys = self.iter().collect::<Vec<_>>();
        keys.sort_by_key(|(k, _)| k.0);
        keys
    }
}

pub struct Iter<'a> {
    base: im::hashmap::Iter<'a, InstRef, isize>,
    offset: isize,
}

impl<'a> Iterator for Iter<'a> {
    type Item = (InstRef, isize);

    fn next(&mut self) -> Option<Self::Item> {
        self.base.next().map(|(k, v)| (*k, *v + self.offset))
    }
}

impl PartialEq for BeladyMap {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            false // A fast path.
        } else {
            self.to_sorted_vec() == other.to_sorted_vec()
        }
    }
}

impl fmt::Display for BeladyMap {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{{")?;
        for (i, (k, v)) in self.to_sorted_vec().into_iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}: {}", k, v)?;
        }
        write!(f, "}}")
    }
}

impl Spiller<'_> {
    /// Evaluate the spill heuristic at each program point & do liveness
    /// analysis.
    pub(super) fn eval_spill_heuristic(&mut self) {
        // Use dominate tree post order to reduce the number of iterations
        // needed for convergence.
        let postorder = self.dom.postorder(self.method.entry);
        let mut q = VecDeque::new();
        let mut in_queue = vec![false; self.method.n_blocks()];
        for block in postorder {
            q.push_back(block);
            in_queue[block.0] = true;
        }
        while let Some(block) = q.pop_front() {
            in_queue[block.0] = false;
            if self.eval_spill_heuristic_for_block(block) {
                for &p in self.predecessors[block.0].iter() {
                    if !in_queue[p.0] {
                        q.push_back(p);
                        in_queue[p.0] = true;
                    }
                }
            }
        }
    }

    /// Updates the spill heuristic map at a program point. Returns if the map
    /// has changed.
    fn update_spill_heuristic(&mut self, prog_pt: ProgPt, h: &BeladyMap) -> bool {
        let mut changed = false;
        self.spill_heuristic
            .entry(prog_pt)
            .and_modify(|h_cur| {
                if *h_cur != *h {
                    changed = true;
                    *h_cur = h.clone();
                }
            })
            .or_insert_with(|| {
                changed = true;
                h.clone()
            });
        changed
    }

    /// Evaluate the spill heuristic for a block.
    fn eval_spill_heuristic_for_block(&mut self, block_ref: BlockRef) -> bool {
        let mut h = BeladyMap::default();
        // Compute spill heuristic backwards.
        // h is the union (min-merge) of the spill heuristic of all successors.
        for_each_successor(&self.method, block_ref, |succ| {
            let first_pt = self.method.first_prog_pt(succ);
            if let Some(h_successor) = self.spill_heuristic.get(&first_pt) {
                h.merge_min(h_successor);
            }
            for inst_ref in self.method.block(succ).insts.iter() {
                match self.method.inst(*inst_ref) {
                    Inst::Phi(map) => {
                        h.remove(inst_ref);
                        // Phi function at the successor block means that the
                        // value is immediately used
                        h.insert(map[&block_ref], 0);
                    }
                    Inst::PhiMem { .. } => continue,
                    _ => break,
                }
            }
        });
        h.increment_all(); // Increase distance by one. One for the edge.
        if !self.update_spill_heuristic(ProgPt::AfterTerm(block_ref), &h) {
            return false;
        }
        // Update value use in terminator.
        self.method
            .block_mut(block_ref)
            .term
            .for_each_inst_ref(|inst_ref| h.insert(*inst_ref, 0));
        if !self.update_spill_heuristic(ProgPt::BeforeTerm(block_ref), &h) {
            return false;
        }
        h.increment_all(); // Increase distance by one. One for the terminator instruction.
        let block = self.method.block(block_ref);
        // Go through the instructions in reverse order.
        for inst_ref in block.insts.clone().into_iter().rev() {
            match self.method.inst_mut(inst_ref) {
                Inst::Phi(_) | Inst::PhiMem { .. } => break, // Phi instructions are handled above.
                inst => {
                    // inst_ref has just been defined, so it's not live above.
                    h.remove(&inst_ref);
                    // Update value use in the instruction.
                    inst.for_each_inst_ref(|inst_ref| h.insert(*inst_ref, 0));
                    if !self.update_spill_heuristic(ProgPt::BeforeInst(inst_ref), &h) {
                        return false;
                    }
                    h.increment_all(); // Increase distance by one. One for the instruction.
                }
            }
        }
        true
    }
}
