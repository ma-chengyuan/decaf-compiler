//! Utilities for loop analysis

#![allow(dead_code)]

use std::{cell::RefCell, collections::HashSet, rc::Rc};

use crate::inter::ir::{BlockRef, Inst, Method, Terminator};

use super::{
    dom::{compute_dominance, Dominance},
    for_each_successor, predecessors, reverse_postorder,
};

#[derive(Debug, Clone)]
pub struct Loop {
    pub header: BlockRef,
    pub body: HashSet<BlockRef>,
    pub continue_: HashSet<BlockRef>, // Back edges
    pub break_: HashSet<BlockRef>,    // Exit edges

    pub parent: Option<Rc<RefCell<Loop>>>,
}

impl Loop {
    pub fn depth(&self) -> usize {
        match &self.parent {
            Some(parent) => parent.borrow().depth() + 1,
            None => 0,
        }
    }
}

// Does not hold a reference to the method to avoid borrowing issues.
#[derive(Debug, Clone)]
pub struct LoopAnalysis {
    loops: Vec<Option<Rc<RefCell<Loop>>>>, // Map from BlockRef to Loop
    predecessors: Vec<HashSet<BlockRef>>,
}

impl LoopAnalysis {
    pub fn new(method: &Method) -> Self {
        let mut ret = Self {
            loops: vec![None; method.n_blocks()],
            predecessors: predecessors(method),
        };
        ret.analyze(
            method,
            &compute_dominance(method),
            &reverse_postorder(method),
            None,
        );
        ret
    }

    fn analyze(
        &mut self,
        method: &Method,
        dom: &Dominance,
        rev_postorder: &[BlockRef], // Blocks in reverse postorder
        parent: Option<Rc<RefCell<Loop>>>,
    ) {
        let mut visited = HashSet::new();
        for block_ref in rev_postorder.iter().cloned() {
            if !visited.insert(block_ref) {
                continue;
            }
            self.loops[block_ref.0] = parent.clone();
            let mut body: Option<HashSet<BlockRef>> = None;
            for pred in self.predecessors[block_ref.0].iter() {
                if dom.dominates(block_ref, *pred) {
                    let mut this_body = HashSet::new();
                    this_body.insert(block_ref);
                    let mut stack = Vec::new();
                    stack.push(*pred);
                    while let Some(block) = stack.pop() {
                        if this_body.insert(block) {
                            stack.extend(self.predecessors[block.0].iter().cloned());
                        }
                    }
                    body = Some(match body {
                        Some(mut loop_blocks) => {
                            loop_blocks.extend(this_body);
                            loop_blocks
                        }
                        None => this_body,
                    });
                }
            }
            if let Some(body) = body {
                visited.extend(&body);
                let header = block_ref;
                let mut continue_ = HashSet::new();
                let mut break_ = HashSet::new();
                for block_ref in &body {
                    for_each_successor(method, *block_ref, |succ| {
                        if succ == header {
                            continue_.insert(*block_ref);
                        }
                        if !body.contains(&succ) {
                            break_.insert(*block_ref);
                        }
                    })
                }
                let rev_postorder = rev_postorder
                    .iter()
                    .cloned()
                    .filter(|block_ref| body.contains(block_ref) && block_ref != &header)
                    .collect::<Vec<_>>();
                let loop_ = Rc::new(RefCell::new(Loop {
                    header,
                    body,
                    continue_,
                    break_,
                    parent: parent.clone(),
                }));
                self.loops[header.0] = Some(loop_.clone());
                self.analyze(method, dom, &rev_postorder, Some(loop_));
            }
        }
    }

    pub fn get_loop(&self, block_ref: BlockRef) -> Option<Rc<RefCell<Loop>>> {
        self.loops[block_ref.0].clone()
    }

    pub fn get_freq(&self, block_ref: BlockRef) -> usize {
        self.get_loop(block_ref)
            .map(|l| 10usize.pow(l.borrow().depth().min(8) as u32))
            .unwrap_or(1)
    }

    pub fn is_header(&self, block_ref: BlockRef) -> bool {
        self.get_loop(block_ref)
            .map(|l| l.borrow().header == block_ref)
            .unwrap_or(false)
    }

    /// Get the preheader of a header block, panics if the block is not a header.
    /// Sometimes a new block is created as the preheader. In this case self is
    /// updated to reflect the new block.
    pub fn get_or_insert_pre_header(
        &mut self,
        method: &mut Method,
        block_ref: BlockRef,
    ) -> BlockRef {
        debug_assert!(self.is_header(block_ref));
        let loop_ = self.get_loop(block_ref).unwrap();
        let loop_body = &loop_.borrow().body;
        let external_preds = self.predecessors[block_ref.0]
            .iter()
            .filter(|pred| !loop_body.contains(pred))
            .copied()
            .collect::<Vec<_>>();
        if external_preds.len() == 1 {
            let pred = external_preds[0];
            let mut other_successors = false;
            for_each_successor(method, pred, |succ| {
                if succ != block_ref {
                    other_successors = true;
                }
            });
            if !other_successors {
                // If we have a single external predecessor, and that
                // predecessor has the header block as the only successor we can
                // use it as the preheader.
                return pred;
            }
        }
        let preheader_ref = method.next_block();
        method.block_mut(preheader_ref).term = Terminator::Jump(block_ref);
        for pred in external_preds.iter() {
            method.block_mut(*pred).term.for_each_block_ref(|succ| {
                if *succ == block_ref {
                    *succ = preheader_ref;
                }
            });
        }
        self.predecessors[block_ref.0].retain(|pred| loop_body.contains(pred));
        self.predecessors[block_ref.0].insert(preheader_ref);
        self.predecessors
            .push(external_preds.iter().copied().collect());
        if external_preds.len() > 1 {
            for phi_ref in method.phis(block_ref) {
                let Inst::Phi(map) = method.inst(phi_ref) else {
                    unreachable!();
                };
                let new_phi = method.next_inst(
                    preheader_ref,
                    Inst::Phi(
                        map.iter()
                            .filter(|(src, _)| !loop_body.contains(src))
                            .map(|(src, dst)| (*src, *dst))
                            .collect(),
                    ),
                );
                let Inst::Phi(map) = method.inst_mut(phi_ref) else {
                    unreachable!();
                };
                map.retain(|src, _| loop_body.contains(src));
                map.insert(preheader_ref, new_phi);
            }
        }
        if let Some(parent) = &loop_.borrow().parent {
            parent.borrow_mut().body.insert(preheader_ref);
            self.loops.push(Some(parent.clone()));
        } else {
            self.loops.push(None);
        }
        preheader_ref
    }
}
