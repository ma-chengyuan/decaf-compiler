//! Utilities for loop analysis

#![allow(dead_code)]

use std::{collections::HashSet, rc::Rc};

use crate::inter::ir::{BlockRef, Method};

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

    pub parent: Option<Rc<Loop>>,
}

impl Loop {
    pub fn depth(&self) -> usize {
        match &self.parent {
            Some(parent) => parent.depth() + 1,
            None => 0,
        }
    }
}

#[derive(Debug, Clone)]
pub struct LoopAnalysis {
    loops: Vec<Option<Rc<Loop>>>, // Map from BlockRef to Loop
}

impl LoopAnalysis {
    pub fn new(method: &Method) -> Self {
        let mut ret = Self {
            loops: vec![None; method.n_blocks()],
        };
        ret.analyze(
            method,
            &compute_dominance(method),
            &predecessors(method),
            &reverse_postorder(method),
            None,
        );
        ret
    }

    fn analyze(
        &mut self,
        method: &Method,
        dom: &Dominance,
        predecessors: &[HashSet<BlockRef>],
        rev_postorder: &[BlockRef], // Blocks in reverse postorder
        parent: Option<Rc<Loop>>,
    ) {
        let mut visited = HashSet::new();
        for block_ref in rev_postorder.iter().cloned() {
            self.loops[block_ref.0] = parent.clone();
            if !visited.insert(block_ref) {
                continue;
            }
            let mut body: Option<HashSet<BlockRef>> = None;
            for pred in predecessors[block_ref.0].iter() {
                if dom.dominates(block_ref, *pred) {
                    let mut this_body = HashSet::new();
                    this_body.insert(block_ref);
                    let mut stack = Vec::new();
                    stack.push(*pred);
                    while let Some(block) = stack.pop() {
                        if this_body.insert(block) {
                            stack.extend(predecessors[block.0].iter().cloned());
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
                let loop_ = Rc::new(Loop {
                    header,
                    body,
                    continue_,
                    break_,
                    parent: parent.clone(),
                });
                self.analyze(method, dom, predecessors, &rev_postorder, Some(loop_));
            }
        }
    }

    pub fn get_loop(&self, block_ref: BlockRef) -> Option<Rc<Loop>> {
        self.loops[block_ref.0].clone()
    }

    pub fn get_freq(&self, block_ref: BlockRef) -> usize {
        self.get_loop(block_ref)
            .map(|l| 10usize.pow(l.depth().max(8) as u32))
            .unwrap_or(1)
    }
}
