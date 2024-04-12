#![allow(dead_code)]
use std::collections::HashSet;

use crate::{
    inter::ir::{BlockRef, Method},
    opt::{predecessors, reverse_postorder},
};

#[derive(Debug, Clone)]
pub struct Dominance {
    doms: Vec<BlockRef>,
    frontiers: Vec<HashSet<BlockRef>>,
}

impl Dominance {
    pub fn immediate_dominator(&self, block: BlockRef) -> BlockRef {
        self.doms[block.0]
    }

    pub fn dominators(&self, block: BlockRef) -> DominatorIterator {
        DominatorIterator {
            doms: &self.doms,
            block: Some(block),
        }
    }

    pub fn dominance_frontier(&self, block: BlockRef) -> &HashSet<BlockRef> {
        &self.frontiers[block.0]
    }

    pub fn preorder(&self, root: BlockRef) -> Vec<BlockRef> {
        let mut children = vec![vec![]; self.doms.len()];
        for (i, &dom) in self.doms.iter().enumerate() {
            if dom.0 != i {
                children[dom.0].push(BlockRef(i));
            }
        }
        let mut ret = vec![];
        fn dfs(children: &[Vec<BlockRef>], node: BlockRef, ret: &mut Vec<BlockRef>) {
            ret.push(node);
            for &child in &children[node.0] {
                dfs(children, child, ret);
            }
        }
        dfs(&children, root, &mut ret);
        ret
    }
}

pub struct DominatorIterator<'a> {
    doms: &'a [BlockRef],
    block: Option<BlockRef>,
}

impl<'a> Iterator for DominatorIterator<'a> {
    type Item = BlockRef;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(block) = self.block {
            let next = self.doms[block.0];
            self.block = if next == block { None } else { Some(next) };
            Some(block)
        } else {
            None
        }
    }
}

/**
 * Computes the dominator tree of a method.
 *
 * See "A Simple, Fast Dominance Algorithm" by Cooper, Harvey, and Kennedy.
 * Implementation reference: https://github.com/petgraph/petgraph/blob/master/src/algo/dominators.rs
 */
pub fn compute_dominance(method: &Method) -> Dominance {
    let rev_postorder = reverse_postorder(method);
    let predecessors = predecessors(method);

    // Compute the postorder numbers of blocks.
    let mut block_to_postorder = vec![0; method.n_blocks()];
    for (i, block) in rev_postorder.iter().enumerate() {
        block_to_postorder[block.0] = rev_postorder.len() - i;
    }

    const UNDEFINED: BlockRef = BlockRef(usize::MAX);

    let mut doms = vec![UNDEFINED; method.n_blocks()];
    doms[method.entry.0] = method.entry;

    let mut changed = true;
    while changed {
        changed = false;
        for block in rev_postorder.iter() {
            if block == &method.entry {
                continue;
            }
            let mut cur_predecessors = predecessors[block.0]
                .iter()
                .filter(|&b| doms[b.0] != UNDEFINED);
            let first_predecessor = cur_predecessors.next().unwrap();
            let new_idom_idx = cur_predecessors.fold(*first_predecessor, |new_idom_idx, &pred| {
                intersect(&doms, &block_to_postorder, new_idom_idx, pred)
            });
            if new_idom_idx != doms[block.0] {
                doms[block.0] = new_idom_idx;
                changed = true;
            }
        }
    }

    fn intersect(
        doms: &[BlockRef],
        block_to_postorder: &[usize],
        mut block1: BlockRef,
        mut block2: BlockRef,
    ) -> BlockRef {
        loop {
            match block_to_postorder[block1.0].cmp(&block_to_postorder[block2.0]) {
                std::cmp::Ordering::Less => {
                    block1 = doms[block1.0];
                }
                std::cmp::Ordering::Greater => {
                    block2 = doms[block2.0];
                }
                std::cmp::Ordering::Equal => {
                    return block1;
                }
            }
        }
    }

    let mut frontiers = vec![HashSet::new(); method.n_blocks()];
    for (block, _) in method.iter_blocks() {
        let cur_predecessors = &predecessors[block.0];
        if cur_predecessors.len() >= 2 {
            for pred in cur_predecessors {
                let mut runner = *pred;
                while runner != doms[block.0] {
                    frontiers[runner.0].insert(block);
                    runner = doms[runner.0];
                }
            }
        }
    }

    Dominance { doms, frontiers }
}
