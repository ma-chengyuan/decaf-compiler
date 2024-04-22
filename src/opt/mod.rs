use std::collections::HashSet;

use crate::{
    inter::ir::{BlockRef, Method, Program, Terminator},
    opt::ssa::construct_ssa,
    utils::cli::Optimization,
};

use self::ssa::destruct_ssa;

pub mod copy_prop;
pub mod cse;
pub mod dead_code;
pub mod dom;
pub mod ssa;

// Common graph algorithms for control flow graphs.

/**
 * Apply a function to each successor of a block.
 */
pub fn for_each_successor(method: &Method, block: BlockRef, mut func: impl FnMut(BlockRef)) {
    match method.block(block).term {
        Terminator::Return(_) => {}
        Terminator::Jump(target) => {
            func(target);
        }
        Terminator::CondJump { true_, false_, .. } => {
            func(true_);
            func(false_);
        }
    }
}

/**
 * Compute the reverse postorder of the control flow graph of a method.
 * The returned vector does not include unreachable blocks.
 *
 * Reverse postorder is usually a good linearization of the control flow graph
 * for codegen adn optimization purposes.
 */
pub fn reverse_postorder(method: &Method) -> Vec<BlockRef> {
    let mut postorder = Vec::new();
    let mut discovered = vec![false; method.n_blocks()];
    let mut finished = vec![false; method.n_blocks()];
    let mut stack = vec![method.entry];
    while let Some(&block) = stack.last() {
        if !discovered[block.0] {
            discovered[block.0] = true;
            for_each_successor(method, block, |succ| {
                if !discovered[succ.0] {
                    stack.push(succ);
                }
            });
        } else {
            stack.pop();
            if !finished[block.0] {
                postorder.push(block);
                finished[block.0] = true;
            }
        }
    }
    postorder.reverse();
    postorder
}

/**
 * Compute the predecessors of each block in the control flow graph of a method.
 * Skips unreachable blocks.
 */
pub fn predecessors(method: &Method) -> Vec<HashSet<BlockRef>> {
    let mut preds = vec![HashSet::new(); method.n_blocks()];
    let mut visited = vec![false; method.n_blocks()];

    fn dfs(
        method: &Method,
        preds: &mut Vec<HashSet<BlockRef>>,
        visited: &mut Vec<bool>,
        block: BlockRef,
    ) {
        if !visited[block.0] {
            visited[block.0] = true;
            for_each_successor(method, block, |succ| {
                preds[succ.0].insert(block);
                dfs(method, preds, visited, succ);
            });
        }
    }

    dfs(method, &mut preds, &mut visited, method.entry);
    preds
}

pub fn optimize(mut program: Program, optimizations: &[Optimization]) -> Program {
    let mut optimizations: HashSet<_> = optimizations.iter().cloned().collect();
    if optimizations.remove(&Optimization::All) {
        optimizations.extend([
            Optimization::CopyPropagation,
            Optimization::DeadCodeElimination,
            Optimization::CommonSubexpressionElimination,
        ]);
    }

    // Construct SSA form
    for method in program.methods.values_mut() {
        *method = construct_ssa(method);
    }

    // Dead code elimination
    if optimizations.contains(&Optimization::DeadCodeElimination) {
        for method in program.methods.values_mut() {
            dead_code::eliminate_dead_code(method);
        }
    }

    // Copy propagation
    if optimizations.contains(&Optimization::CopyPropagation) {
        for method in program.methods.values_mut() {
            copy_prop::propagate_copies(method);
        }
    }

    // Common subexpression elimination
    if optimizations.contains(&Optimization::CommonSubexpressionElimination) {
        for method in program.methods.values_mut() {
            cse::eliminate_common_subexpressions(method);
        }
    }

    for (name, method) in program.methods.iter() {
        println!("{}:", name);
        crate::assembler::regalloc::Spiller::new(&program, method, 4).spill();
    }
    // Destruct SSA form
    program.methods = program
        .methods
        .iter()
        .map(|(name, method)| (name.clone(), destruct_ssa(&program, method)))
        .collect();
    program
}
