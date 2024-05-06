use std::collections::HashSet;

use crate::{
    inter::ir::{BlockRef, Inst, Method, Program, Terminator},
    opt::ssa::construct_ssa,
    utils::cli::Optimization,
};

pub mod array_split;
pub mod constant_folding;
pub mod copy_prop;
pub mod cse;
pub mod dead_code;
pub mod dom;
pub mod function_inlining;
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

/// Create a new method where all critical edges are split.
///
/// Critical edges are edges of the form A->B where A has >=2 successors and B
/// has >=2 predecessors. The problem with critical edges is that their
/// existence makes it hard to add code "to the edge," which is often needed
/// when destructing phi instructions. Without phi edges,
///
/// - A->B, A has multiple successors => A must be B's only predecessor =>
///   adding code "on edge" is prepending to B;
/// - A->B, B has multiple predecessors => B must be A's only successor =>
///   adding code "on edge" is appending to A.
///
/// Nice and simple. Can't do that with critical edges though.
pub fn split_critical_edges(method: &Method) -> Method {
    let mut new_method = method.clone();
    let predecessors = predecessors(method);
    for block in method.iter_block_refs() {
        if predecessors[block.0].len() <= 1 {
            continue;
        }
        for pred in predecessors[block.0].iter() {
            let mut successors = HashSet::new();
            for_each_successor(method, *pred, |succ| {
                successors.insert(succ);
            });
            if successors.len() == 1 {
                // If we only have one successor, we can just jump to it.
                // This is just in case the original terminator is a conditional
                // jump with the same destination on both branches. This slightly
                // messes up with register allocation down the line.
                let succ = *successors.iter().next().unwrap();
                new_method.block_mut(*pred).term = Terminator::Jump(succ);
            }
            let critical = successors.len() >= 2;
            if critical {
                let edge_block = new_method.next_block();
                new_method.block_mut(*pred).term.for_each_block_ref(|succ| {
                    if *succ == block {
                        *succ = edge_block;
                    }
                });
                new_method.block_mut(edge_block).term = Terminator::Jump(block);
                for inst_ref in new_method.block(block).insts.clone() {
                    let Inst::Phi(map) = new_method.inst_mut(inst_ref) else {
                        break;
                    };
                    map.insert(edge_block, map[&pred]);
                    map.remove(pred);
                }
            };
        }
    }
    new_method
}

pub fn optimize(mut program: Program, optimizations: &[Optimization]) -> Program {
    let mut optimizations: HashSet<_> = optimizations.iter().cloned().collect();
    if optimizations.remove(&Optimization::All) {
        optimizations.extend([
            Optimization::CopyPropagation,
            Optimization::DeadCodeElimination,
            Optimization::CommonSubexpressionElimination,
            Optimization::ConstantFolding,
            // Optimization::ArraySplitting,
            Optimization::FunctionInlining,
        ]);
    }

    if optimizations.contains(&Optimization::FunctionInlining) {
        // function_inlining::inline_functions(&mut program);
    }

    // Construct SSA form
    for method in program.methods.values_mut() {
        *method = construct_ssa(method);
    }

    for _ in 0..10 {
        // Constant folding
        if optimizations.contains(&Optimization::ConstantFolding) {
            for method in program.methods.values_mut() {
                constant_folding::fold_constants(method);
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

        // Dead code elimination
        if optimizations.contains(&Optimization::DeadCodeElimination) {
            for method in program.methods.values_mut() {
                dead_code::eliminate_dead_code(method);
            }
        }

        if optimizations.contains(&Optimization::ArraySplitting) {
            for method in program.methods.values_mut() {
                array_split::split_arrays(method);
            }
        }
    }

    // let mut ls = vec![];
    // for (name, method) in program.methods.iter() {
    //     // println!("{}:", name);
    //     let max_reg = 3;
    //     let mut lowered = crate::assembler::spill::Spiller::new(&program, method, max_reg).spill();
    //     crate::assembler::regalloc::RegAllocator::new(&program, &mut lowered, max_reg).allocate();
    //     ls.push(lowered);
    // }
    // let mut assembler = crate::assembler::Assembler::new(program.clone());
    // let _output = assembler.assemble_lowered("test.S", ls);
    // println!("{}", output);

    // Destruct SSA form
    // program.methods = program
    //     .methods
    //     .iter()
    //     .map(|(name, method)| (name.clone(), destruct_ssa(&program, method)))
    //     .collect();
    program
}
