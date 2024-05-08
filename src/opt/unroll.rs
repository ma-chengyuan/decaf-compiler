//! Loop unrolling
use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::inter::{
    constant::Const,
    ir::{BlockRef, Inst, InstRef, Method, Terminator},
};

use super::loop_utils::{Loop, LoopAnalysis};

const UNROLL_N_BLOCKS: usize = 10;
const UNROLL_N_INSTS: usize = 30;
const UNROLL_N_TRIP_COUNT: i64 = 8; // Unroll loops with trip count <= 8

fn find_unroll_target(method: &Method, loops: &LoopAnalysis) -> Option<(Rc<RefCell<Loop>>, usize)> {
    'next_loop: for header_ref in method.iter_block_refs().filter(|b| loops.is_header(*b)) {
        let rc_loop = loops.get_loop(header_ref).unwrap();
        let loop_ = rc_loop.borrow();
        if loop_.break_.len() > 1 {
            // Do not unroll loops with multiple exits.
            continue;
        }
        if loop_.continue_.len() > 1 {
            // Do not unroll loops with multiple back edges.
            continue;
        }
        if loop_.body.len() > UNROLL_N_BLOCKS {
            // Do not unroll large loops.
            continue;
        }
        if !loop_.break_.contains(&header_ref) {
            // For now we only unroll loop where the header node is also the break node.
            continue;
        }

        let depth = loop_.depth();
        let mut n_insts = 0;
        for block_ref in loop_.body.iter() {
            if loops.get_loop(*block_ref).unwrap().borrow().depth() > depth {
                // Do not unroll loops with nested loops.
                continue 'next_loop;
            }
            n_insts += method.block(*block_ref).insts.len();
            if n_insts > UNROLL_N_INSTS {
                // Do not unroll loops with many instructions.
                continue 'next_loop;
            }
        }

        // Find the loop variable and the value at which the loop breaks.
        macro_rules! get_const {
            ($x:expr) => {
                match method.inst($x) {
                    Inst::LoadConst(Const::Int(n)) => Some(*n),
                    _ => None,
                }
            };
        }

        let (loop_var, exit_value, expect_increment) = match &method.block(header_ref).term {
            Terminator::CondJump {
                cond,
                true_,
                false_,
            } => {
                if !loop_.body.contains(true_) && !loop_.body.contains(false_) {
                    continue;
                }
                let break_on_true = loop_.body.contains(false_);
                match method.inst(*cond) {
                    Inst::Less(a, b) => match (get_const!(*a), get_const!(*b)) {
                        // If a >= b then break, expect a to be a incrementing variable
                        // If a < b then break, expect a to be an decrementing variable
                        (None, Some(b)) => (*a, b - (break_on_true as i64), !break_on_true),
                        // If b <= a then break, expect b to be an decrementing variable
                        // If b > a then break, expect b to be a incrementing variable
                        (Some(a), None) => (*b, a + (break_on_true as i64), break_on_true),
                        _ => continue,
                    },
                    Inst::LessEq(a, b) => match (get_const!(*a), get_const!(*b)) {
                        // If a > b then break, expect a to be a incrementing variable
                        // If a <= b then break, expect a to be an decrementing variable
                        (None, Some(b)) => (*a, b + (!break_on_true as i64), !break_on_true),
                        // If b < a then break, expect b to be an decrementing variable
                        // If b >= a then break, expect b to be a incrementing variable
                        (Some(a), None) => (*b, a - (!break_on_true as i64), break_on_true),
                        _ => continue,
                    },
                    _ => continue,
                }
            }
            _ => continue,
        };
        // The loop variable will need to be a phi node.
        let Inst::Phi(map) = method.inst(loop_var) else {
            continue;
        };
        // The loop variable will need to be initialized by a constant.
        let mut initial_value: Option<i64> = None;
        let mut increment: Option<i64> = None;
        for (src_block, src_inst_ref) in map.iter() {
            if !loop_.body.contains(src_block) {
                initial_value = match (initial_value, method.inst(*src_inst_ref)) {
                    (None, Inst::LoadConst(Const::Int(n))) => Some(*n),
                    (Some(v), Inst::LoadConst(Const::Int(n))) if v == *n => Some(*n),
                    _ => continue 'next_loop,
                };
            } else {
                let (lhs, rhs, sign) = match method.inst(*src_inst_ref) {
                    Inst::Add(lhs, rhs) if *lhs == loop_var || *rhs == loop_var => (lhs, rhs, 1),
                    Inst::Sub(lhs, rhs) if *lhs == loop_var => (lhs, rhs, -1),
                    _ => continue 'next_loop,
                };
                let other = if *lhs == loop_var { *rhs } else { *lhs };
                match method.inst(other) {
                    Inst::LoadConst(Const::Int(n)) => {
                        increment = match (increment, *n * sign) {
                            (None, n) => Some(n),
                            (Some(inc), n) if inc == n => Some(n),
                            _ => continue 'next_loop,
                        };
                    }
                    _ => continue 'next_loop,
                }
            }
        }
        let initial_value = initial_value.unwrap();
        let increment = increment.unwrap();
        let trip_count = if expect_increment && increment > 0 && exit_value > initial_value {
            (exit_value - initial_value + increment - 1) / increment
        } else if !expect_increment && increment < 0 && exit_value < initial_value {
            (initial_value - exit_value - increment - 1) / -increment
        } else {
            // The loop variable must be incremented or decremented.
            continue;
        };

        if trip_count <= 0 {
            // Do not unroll loops with non-positive trip counts.
            continue;
        }
        if trip_count > UNROLL_N_TRIP_COUNT {
            // Do not unroll loops with large trip counts.
            continue;
        }
        // println!(
        //     "{} -> {} step {} ({})",
        //     initial_value, exit_value, increment, trip_count
        // );
        return Some((loops.get_loop(header_ref).unwrap(), trip_count as usize));
    }
    None
}

pub fn unroll_loops(method: &mut Method) {
    loop {
        let mut loops = LoopAnalysis::new(method);
        let Some((rc_loop, trip_count)) = find_unroll_target(method, &loops) else {
            break;
        };
        let header_ref = rc_loop.borrow().header;
        let pre_header_ref = loops.get_or_insert_pre_header(method, header_ref);
        let loop_ = rc_loop.borrow();

        let mut block_maps: Vec<HashMap<BlockRef, BlockRef>> = vec![HashMap::new(); trip_count];
        let mut inst_maps: Vec<HashMap<InstRef, InstRef>> = vec![HashMap::new(); trip_count];

        for (block_map, inst_map) in block_maps.iter_mut().zip(inst_maps.iter_mut()) {
            for block_ref in loop_.body.iter() {
                let new_block_ref = method.next_block();
                method.block_mut(new_block_ref).term = method.block(*block_ref).term.clone();
                if let Some(annotation) = method.get_block_annotation(block_ref) {
                    *method.annotate_block_mut(new_block_ref) = annotation.clone();
                }
                block_map.insert(*block_ref, new_block_ref);
                for inst_ref in method.block(*block_ref).insts.clone() {
                    let new_inst_ref =
                        method.next_inst(new_block_ref, method.inst(inst_ref).clone());
                    if let Some(annotation) = method.get_inst_annotation(&inst_ref) {
                        *method.annotate_inst_mut(new_inst_ref) = annotation.clone();
                    }
                    inst_map.insert(inst_ref, new_inst_ref);
                }
            }
        }
        // Now fix the transitions

        // Pre-header -> Header of 0th iteration
        method.block_mut(pre_header_ref).term = Terminator::Jump(block_maps[0][&header_ref]);
        for i in 0..trip_count {
            let header_term = &mut method.block_mut(block_maps[i][&header_ref]).term;
            // Update header terminator: remove break edges, go striaight into the loop body
            *header_term = match header_term {
                Terminator::CondJump { true_, false_, .. } => {
                    Terminator::Jump(if loop_.body.contains(true_) {
                        block_maps[i][true_]
                    } else {
                        block_maps[i][false_]
                    })
                }
                _ => unreachable!(),
            };
            // Update body terminators: redirect continue edges to the next iteration
            for block_ref in loop_
                .body
                .iter()
                .filter(|b| **b != header_ref)
                .map(|b| block_maps[i][b])
            {
                let term = &mut method.block_mut(block_ref).term;
                term.for_each_block_ref(|succ| {
                    if *succ == header_ref {
                        // Redirect back edge to next iteration
                        *succ = if i + 1 < trip_count {
                            block_maps[i + 1][&header_ref]
                        } else {
                            header_ref
                        };
                    } else {
                        // Update other edges, succ must be in the loop.
                        // Otherwise it's another break edge. We assume the only
                        // break edge is in the header.
                        *succ = block_maps[i][succ];
                    }
                });
                term.for_each_inst_ref(|arg_ref| {
                    *arg_ref = *inst_maps[i].get(arg_ref).unwrap_or(arg_ref);
                })
            }
            // Update instructions
            for block_ref in loop_.body.iter().map(|b| block_maps[i][b]) {
                for inst_ref in method.block(block_ref).insts.clone() {
                    // Header phi needs special treatment
                    if let Inst::Phi(map) = method.inst_mut(inst_ref) {
                        if block_ref == block_maps[i][&header_ref] {
                            if i == 0 {
                                // In the first unrolled iteration, the
                                // preheader is the only predecessor to header.
                                // The phi is gone.
                                *method.inst_mut(inst_ref) = Inst::Copy(map[&pre_header_ref]);
                            } else {
                                map.remove(&pre_header_ref);
                                // In the subsequent unrolled iterations, the
                                // continue edges from the previous iteration
                                // are the predecessors to the header.
                                *map = map
                                    .iter()
                                    .map(|(src_block, src_ref)| {
                                        (block_maps[i - 1][src_block], inst_maps[i - 1][src_ref])
                                    })
                                    .collect();
                                if map.len() == 1 {
                                    // The phi is gone too
                                    let src = map.values().copied().next().unwrap();
                                    *method.inst_mut(inst_ref) = Inst::Copy(src);
                                }
                            }
                        } else {
                            *map = map
                                .iter()
                                .map(|(src_block, src_ref)| {
                                    (block_maps[i][src_block], inst_maps[i][src_ref])
                                })
                                .collect();
                        }
                    } else {
                        method.inst_mut(inst_ref).for_each_inst_ref(|arg_ref| {
                            *arg_ref = *inst_maps[i].get(arg_ref).unwrap_or(arg_ref);
                        });
                    }
                }
            }
        }

        // Now some special treatment to the initial header ref block.
        let header_term = &mut method.block_mut(header_ref).term;
        // The last header is meant to break directly. Remove continue edges.
        *header_term = match header_term {
            Terminator::CondJump { true_, false_, .. } => {
                Terminator::Jump(if loop_.body.contains(true_) {
                    *false_
                } else {
                    *true_
                })
            }
            _ => unreachable!(),
        };
        for phi_ref in method.phis(header_ref) {
            let Inst::Phi(map) = method.inst_mut(phi_ref) else {
                unreachable!();
            };
            map.remove(&pre_header_ref);
            *map = map
                .iter()
                .map(|(src_block, src_ref)| {
                    (
                        block_maps[trip_count - 1][src_block],
                        inst_maps[trip_count - 1][src_ref],
                    )
                })
                .collect();
            if map.len() == 1 {
                // The phi is gone too
                let src = map.values().copied().next().unwrap();
                *method.inst_mut(phi_ref) = Inst::Copy(src);
            };
        }
        method.remove_unreachable();
        method.merge_blocks();
    }
}
