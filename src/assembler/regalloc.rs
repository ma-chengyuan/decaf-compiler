#![allow(dead_code)]
use std::{
    collections::{HashMap, HashSet, VecDeque},
    hash::Hash,
};

use crate::{
    inter::{
        ir::{BlockRef, Inst, InstRef, Method, Program, Terminator},
        types::Type,
    },
    opt::{
        dom::{compute_dominance, Dominance},
        for_each_successor, predecessors,
    },
    utils::formatting::{Table, TableRow},
};

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

/// A Program Point.
///
/// Note: a block's first program point comes after all phi instructions. This
/// is because phi instructions have special semantics (parallel execution) and
/// technically happens "on the edge" rather than in the block.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ProgPt {
    /// Before an instruction.
    BeforeInst(InstRef),
    /// Before the terminator of a block.
    BeforeTerm(BlockRef),
    /// After the terminator of a block.
    AfterTerm(BlockRef),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ReloadSpill {
    Reload(InstRef),
    Spill(InstRef),
}

pub struct Spiller<'a> {
    program: &'a Program,
    method: Method,
    dom: Dominance,
    dom_tree: Vec<Vec<BlockRef>>,
    max_reg: usize,

    // live_in: Vec<HashSet<InstRef>>,
    // live_out: Vec<HashSet<InstRef>>,
    /// The spill heuristic map for each program point.
    /// Following Hack's paper, at each program point, the spill weight of a
    /// variable is the distance to its nearest use, taking minimum across all
    /// possible paths.
    /// This map also doubles as liveness analysis.
    /// For a block b,
    /// spill_heuristic[first program point of b after phis].keys() = live_in[b]
    /// spill_heuristic[program point after b.term].keys() = live_out[b]
    spill_heuristic: HashMap<ProgPt, HashMap<InstRef, usize>>,
    reg_in: Vec<HashSet<InstRef>>,
    reg_out: Vec<HashSet<InstRef>>,
    spill_reloads: HashMap<ProgPt, Vec<ReloadSpill>>,
    phi_spills: HashSet<InstRef>,
}

impl<'a> Spiller<'a> {
    pub fn new(program: &'a Program, method: &Method, max_reg: usize) -> Self {
        let method = split_critical_edges(method);
        let dom = compute_dominance(&method);
        let dom_tree = dom.dominator_tree();
        Spiller {
            program,
            dom,
            dom_tree,
            // live_in: vec![HashSet::new(); method.n_blocks()],
            // live_out: vec![HashSet::new(); method.n_blocks()],
            spill_heuristic: HashMap::new(),
            reg_in: vec![HashSet::new(); method.n_blocks()],
            reg_out: vec![HashSet::new(); method.n_blocks()],
            spill_reloads: HashMap::new(),
            phi_spills: HashSet::new(),
            max_reg,
            method,
        }
    }

    pub fn spill(&mut self) {
        // self.analyze_liveness();
        self.eval_spill_heuristic();
        for block_ref in self.method.iter_block_refs() {
            self.compute_spills(block_ref);
        }
        self.adjust_spills();
        crate::utils::show_graphviz(&self.dump_graphviz());
    }

    // fn analyze_liveness(&mut self) {
    //     let postorder = self.dom.postorder(self.method.entry);
    //     let predecessors = predecessors(&self.method);
    //     let mut q = VecDeque::new();
    //     let mut in_queue = vec![false; self.method.n_blocks()];
    //     for block in postorder {
    //         q.push_back(block);
    //         in_queue[block.0] = true;
    //     }
    //     while let Some(block) = q.pop_front() {
    //         in_queue[block.0] = false;
    //         if self.analyze_liveness_for_block(block) {
    //             for &p in predecessors[block.0].iter() {
    //                 if !in_queue[p.0] {
    //                     q.push_back(p);
    //                     in_queue[p.0] = true;
    //                 }
    //             }
    //         }
    //     }
    // }

    // fn analyze_liveness_for_block(&mut self, block_ref: BlockRef) -> bool {
    //     let mut live = HashSet::new();
    //     for_each_successor(&self.method, block_ref, |succ| {
    //         let mut live_in = self.live_in[succ.0].clone();
    //         for inst_ref in self.method.block(succ).insts.iter() {
    //             if let Inst::Phi(map) = self.method.inst(*inst_ref) {
    //                 live_in.remove(inst_ref);
    //                 live.insert(map[&block_ref]);
    //             } else {
    //                 break;
    //             }
    //         }
    //         live.extend(live_in.iter().cloned());
    //     });
    //     if self.live_out.get(block_ref.0) == Some(&live) {
    //         return false;
    //     }
    //     self.live_out[block_ref.0] = live.clone();
    //     let term = &mut self.method.block_mut(block_ref).term;
    //     term.for_each_inst_ref(|inst_ref| live.insert(*inst_ref));
    //     let block = self.method.block(block_ref);
    //     for inst_ref in block.insts.clone().into_iter().rev() {
    //         match self.method.inst_mut(inst_ref) {
    //             Inst::Phi(_) => {
    //                 live.insert(inst_ref);
    //             }
    //             other => {
    //                 other.for_each_inst_ref(|inst_ref| live.insert(*inst_ref));
    //                 live.remove(&inst_ref);
    //             }
    //         }
    //     }
    //     if self.live_in.get(block_ref.0) == Some(&live) {
    //         return false;
    //     }
    //     self.live_in[block_ref.0] = live;
    //     true
    // }

    fn eval_spill_heuristic(&mut self) {
        let postorder = self.dom.postorder(self.method.entry);
        let predecessors = predecessors(&self.method);
        let mut q = VecDeque::new();
        let mut in_queue = vec![false; self.method.n_blocks()];
        for block in postorder {
            q.push_back(block);
            in_queue[block.0] = true;
        }
        while let Some(block) = q.pop_front() {
            in_queue[block.0] = false;
            if self.eval_spill_heuristic_for_block(block) {
                for &p in predecessors[block.0].iter() {
                    if !in_queue[p.0] {
                        q.push_back(p);
                        in_queue[p.0] = true;
                    }
                }
            }
        }
    }

    fn update_spill_heuristic(&mut self, prog_pt: ProgPt, h: &HashMap<InstRef, usize>) -> bool {
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

    fn first_prog_pt(&self, block_ref: BlockRef) -> ProgPt {
        for inst_ref in self.method.block(block_ref).insts.iter() {
            match self.method.inst(*inst_ref) {
                Inst::Phi(_) => continue,
                _ => return ProgPt::BeforeInst(*inst_ref),
            }
        }
        ProgPt::BeforeTerm(block_ref)
    }

    fn eval_spill_heuristic_for_block(&mut self, block_ref: BlockRef) -> bool {
        let mut h: HashMap<InstRef, usize> = HashMap::new();
        for_each_successor(&self.method, block_ref, |succ| {
            let first_pt = self.first_prog_pt(succ);
            if let Some(h_successor) = self.spill_heuristic.get(&first_pt) {
                for (inst_ref, cost) in h_successor {
                    h.entry(*inst_ref)
                        .and_modify(|c| *c = (*c).min(*cost + 1))
                        .or_insert(*cost + 1);
                }
            }
            for inst_ref in self.method.block(succ).insts.iter() {
                match self.method.inst(*inst_ref) {
                    Inst::Phi(map) => {
                        // Phi function at the successor block means that the
                        // value is immediately used
                        h.remove(inst_ref);
                        h.insert(map[&block_ref], 0);
                    }
                    _ => break,
                }
            }
        });
        if !self.update_spill_heuristic(ProgPt::AfterTerm(block_ref), &h) {
            return false;
        }
        h.values_mut().for_each(|c| *c += 1);
        self.method
            .block_mut(block_ref)
            .term
            .for_each_inst_ref(|inst_ref| h.insert(*inst_ref, 0));
        if !self.update_spill_heuristic(ProgPt::BeforeTerm(block_ref), &h) {
            return false;
        }
        h.values_mut().for_each(|c| *c += 1);
        let block = self.method.block(block_ref);
        for inst_ref in block.insts.clone().into_iter().rev() {
            match self.method.inst_mut(inst_ref) {
                Inst::Phi(_) => break,
                other => {
                    other.for_each_inst_ref(|inst_ref| h.insert(*inst_ref, 0));
                    h.remove(&inst_ref);
                    if !self.update_spill_heuristic(ProgPt::BeforeInst(inst_ref), &h) {
                        return false;
                    }
                    h.values_mut().for_each(|c| *c += 1);
                }
            }
        }
        true
    }

    pub fn compute_spills(&mut self, block_ref: BlockRef) {
        let first_pt = self.first_prog_pt(block_ref);
        let mut reg_vars: HashSet<InstRef> = self.spill_heuristic[&first_pt]
            .iter()
            .map(|(&i, _)| i)
            .collect();
        let mut in_set = reg_vars.clone();
        let mut used: HashSet<InstRef> = HashSet::new();

        let mut phi_vars = HashSet::new();
        for inst_ref in self.method.block(block_ref).insts.iter() {
            match self.method.inst(*inst_ref) {
                Inst::Phi(_) => {
                    phi_vars.insert(*inst_ref);
                    in_set.remove(inst_ref);
                    if !reg_vars.contains(inst_ref) {
                        // Ideally, reg_vars should already hold inst_ref because
                        // the result of the phi function really should be live at
                        // the first non-phi instruction in the block (otherwise why
                        // insert the phi in the first place?)
                        // But just in case, we insert it here.
                        reg_vars.insert(*inst_ref);
                    }
                }
                _ => break,
            }
        }
        // At this point, reg_vars hold all value we wish to be live at
        // first_pt. But there may be more of them than the number of registers,
        // so some will need to be spilled.
        let mut h = &self.spill_heuristic[&first_pt];
        while reg_vars.len() > self.max_reg {
            let to_spill = reg_vars
                .iter()
                .max_by_key(|i| h.get(i).unwrap_or(&usize::MAX))
                .cloned()
                .unwrap();
            reg_vars.remove(&to_spill);
            if phi_vars.contains(&to_spill) {
                self.phi_spills.insert(to_spill);
                let Inst::Phi(map) = self.method.inst(to_spill) else {
                    unreachable!()
                };
                for src_var in map.values() {
                    // Following Hack's paper, a memory phi must have all its
                    // operand in memory, so these variable better not be in
                    // in_set.
                    in_set.remove(src_var);
                    reg_vars.remove(src_var);
                }
            } else {
                // Just mark it as spilled. The actual spill instruction will be
                // inserted later.
                in_set.remove(&to_spill);
            }
        }
        // At this point, we have ensured that the register pressure at first_pt
        // is at most max_reg.
        // Now we go over the instructions one by one, assuming that the prog
        // point preceding the instruction is already correct, we insert loads
        // and spills so the register pressure throughout and after the
        // instruction is at most max_reg too.
        let insts = self.method.block(block_ref).insts.clone();
        for i in 0..(insts.len() + 1) {
            let mut args = HashSet::new();
            let (pre_pt, result_value) = if i < insts.len() {
                let inst_ref = insts[i];
                match self.method.inst_mut(inst_ref) {
                    Inst::Phi(_) => continue,
                    inst => inst.for_each_inst_ref(|inst_ref| {
                        args.insert(*inst_ref);
                    }),
                };
                let result_value = match self.program.infer_inst_type(&self.method, inst_ref) {
                    Type::Void => None,
                    _ => Some(inst_ref),
                };
                (ProgPt::BeforeInst(inst_ref), result_value)
            } else {
                let term = &mut self.method.block_mut(block_ref).term;
                term.for_each_inst_ref(|inst_ref| {
                    args.insert(*inst_ref);
                });
                (ProgPt::BeforeTerm(block_ref), None)
            };
            let spill_reloads = self.spill_reloads.entry(pre_pt).or_default();
            // Ensure that a value is in register, inserting reloads and spills
            // if necessary.
            let mut ensure_in_reg = |val: InstRef,
                                     used: &mut HashSet<InstRef>,
                                     h: &HashMap<InstRef, usize>,
                                     reload: bool| {
                if !reg_vars.contains(&val) {
                    // A reload is necessary
                    if reg_vars.len() == self.max_reg {
                        // Need to spill a variable first
                        let to_spill = reg_vars
                            .iter()
                            .filter(|i| !args.contains(i))
                            .max_by_key(|i| h.get(i).unwrap_or(&usize::MAX))
                            .cloned()
                            .unwrap();
                        reg_vars.remove(&to_spill);
                        if in_set.contains(&to_spill) && !used.contains(&to_spill) {
                            // It's a mistake to let to_spill be in register at
                            // the beginning of the block
                            in_set.remove(&to_spill);
                        } else {
                            spill_reloads.push(ReloadSpill::Spill(to_spill));
                        }
                    }
                    if reload {
                        spill_reloads.push(ReloadSpill::Reload(val));
                    }
                    reg_vars.insert(val);
                }
            };

            if args.len() + (result_value.is_some() as usize) <= self.max_reg {
                for arg in &args {
                    used.insert(*arg);
                    ensure_in_reg(*arg, &mut used, h, true);
                }
            } else {
                // We are screwed! No way to ensure all arguments (and result,
                // if any) are in registers.
                // All our IR except phi and call have at most 2 argument and 1 result each.
                // So this really only happens with calls which could have an
                // unbounded number of arguments.
                // But function calls should be special-cased anyways...
                // So do nothing here!
            }
            let post_pt = insts
                .get(i + 1)
                .cloned()
                .map_or(ProgPt::BeforeTerm(block_ref), ProgPt::BeforeInst);
            h = &self.spill_heuristic[&post_pt];
            if let Some(result) = result_value {
                ensure_in_reg(result, &mut used, h, false);
            }
        }
        self.reg_out[block_ref.0] = reg_vars;
        self.reg_in[block_ref.0] = in_set;
    }

    /// Insert extra reloads to ensure that for any edge a -> b we have
    /// reg_out[a] is a subset of reg_in[b].
    /// Assumes critical edges have been split.
    fn adjust_spills(&mut self) {
        let predecessors = predecessors(&self.method);
        for block_ref in self.method.iter_block_refs() {
            if predecessors[block_ref.0].len() != 1 {
                // If we the block multiple predecessors, then the block must be
                // the only successor for each of its predecessors.
                let reg_in = &self.reg_in[block_ref.0];
                for pred in predecessors[block_ref.0].iter() {
                    let reg_out = &mut self.reg_out[pred.0];
                    // For every v in reg_in but not reg_out, insert reload of v
                    // at the end of the predecessor. A key property we would
                    // like to keep is that |reg_out| <= max_reg, but inserting
                    // a reload could violate that.
                    for v in reg_in.iter() {
                        if !reg_out.contains(v) {
                            let spill_reloads = self
                                .spill_reloads
                                .entry(ProgPt::AfterTerm(*pred))
                                .or_default();
                            if reg_out.len() == self.max_reg {
                                // Try to fix it by spilling a variable in reg_out.
                                // Note that block_ref is the only successor of
                                // pred, so pred.term is a jump that depends on
                                // no value. Hence, all values in reg_out can be
                                // spilled. In the worst case, we'll just spill
                                // everything in reg_out and replace it with
                                // reg_in.
                                let h = &self.spill_heuristic[&ProgPt::BeforeTerm(*pred)];
                                let to_spill = reg_out
                                    .iter()
                                    .filter(|i| !reg_in.contains(i))
                                    .max_by_key(|i| h.get(i).unwrap_or(&usize::MAX))
                                    .cloned()
                                    .unwrap();
                                spill_reloads.push(ReloadSpill::Spill(to_spill));
                                reg_out.remove(&to_spill);
                            }
                            spill_reloads.push(ReloadSpill::Reload(*v));
                            reg_out.insert(*v); // A key property we w
                        }
                    }
                }
            } else {
                // If thet block has only one predecessor, insert the reloads
                // right after the phi functions. This is fine because it only
                // makes reg_in smaller.
                let pred = predecessors[block_ref.0].iter().next().unwrap();
                let first_pt = self.first_prog_pt(block_ref);
                let reg_in = &mut self.reg_in[block_ref.0];
                let reg_out = &self.reg_out[pred.0];
                let diff = reg_in.difference(reg_out).cloned().collect::<Vec<_>>();
                for v in diff {
                    self.spill_reloads
                        .entry(first_pt)
                        .or_default()
                        .push(ReloadSpill::Reload(v));
                    reg_in.remove(&v);
                }
            }
        }
    }

    pub fn dump_graphviz(&self) -> String {
        let mut output = "digraph G {\n".to_string();
        output.push_str("  rankdir=TD;\n");
        output.push_str("  node [shape=box fontname=Courier];\n");

        let mut stack_slots = Table::new();
        for (stack_slot_ref, stack_slot) in self.method.iter_slack_slots() {
            stack_slots.add_row(
                TableRow::new()
                    .add(stack_slot_ref)
                    .add(&stack_slot.ty)
                    .add(&stack_slot.name.inner),
            );
        }
        output.push_str(
            format!(
                "  stack_slots [label={}];\n",
                format!("{:?}", stack_slots.to_string()).replace("\\n", "\\l")
            )
            .as_str(),
        );
        for (block_ref, block) in self.method.iter_blocks() {
            let mut block_label = format!("{}:", block_ref);
            if let Some(annotation) = self.method.get_block_annotation(&block_ref) {
                block_label.push_str(format!(" ; {}", annotation).as_str());
            }
            // block_label.push('\n');
            block_label.push_str(&format!("\n; reg in: {:?}\n", self.reg_in[block_ref.0]));
            let mut insts = Table::new();
            let add_spill_loads = |spiller: &Spiller<'a>, insts: &mut Table, prog_pt: ProgPt| {
                if let Some(h) = spiller.spill_heuristic.get(&prog_pt) {
                    insts.add_row(TableRow::new().add(";").add("").add(format!("{:?}", h)));
                }
                if let Some(reload_spills) = spiller.spill_reloads.get(&prog_pt) {
                    for rs in reload_spills {
                        let text = match rs {
                            ReloadSpill::Reload(inst) => format!("reload {}", inst),
                            ReloadSpill::Spill(inst) => format!("spill  {}", inst),
                        };
                        insts.add_row(TableRow::new().add(".").add("").add(text));
                    }
                }
            };
            for inst in &block.insts {
                add_spill_loads(self, &mut insts, ProgPt::BeforeInst(*inst));
                let mut row = TableRow::new()
                    .add(inst)
                    .add('=')
                    .add(self.method.inst(*inst));
                if let Some(annotation) = self.method.get_inst_annotation(inst) {
                    row = row.add(format!("; {}", annotation));
                }
                insts.add_row(row);
            }
            add_spill_loads(self, &mut insts, ProgPt::BeforeTerm(block_ref));
            insts.add_row(TableRow::new().add(".").add("").add(&block.term));
            add_spill_loads(self, &mut insts, ProgPt::AfterTerm(block_ref));
            block_label.push_str(format!("{}", insts).as_str());
            block_label.push_str(&format!("\n; reg out: {:?}\n", self.reg_out[block_ref.0]));
            // Escape newlines in the block label and replace to \l to left-align.
            let block_label = format!("{:?}", block_label).replace("\\n", "\\l");

            output.push_str(format!("  {} [label={}];\n", block_ref, block_label).as_str());
        }
        for (block_ref, block) in self.method.iter_blocks() {
            match block.term {
                Terminator::Jump(target) => {
                    output.push_str(format!("  {} -> {};\n", block_ref, target).as_str());
                }
                Terminator::CondJump { true_, false_, .. } => {
                    output
                        .push_str(format!("  {} -> {} [label=true];\n", block_ref, true_).as_str());
                    output.push_str(
                        format!("  {} -> {} [label=false];\n", block_ref, false_).as_str(),
                    );
                }
                _ => {}
            }
        }
        output.push('}');
        output
    }
}
