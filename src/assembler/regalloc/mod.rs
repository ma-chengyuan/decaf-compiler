#![allow(dead_code)]
use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet, VecDeque},
    hash::Hash,
};

use crate::{
    inter::{
        ir::{Address, BlockRef, Inst, InstRef, Method, Program, StackSlotRef, Terminator},
        types::Type,
    },
    opt::{
        dom::{compute_dominance, Dominance},
        for_each_successor, predecessors, reverse_postorder, ssa,
    },
    utils::{
        formatting::{Table, TableRow},
        make_internal_ident,
    },
};

mod belady;

use belady::BeladyMap;

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
    // Precomputed data that many parts of the algorithm need.
    dom: Dominance,
    dom_tree: Vec<Vec<BlockRef>>,
    predecessors: Vec<HashSet<BlockRef>>,
    rev_postorder: Vec<BlockRef>,
    /// Maps an instruction to the block it belongs to and its index in the
    /// block.
    inst_to_block_pos: Vec<(BlockRef, usize)>,

    /// Max number of registers available.
    max_reg: usize,

    /// The spill heuristic map for each program point.
    /// Following Hack's paper, at each program point, the spill weight of a
    /// variable is the distance to its nearest use, taking minimum across all
    /// possible paths. (extention of Belady's MIN heuristic)
    /// This map also doubles as liveness analysis.
    /// For a block b,
    /// spill_heuristic[first program point of b after phis].keys() = live_in[b]
    /// spill_heuristic[program point after b.term].keys() = live_out[b]
    spill_heuristic: HashMap<ProgPt, BeladyMap>,
    /// reg_in[block]: set of variables that must be in register at the
    /// beginning of block.
    reg_in: Vec<HashSet<InstRef>>,
    /// reg_out[block]: set of variables that must be in register at the end of
    /// block.
    reg_out: Vec<HashSet<InstRef>>,
    /// spill_in[block]: set of variables that must be spilled at the beginning
    /// of block. spill_in is always a subset of reg_in.
    spill_in: Vec<HashSet<InstRef>>,
    /// spill_out[block]: set of variables that must be spilled at the end of
    /// block. spill_out is always a subset of reg_out.
    spill_out: Vec<HashSet<InstRef>>,
    /// Inserted spills and reloads at each program point.
    spill_reloads: HashMap<ProgPt, Vec<ReloadSpill>>,
    /// Mapping from spilled variables to their spill sites.
    spill_sites: HashMap<InstRef, HashSet<ProgPt>>,

    /// Phi-spills that will be converted to PhiMem instructions.
    /// There is a difference between a phi instruction followed by a spill of
    /// its result and a phi-spill. For the former, the result must briefly stay
    /// in some register. The latter is a pure memory-to-memory operation. We
    /// require that operands of a phi-spill are also spilled.
    phi_spills: HashSet<InstRef>,

    /// Mapping from spilled variables to their spill slots.
    spill_slots: HashMap<InstRef, StackSlotRef>,
}

impl<'a> Spiller<'a> {
    pub fn new(program: &'a Program, method: &Method, max_reg: usize) -> Self {
        let method = split_critical_edges(method);
        let dom = compute_dominance(&method);
        let dom_tree = dom.dominator_tree();
        let mut inst_to_block_pos = vec![(BlockRef(0), 0); method.n_insts()];
        for block_ref in method.iter_block_refs() {
            for (i, inst_ref) in method.block(block_ref).insts.iter().enumerate() {
                inst_to_block_pos[inst_ref.0] = (block_ref, i);
            }
        }
        Spiller {
            program,
            dom,
            dom_tree,
            predecessors: predecessors(&method),
            rev_postorder: reverse_postorder(&method),
            spill_heuristic: HashMap::new(),
            reg_in: vec![HashSet::new(); method.n_blocks()],
            reg_out: vec![HashSet::new(); method.n_blocks()],
            spill_in: vec![HashSet::new(); method.n_blocks()],
            spill_out: vec![HashSet::new(); method.n_blocks()],
            spill_reloads: HashMap::new(),
            spill_slots: HashMap::new(),
            spill_sites: HashMap::new(),
            phi_spills: HashSet::new(),
            inst_to_block_pos,
            max_reg,
            method,
        }
    }

    fn sanity_check_rev_postorder(&self) {
        let mut visited = vec![false; self.method.n_blocks()];
        for block in self.rev_postorder.iter() {
            for pred in self.predecessors[block.0].iter() {
                if self.dom.dominates(*block, *pred) {
                    assert!(!visited[pred.0]);
                } else {
                    assert!(visited[pred.0]);
                }
            }
            visited[block.0] = true;
        }
    }

    pub fn spill(mut self) -> Method {
        self.eval_spill_heuristic();
        // Go over blocks in reverse postorder.
        // For normal blocks that aren't loop headers, this order ensures that
        // all its predecessors have been processed by the time we process the
        // block.

        // Some sanity check.
        if cfg!(debug_assertions) {
            self.sanity_check_rev_postorder()
        }

        // .clone() to appease the borrow checker.
        let rev_postorder = self.rev_postorder.clone();
        for block in &rev_postorder {
            self.insert_intrablock_spills(*block);
        }
        for block in &rev_postorder {
            self.fix_interblock_coupling(*block);
        }
        // crate::utils::show_graphviz(&self.dump_graphviz());
        let new_method = self.reconstruct_ssa();
        // crate::utils::show_graphviz(&new_method.dump_graphviz());
        new_method
    }

    /// Returns the first program point of a block.
    ///
    /// The first program point of a block is here defined as the first program
    /// point AFTER ALL PHI instructions. Phi instructions don't count since
    /// they execute in parallel and should really happen "on the edge."
    fn first_prog_pt(&self, block_ref: BlockRef) -> ProgPt {
        for inst_ref in self.method.block(block_ref).insts.iter() {
            match self.method.inst(*inst_ref) {
                Inst::Phi(_) | Inst::PhiMem { .. } => continue,
                _ => return ProgPt::BeforeInst(*inst_ref),
            }
        }
        ProgPt::BeforeTerm(block_ref)
    }

    /// Get the set of phi instructions at the beginning of a block, excluding
    /// phi memory instructions.
    fn get_phis(&self, block_ref: BlockRef) -> HashSet<InstRef> {
        let mut phis = HashSet::new();
        for inst_ref in self.method.block(block_ref).insts.iter() {
            match self.method.inst(*inst_ref) {
                Inst::Phi(_) => {
                    phis.insert(*inst_ref);
                }
                Inst::PhiMem { .. } => continue,
                _ => break,
            }
        }
        phis
    }

    /// Returns the set of blocks that are in the loop containing block_ref.
    /// Or None if block_ref is not a loop header.
    fn get_loop(&self, block_ref: BlockRef) -> Option<HashSet<BlockRef>> {
        let mut body: Option<HashSet<BlockRef>> = None;
        for pred in self.predecessors[block_ref.0].iter() {
            if self.dom.dominates(block_ref, *pred) {
                let mut this_body = HashSet::new();
                this_body.insert(block_ref);
                let mut stack = Vec::new();
                stack.push(*pred);
                while let Some(block) = stack.pop() {
                    if !this_body.insert(block) {
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
        body
    }

    /// Gets the set of variables used in a loop and the maximum register
    /// pressure inside the loop.
    fn get_loop_used_vars_and_max_pressure(
        &mut self,
        loop_body: &HashSet<BlockRef>,
        candidates: &HashSet<InstRef>,
    ) -> (HashSet<InstRef>, usize) {
        let mut used = HashSet::new();
        let mut max_pressure = 0;
        let mut update_used = |var: &mut InstRef| {
            if candidates.contains(var) {
                used.insert(*var);
            }
        };
        let mut update_max_pressure = |prog_pt: &ProgPt| {
            max_pressure = max_pressure.max(self.spill_heuristic[prog_pt].len());
        };
        for block in loop_body {
            for inst_ref in self.method.block(*block).insts.clone() {
                match self.method.inst_mut(inst_ref) {
                    Inst::Phi(map) => {
                        for (src, var) in map {
                            if loop_body.contains(src) {
                                update_used(var)
                            }
                        }
                    }
                    inst => {
                        update_max_pressure(&ProgPt::BeforeInst(inst_ref));
                        inst.for_each_inst_ref(&mut update_used)
                    }
                }
            }
            update_max_pressure(&ProgPt::BeforeTerm(*block));
            self.method
                .block_mut(*block)
                .term
                .for_each_inst_ref(&mut update_used);
            update_max_pressure(&ProgPt::AfterTerm(*block));
        }
        (used, max_pressure)
    }

    /// Given a variable that's supposedly live at the start of a block, should
    /// we take it into a register?
    ///
    /// - `loop_usage` is the set of variables used in the loop if the program
    ///   point starts a loop header, or empty otherwise.
    /// - `availability` is an estimate if the variable is available in the
    ///   block's predessors. There are three possible values:
    ///   - None: we don't know.
    ///   - Some(true): the variable is available in all predecessors.
    ///   - Some(false): the variable is not available in all predecessors.
    ///
    /// There are three possible return values:
    /// - Some(true): definitely take the variable.
    /// - Some(false): definitely don't take the variable.
    /// - None: we don't know.
    ///
    /// Reference: https://github.com/libfirm/libfirm/blob/master/ir/be/bespillbelady.c#L403
    fn should_take_variable(
        &self,
        block_ref: BlockRef,
        var: InstRef,
        loop_usage: &HashSet<InstRef>,
        availability: Option<bool>,
    ) -> Option<bool> {
        let h = &self.spill_heuristic[&self.first_prog_pt(block_ref)];
        if !h.is_live(&var) {
            // If a variable is supposedly "live", but actually not, it must be a phi.
            // A dead phi is not worth taking.
            return Some(false);
        }
        if availability == Some(true) {
            // If a variable is available in all predecessors, we should take it.
            return Some(true);
        } else if availability == Some(false) {
            // If a variable is not available in all predecessors, we should not take it.
            return Some(false);
        }
        if loop_usage.contains(&var) {
            // If the variable is used in the loop, we should take it.
            return Some(true);
        }
        None // Not really sure
    }

    /// Returns if a variable is available in all predecessors of a block.
    /// `block_ref` must NOT be a loop header.
    fn is_available_in_all_predecessors(
        &self,
        block_ref: BlockRef,
        var: InstRef,
        block_phis: &HashSet<InstRef>,
    ) -> bool {
        let mut ret = true;
        for pred in self.predecessors[block_ref.0].iter() {
            let var = match self.method.inst(var) {
                Inst::Phi(map) if block_phis.contains(&var) => map[&pred],
                _ => var,
            };
            if !self.reg_out[pred.0].contains(&var) {
                ret = false;
                break;
            }
        }
        ret
    }

    /// Initialize the set of registers to be used at the beginning of a block.
    /// Returns two sets, reg_in and spill_in. reg_in is the set of variables
    /// assumed to be in register at the start of a block (e.g., first program
    /// point after phi). spill_in is a subset of reg_in, containing variables
    /// that have been spilled.
    fn init_reg_in(&mut self, block_ref: BlockRef) -> (HashSet<InstRef>, HashSet<InstRef>) {
        if self.predecessors[block_ref.0].is_empty() {
            // Initial block
            return (HashSet::new(), HashSet::new());
        } else if self.predecessors[block_ref.0].len() == 1 {
            let pred = self.predecessors[block_ref.0].iter().next().unwrap();
            return (self.reg_out[pred.0].clone(), self.spill_out[pred.0].clone());
        }

        let first_pt = self.first_prog_pt(block_ref);
        let loop_body = self.get_loop(block_ref);
        // The set of variables we very much want to take into registers.
        let mut starter: Vec<InstRef> = vec![];
        // Uh..., not so sure, but good to have.
        let mut delayed: Vec<InstRef> = vec![];
        let phis = self.get_phis(block_ref);

        // If a loop, gets used variables in the loop and the maximum register
        // pressure.
        let (loop_usage, max_pressure) = match &loop_body {
            Some(loop_body) => {
                let mut alive = phis.clone();
                alive.extend(self.spill_heuristic[&first_pt].iter().map(|(var, _)| var));
                self.get_loop_used_vars_and_max_pressure(loop_body, &alive)
            }
            None => (HashSet::new(), 0),
        };

        let h = &self.spill_heuristic[&first_pt];
        let mut phi_plus_live_in = phis.clone();
        phi_plus_live_in.extend(h.iter().map(|(var, _)| var));

        for var in phi_plus_live_in {
            let availability = match &loop_body {
                None => Some(self.is_available_in_all_predecessors(block_ref, var, &phis)),
                Some(_) => None,
            };
            match self.should_take_variable(block_ref, var, &loop_usage, availability) {
                Some(true) => starter.push(var),
                None => delayed.push(var),
                Some(false) => {}
            }
        }

        // Do we have more registers slots that can be used beyond starter?
        let n_free_slots = self.max_reg.saturating_sub(starter.len());
        // Recall self.should_take_variable, a variable is in delayed if and
        // only if block_ref is a loop header, the variable is live in the loop,
        // but not used in the loop. That is, the variable lives through the
        // loop. These variables should have been counted as part of the max
        // register pressure of the loop. Hence, max_pressure - delayed.len() is
        // the register pressure caused by variables actually used in the loop.
        // self.max_reg - (max_pressure - delayed.len()) is the number of free
        // slots if we keep all variables used in the loop in registers.
        let n_free_pressure_slots = self
            .max_reg
            .saturating_sub(max_pressure.saturating_sub(delayed.len()));
        let mut n_free_slots = n_free_slots.min(n_free_pressure_slots);
        if n_free_slots > 0 {
            delayed.sort_by_key(|var| (h.get(var), var.0));
            for var in delayed.iter() {
                if n_free_slots == 0 {
                    break;
                }
                let mut take = true;
                // Decide if we should take the variable.
                match self.method.inst(*var) {
                    Inst::Phi(_) => {
                        // Phi nodes incur some extra movements anyway so we care less
                    }
                    _ => {
                        for pred in self.predecessors[block_ref.0].iter() {
                            if self.dom.dominates(block_ref, *pred) {
                                // Loop backedge, we haven't visited pred yet.
                            }
                            if !self.reg_out[pred.0].contains(var) {
                                // If not available in a visited predecessor,
                                // don't take it as it would incur a reload.
                                take = false;
                                break;
                            }
                        }
                    }
                }
                if take {
                    starter.push(*var);
                    n_free_slots -= 1;
                }
            }
        }
        starter.sort_by_key(|var| (h.get(var), var.0));
        let reg_in = starter
            .into_iter()
            .take(self.max_reg)
            .collect::<HashSet<_>>();
        let mut spill_in: HashSet<InstRef> = HashSet::new();
        for phi_var in &phis {
            if !reg_in.contains(phi_var) {
                self.add_phi_spill(*phi_var);
            }
        }
        for var in reg_in.iter() {
            if phis.contains(var) {
                // Don't consider phi as spilled.
                continue;
            }
            for pred in self.predecessors[block_ref.0].iter() {
                if self.dom.dominates(block_ref, *pred) {
                    continue; // Loop backedge, we haven't visited pred yet.
                }
                // If the value has been spilled in a predecessor, consider it
                // spilled.
                if self.spill_in[pred.0].contains(var) {
                    spill_in.insert(*var);
                    break;
                }
            }
        }
        (reg_in, spill_in)
    }

    /// Checks if a program point dominates another.
    fn prog_pt_dominates(&self, a: &ProgPt, b: &ProgPt) -> bool {
        let get_block_pos = |pt: &ProgPt| match pt {
            ProgPt::BeforeInst(inst_ref) => self.inst_to_block_pos[inst_ref.0],
            ProgPt::BeforeTerm(block_ref) => {
                (*block_ref, self.method.block(*block_ref).insts.len())
            }
            ProgPt::AfterTerm(block_ref) => {
                (*block_ref, self.method.block(*block_ref).insts.len() + 1)
            }
        };
        let (block_a, pos_a) = get_block_pos(a);
        let (block_b, pos_b) = get_block_pos(b);
        if block_a == block_b {
            pos_a <= pos_b
        } else {
            self.dom.dominates(block_a, block_b)
        }
    }

    /// Adds a spill of a variable at a program point.
    fn add_spill(&mut self, prog_pt: &ProgPt, var: InstRef) {
        // It's a hard fight against the borrow checker, had to clone here so we
        // don't borrow self.
        let mut sites = self.spill_sites.get(&var).cloned().unwrap_or_default();
        for site in sites.clone() {
            // And clone again so we don't borrow sites.
            if self.prog_pt_dominates(&site, prog_pt) {
                // If the spill is dominated by another spill, we don't need to
                // spill.
                return;
            }
            if self.prog_pt_dominates(prog_pt, &site) {
                // Remove all spills we dominate.
                sites.remove(&site);
                self.spill_reloads
                    .entry(site)
                    .or_default()
                    .retain(|rs| rs != &ReloadSpill::Spill(var));
            }
        }
        sites.insert(*prog_pt);
        self.spill_reloads
            .entry(*prog_pt)
            .or_default()
            .push(ReloadSpill::Spill(var));
        self.spill_sites.insert(var, sites);
    }

    /// Adds a reload of a variable at a program point.
    fn add_reload(&mut self, prog_pt: &ProgPt, var: InstRef) {
        self.spill_reloads
            .entry(*prog_pt)
            .or_default()
            .push(ReloadSpill::Reload(var));
    }

    /// Adds a phi-spill to the list of phi-spills.
    fn add_phi_spill(&mut self, phi_var: InstRef) {
        if self.phi_spills.insert(phi_var) {
            let Inst::Phi(map) = self.method.inst(phi_var) else {
                unreachable!();
            };
            for (pred, var) in map.clone() {
                self.add_spill(&ProgPt::BeforeTerm(pred), var);
            }
        }
    }

    fn fix_interblock_coupling(&mut self, block_ref: BlockRef) {
        let first_pt = self.first_prog_pt(block_ref);
        let phis = self.get_phis(block_ref);
        let reg_in = self.reg_in[block_ref.0].clone();
        let spill_in = self.spill_in[block_ref.0].clone();
        let h = self.spill_heuristic[&first_pt].clone();
        for pred in self.predecessors[block_ref.0].clone() {
            if self.dom.dominates(block_ref, pred) {
                continue;
            }
            let reg_out = self.reg_out[pred.0].clone();
            let spill_out = self.spill_out[pred.0].clone();
            for var in reg_out.iter() {
                if !reg_in.contains(var) && h.is_live(var) && !spill_out.contains(var) {
                    self.add_spill(&ProgPt::BeforeTerm(pred), *var);
                }
            }
            for var in reg_in.iter() {
                let var = match self.method.inst(*var) {
                    Inst::Phi(map) if phis.contains(var) => map[&pred],
                    _ => *var,
                };
                if reg_out.contains(&var) {
                    if !spill_out.contains(&var) && spill_in.contains(&var) {
                        self.add_spill(&ProgPt::BeforeTerm(pred), var);
                    }
                } else {
                    // Insert reload on the edge.
                    if self.predecessors[pred.0].len() > 1 {
                        self.add_reload(&ProgPt::BeforeTerm(pred), var);
                    } else {
                        self.add_reload(&first_pt, var);
                    }
                }
            }
        }
    }

    /// Insert spills and reloads to ensure that the register pressure at a
    /// block is at most max_reg. This is done locally for each block.
    fn insert_intrablock_spills(&mut self, block_ref: BlockRef) {
        let (mut live, mut spilled) = self.init_reg_in(block_ref);
        self.reg_in[block_ref.0] = live.clone();
        self.spill_in[block_ref.0] = spilled.clone();

        fn limit(
            spiller: &mut Spiller,
            live: &mut HashSet<InstRef>,
            spilled: &mut HashSet<InstRef>,
            h: &BeladyMap,
            spill_pt: &ProgPt,
            count: usize,
        ) {
            if live.len() <= count {
                return;
            }
            let mut live_vec = live.iter().cloned().collect::<Vec<_>>();
            live_vec.sort_by_key(|var| (h.get(var), var.0));
            for var in live_vec.iter().skip(count) {
                if !spilled.contains(var) && h.is_live(var) {
                    spiller.add_spill(spill_pt, *var);
                }
                spilled.remove(var);
            }
            *live = live_vec.into_iter().take(count).collect();
        }

        let insts = self.method.block(block_ref).insts.clone();
        for i in 0..(insts.len() + 1) {
            // insts.len() + 1 because terminator counts as an "instruction"
            // The arguments of the instruction at i.
            let mut args = HashSet::new();
            let mut insert_args = |inst_ref: &mut InstRef| args.insert(*inst_ref);
            // Get the program point before the instruction at i and the result value, if any.
            let (prog_pt, result_value) = if i < insts.len() {
                let inst_ref = insts[i];
                match self.method.inst_mut(inst_ref) {
                    Inst::Phi(_) => continue, // Skip phi instructions as they have been taken care of.
                    inst => inst.for_each_inst_ref(&mut insert_args),
                };
                let result_value = match self.program.infer_inst_type(&self.method, inst_ref) {
                    // Instructions that return void don't have a result value.
                    // It would be a waste to assign a register to them.
                    Type::Void => None,
                    _ => Some(inst_ref),
                };
                (ProgPt::BeforeInst(inst_ref), result_value)
            } else {
                self.method
                    .block_mut(block_ref)
                    .term
                    .for_each_inst_ref(&mut insert_args);
                (ProgPt::BeforeTerm(block_ref), None)
            };
            let reloading = args.difference(&live).cloned().collect::<Vec<_>>();
            let h = self.spill_heuristic[&prog_pt].clone();

            let non_big_call = args.len() + (result_value.is_some() as usize) <= self.max_reg;

            if non_big_call {
                for var in reloading.iter() {
                    live.insert(*var);
                    spilled.insert(*var);
                }
                #[rustfmt::skip]
                limit(self, &mut live, &mut spilled, &h, &prog_pt, self.max_reg);
            } else {
                // No way to ensure all arguments (and result, if any) are in registers.
                // This happens for big function calls. But that needs to be
                // special-cased anyways, so life is good.
            }
            // Now we need to possibly spill another register to make room for the value.
            let post_pt = insts
                .get(i + 1)
                .cloned()
                .map_or(ProgPt::BeforeTerm(block_ref), ProgPt::BeforeInst);
            let without_res = self.max_reg - result_value.is_some() as usize;
            // The heuristic map based on which we make the spill decision is
            // the one for the program point AFTER the instruction.
            let mut h_post = self.spill_heuristic[&post_pt].clone();
            if non_big_call {
                // But modify it to prevent spilling of the arguments, since the
                // spill is technically still inserted before the instruction. Don't
                // want an argument to be spilled just to protect the result.
                for arg in &args {
                    h_post.insert(*arg, 0);
                }
            }
            #[rustfmt::skip]
            limit(self, &mut live, &mut spilled, &h_post, &prog_pt, without_res);
            if let Some(var) = result_value {
                live.insert(var);
            }
            for var in reloading {
                self.add_reload(&prog_pt, var);
            }
        }
        self.reg_out[block_ref.0] = live;
        self.spill_out[block_ref.0] = spilled;
    }

    /// Insertion of spills and reloads breaks the SSA form. This function
    /// restores it.
    fn reconstruct_ssa(&mut self) -> Method {
        let mut new_method = self.method.clone();
        // Identify variables that have been split and reloaded. These variables
        // have their SSA forms broken and we need to fix them.
        let mut var_to_def_blocks: HashMap<InstRef, HashSet<BlockRef>> = HashMap::new();
        // And create one spill slot for each spilled variable.
        // Sort keys for determinism.
        let mut spill_reloads_sorted = self.spill_reloads.keys().collect::<Vec<_>>();
        spill_reloads_sorted.sort_by_key(|prog_pt| match prog_pt {
            ProgPt::BeforeInst(inst) => {
                let block_pos = self.inst_to_block_pos[inst.0];
                (block_pos.0 .0, block_pos.1)
            }
            ProgPt::BeforeTerm(block) => (block.0, usize::MAX - 1),
            ProgPt::AfterTerm(block) => (block.0, usize::MAX),
        });
        for prog_pt in spill_reloads_sorted {
            let spill_reloads = &self.spill_reloads[prog_pt];
            let block_ref = match prog_pt {
                ProgPt::BeforeInst(inst) => self.inst_to_block_pos[inst.0].0,
                ProgPt::BeforeTerm(block) | ProgPt::AfterTerm(block) => *block,
            };
            for sr in spill_reloads {
                let inst_ref = match sr {
                    ReloadSpill::Reload(inst) | ReloadSpill::Spill(inst) => *inst,
                };
                self.spill_slots.entry(inst_ref).or_insert_with(|| {
                    let ty = self.program.infer_inst_type(&self.method, inst_ref);
                    let name = make_internal_ident(&format!("spill slot for {}", inst_ref));
                    new_method.next_stack_slot(ty, name)
                });
                let def_blocks = var_to_def_blocks.entry(inst_ref).or_default();
                def_blocks.insert(self.inst_to_block_pos[inst_ref.0].0);
                // Reloads are essentially redefinitions of the variable.
                if let ReloadSpill::Reload(_) = sr {
                    def_blocks.insert(block_ref);
                }
            }
        }

        let mut phi_spills_sorted = self.phi_spills.iter().collect::<Vec<_>>();
        phi_spills_sorted.sort_by_key(|inst_ref| inst_ref.0);
        for inst_ref in phi_spills_sorted {
            self.spill_slots.entry(*inst_ref).or_insert_with(|| {
                let ty = self.program.infer_inst_type(&self.method, *inst_ref);
                let name = make_internal_ident(&format!("spill slot for {}", inst_ref));
                new_method.next_stack_slot(ty, name)
            });
        }

        // Convert loads and spills into SSA instructions.
        let mut real_var: HashMap<InstRef, InstRef> = HashMap::new();
        for block in new_method.iter_block_refs() {
            let mut convert_spill_reloads =
                |m: &mut Method, prog_pt: &ProgPt, inst_after: Option<InstRef>| {
                    if let Some(spill_reloads) = self.spill_reloads.get(prog_pt) {
                        let mut prev: Option<InstRef> = None;
                        for sr in spill_reloads {
                            let var = match sr {
                                ReloadSpill::Reload(inst) | ReloadSpill::Spill(inst) => *inst,
                            };
                            let new_inst = match sr {
                                ReloadSpill::Reload(var) => {
                                    Inst::Load(Address::Local(self.spill_slots[var]))
                                }
                                ReloadSpill::Spill(var) => Inst::Store {
                                    addr: Address::Local(self.spill_slots[var]),
                                    value: *var,
                                },
                            };
                            let new_inst_ref = match prev {
                                Some(prev) => m.next_inst_after(block, new_inst, prev),
                                None => match inst_after {
                                    Some(inst_ref) => m.next_inst_before(block, new_inst, inst_ref),
                                    None => m.next_inst(block, new_inst),
                                },
                            };
                            if let Some(original_annotation) = m.get_inst_annotation(&var).cloned()
                            {
                                let annotation_mut = m.annotate_inst_mut(new_inst_ref);
                                annotation_mut.str = Some(match sr {
                                    ReloadSpill::Reload(_) => "reload".to_string(),
                                    ReloadSpill::Spill(_) => "spill".to_string(),
                                });
                                annotation_mut.children = vec![original_annotation];
                            }
                            prev = Some(new_inst_ref);
                            if let ReloadSpill::Reload(var) = sr {
                                real_var.insert(new_inst_ref, *var);
                            }
                        }
                    }
                };
            for inst_ref in new_method.block(block).insts.clone() {
                convert_spill_reloads(
                    &mut new_method,
                    &ProgPt::BeforeInst(inst_ref),
                    Some(inst_ref),
                );
            }
            convert_spill_reloads(&mut new_method, &ProgPt::BeforeTerm(block), None);
        }

        let predecessors = predecessors(&new_method);

        fn find_def(
            method: &mut Method,
            usage: (ProgPt, BlockRef),
            var: InstRef,
            dominance_frontier: &HashSet<BlockRef>,
            dom: &Dominance,
            real_var: &mut HashMap<InstRef, InstRef>,
            predecessors: &[HashSet<BlockRef>],
        ) -> InstRef {
            let (usage_pt, usage_block) = usage;
            let mut processing = match usage_pt {
                ProgPt::BeforeInst(_) => false,
                ProgPt::BeforeTerm(_) | ProgPt::AfterTerm(_) => true,
            };
            let mut block = usage_block;
            loop {
                for inst_ref in method.block(block).insts.iter().rev() {
                    if processing && real_var.get(inst_ref).unwrap_or(inst_ref) == &var {
                        return *inst_ref;
                    }
                    if usage_pt == ProgPt::BeforeInst(*inst_ref) {
                        processing = true;
                    }
                }
                if dominance_frontier.contains(&block) {
                    // At dominance frontier, need to insert phi
                    let phi_inst = method.next_inst_prepend(block, Inst::Phi(HashMap::new()));
                    real_var.insert(phi_inst, var);
                    let mut map = HashMap::new();
                    for pred in predecessors[block.0].iter() {
                        #[rustfmt::skip]
                        map.insert(
                            *pred,
                            find_def(method, (ProgPt::AfterTerm(*pred), *pred), var,
                                dominance_frontier, dom, real_var, predecessors),
                        );
                    }
                    let Inst::Phi(old_map) = method.inst_mut(phi_inst) else {
                        unreachable!();
                    };
                    *old_map = map;
                    return phi_inst;
                }
                if block == method.entry {
                    unreachable!();
                }
                block = dom.immediate_dominator(block)
            }
        }

        // Alg. 4.1 in Hack's paper.
        for (var, def_blocks) in var_to_def_blocks {
            // Compute iterated dominance frontier
            let mut worklist = def_blocks.iter().cloned().collect::<Vec<_>>();
            let mut visited = worklist.iter().cloned().collect::<HashSet<_>>();
            let mut dominance_frontier = HashSet::new();
            while let Some(block) = worklist.pop() {
                for frontier in self.dom.dominance_frontier(block) {
                    dominance_frontier.insert(*frontier);
                    if visited.insert(*frontier) {
                        worklist.push(*frontier);
                    }
                }
            }
            for block in new_method.iter_block_refs() {
                macro_rules! resolve_uses {
                    ($base:expr, $prog_pt:expr) => {{
                        let mut used = false;
                        ($base).for_each_inst_ref(|inst| {
                            if *inst == var {
                                used = true;
                            }
                        });
                        if used {
                            let resolved = find_def(
                                &mut new_method,
                                ($prog_pt, block),
                                var,
                                &dominance_frontier,
                                &self.dom,
                                &mut real_var,
                                &predecessors,
                            );
                            ($base).for_each_inst_ref(|inst| {
                                if *inst == var {
                                    *inst = resolved;
                                }
                            });
                        }
                    }};
                }
                for inst_ref in new_method.block(block).insts.clone() {
                    let inst_mut = new_method.inst_mut(inst_ref);
                    match inst_mut {
                        Inst::Phi(map) => {
                            // This is so ugly. I fought the borrow checker so hard...
                            let mut new_map = map.clone();
                            for (block, src) in new_map.iter_mut() {
                                if *src == var {
                                    *src = find_def(
                                        &mut new_method,
                                        (ProgPt::AfterTerm(*block), *block),
                                        var,
                                        &dominance_frontier,
                                        &self.dom,
                                        &mut real_var,
                                        &predecessors,
                                    );
                                }
                            }
                            let Inst::Phi(map) = new_method.inst_mut(inst_ref) else {
                                unreachable!()
                            };
                            *map = new_map;
                        }
                        _ => resolve_uses!(
                            new_method.inst_mut(inst_ref),
                            ProgPt::BeforeInst(inst_ref)
                        ),
                    }
                }
                resolve_uses!(new_method.block_mut(block).term, ProgPt::BeforeTerm(block))
            }
        }

        // Finally, convert Phis marked in phi_spills to PhiMems
        for inst_ref in self.phi_spills.iter() {
            let inst_mut = new_method.inst_mut(*inst_ref);
            let map = match inst_mut {
                Inst::Phi(map) => map.clone(),
                _ => unreachable!(),
            };
            let mem_map = map
                .into_iter()
                .map(|(block, var)| {
                    let var = real_var.get(&var).unwrap_or(&var);
                    let spill_slot = self.spill_slots[&var];
                    (block, spill_slot)
                })
                .collect::<HashMap<_, _>>();
            *inst_mut = Inst::PhiMem {
                src: mem_map,
                dst: self.spill_slots[&real_var.get(inst_ref).unwrap_or(inst_ref)],
            }
        }

        new_method
    }

    // Dump the method to a graphviz dot file, for debugging.
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
            block_label.push('\n');
            // block_label.push_str(&format!(
            //     "\n; reg in: {:?}\n; spill in: {:?}\n",
            //     self.reg_in[block_ref.0], self.spill_in[block_ref.0]
            // ));
            let mut insts = Table::new();
            let add_spill_loads = |spiller: &Spiller<'a>, insts: &mut Table, prog_pt: ProgPt| {
                // if let Some(h) = spiller.spill_heuristic.get(&prog_pt) {
                //     insts.add_row(TableRow::new().add(";").add("").add(format!("{}", h)));
                // }
                if let Some(reload_spills) = spiller.spill_reloads.get(&prog_pt) {
                    for rs in reload_spills {
                        let text = match rs {
                            ReloadSpill::Reload(inst) => format!("reload {}", inst),
                            ReloadSpill::Spill(inst) => format!("spill  {}", inst),
                        };
                        insts.add_row(TableRow::new().add(" ").add("").add(text));
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
                if self.phi_spills.contains(inst) {
                    row = row.add(" (phi-spill)");
                }
                insts.add_row(row);
            }
            add_spill_loads(self, &mut insts, ProgPt::BeforeTerm(block_ref));
            insts.add_row(TableRow::new().add(" ").add("").add(&block.term));
            add_spill_loads(self, &mut insts, ProgPt::AfterTerm(block_ref));
            block_label.push_str(format!("{}", insts).as_str());
            // block_label.push_str(&format!(
            //     "; reg out: {:?}\n; spill out: {:?}\n",
            //     self.reg_out[block_ref.0], self.spill_out[block_ref.0]
            // ));
            // Escape newlines in the block label and replace to \l to left-align.
            let block_label = format!("{:?}", block_label).replace("\\n", "\\l ");
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
