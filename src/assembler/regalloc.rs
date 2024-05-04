use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use crate::{
    inter::{
        ir::{BlockRef, Inst, InstRef, ProgPt, Program},
        types::Type,
    },
    opt::for_each_successor,
};

use super::{LoweredMethod, NonMaterializedArgMapExt};

pub struct RegAllocator<'a> {
    program: &'a Program,
    l: &'a mut LoweredMethod,
    live_at: HashMap<ProgPt, im::HashSet<InstRef>>,
    reg: HashMap<InstRef, usize>,
}

impl<'a> RegAllocator<'a> {
    pub fn new(program: &'a Program, method: &'a mut LoweredMethod) -> Self {
        Self {
            program,
            l: method,
            live_at: HashMap::new(),
            reg: HashMap::new(),
        }
    }

    fn analyze_liveness(&mut self) {
        let postorder = self.l.dom.postorder(self.l.method.entry);
        let mut q = VecDeque::new();
        let mut in_queue = vec![false; self.l.method.n_blocks()];
        for block in postorder {
            q.push_back(block);
            in_queue[block.0] = true;
        }
        while let Some(block) = q.pop_front() {
            in_queue[block.0] = false;
            if self.analyze_liveness_for_block(block) {
                for &p in self.l.predecessors[block.0].iter() {
                    if !in_queue[p.0] {
                        q.push_back(p);
                        in_queue[p.0] = true;
                    }
                }
            }
        }
    }

    fn analyze_liveness_for_block(&mut self, block_ref: BlockRef) -> bool {
        let method = &mut self.l.method;
        let first_pt = method.first_prog_pt(block_ref);
        let old_live = self.live_at.get(&first_pt).cloned();
        let mut live: im::HashSet<InstRef> = im::HashSet::new();
        for_each_successor(method, block_ref, |succ| {
            if let Some(live_succ) = self.live_at.get(&method.first_prog_pt(succ)) {
                live.extend(live_succ.iter().cloned());
            }
            for phi in method.phis(succ) {
                let Inst::Phi(map) = method.inst(phi) else {
                    unreachable!();
                };
                live.remove(&phi);
                let var = map[&block_ref];
                live.insert(var);
            }
        });
        self.live_at
            .insert(ProgPt::AfterTerm(block_ref), live.clone());
        method
            .block_mut(block_ref)
            .term
            .for_each_inst_ref(|inst| live.insert(*inst));
        self.live_at
            .insert(ProgPt::BeforeTerm(block_ref), live.clone());
        for inst_ref in method.block(block_ref).insts.clone().into_iter().rev() {
            match method.inst_mut(inst_ref) {
                Inst::Phi(_) | Inst::PhiMem { .. } => break,
                inst => {
                    live.remove(&inst_ref);
                    inst.for_each_inst_ref(|arg_ref| {
                        if self.l.nm_args.is_materialized(inst_ref, *arg_ref) {
                            live.insert(*arg_ref);
                        }
                    });
                    self.live_at
                        .insert(ProgPt::BeforeInst(inst_ref), live.clone());
                }
            }
        }
        old_live != Some(live)
    }

    pub fn allocate(mut self) {
        self.analyze_liveness();
        self.color_recursive(self.l.method.entry);
        self.l.live_at = self.live_at;
        self.l.reg = self.reg;
    }

    fn color_recursive(&mut self, block_ref: BlockRef) {
        // println!("Coloring block {}:{}", self.l.method.name.inner, block_ref);
        let mut used: HashSet<usize> = HashSet::new();
        // Use BTreeSet to keep registers ordered, and the execution deterministic.
        let mut free = (0..self.l.max_reg).collect::<BTreeSet<_>>();
        let method = &mut self.l.method;
        let first_pt = method.first_prog_pt(block_ref);
        // println!("  live in: {:?}", self.live_at[&first_pt]);
        for var in self.live_at[&first_pt].iter() {
            if let Some(reg) = self.reg.get(var) {
                used.insert(*reg);
                free.remove(reg);
            } else {
                // Live-in but not yet assigned a register, must be a phi.
            }
        }
        let insts = method.block(block_ref).insts.clone();
        for (i, inst_ref) in insts.iter().enumerate() {
            let next_pt = match method.inst(*inst_ref) {
                Inst::Phi(_) | Inst::PhiMem { .. } => first_pt,
                _ if i + 1 < insts.len() => ProgPt::BeforeInst(insts[i + 1]),
                _ => ProgPt::BeforeTerm(block_ref),
            };
            match method.inst_mut(*inst_ref) {
                Inst::Phi(_) | Inst::PhiMem { .. } => {}
                inst => inst.for_each_inst_ref(|inst| {
                    if !self.live_at[&next_pt].contains(inst) {
                        let in_mem = self
                            .l
                            .nm_args
                            .get(inst_ref)
                            .map_or(false, |mem| mem.contains(inst));
                        if !in_mem {
                            if let Some(reg) = self.reg.get(inst) {
                                // println!("  freeing register {} from {}", reg, inst);
                                used.remove(reg);
                                free.insert(*reg);
                            }
                        }
                    }
                }),
            }
            // println!("At {}: {:?}", inst_ref, self.live_at[&next_pt]);
            if let Type::Void = self.program.infer_inst_type(method, *inst_ref) {
                continue; // No need to allocate registers for void instructions.
            }
            if !self.live_at[&next_pt].contains(inst_ref) {
                continue; // No need to allocate registers for dead instructions.
            }
            let reg = free.iter().next().copied().expect("ran out of registers");
            used.insert(reg);
            free.remove(&reg);
            // println!(
            //     "  assigned register {} to {} {:?} {:?}",
            //     reg, inst_ref, used, free
            // );
            self.reg.insert(*inst_ref, reg);
        }
        for dominates in self.l.dom_tree[block_ref.0].clone() {
            self.color_recursive(dominates);
        }
    }
}
