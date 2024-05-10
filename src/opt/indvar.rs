//! Induction variable analysis, elimination, and strength reduction.
//!
//! Generally, the multiplier, increment, and offset of an induction variable
//! can be any value as long as it's a loop invariant. This implementation
//! restricts them to constants. For the following reasons:
//! - Easier to code
//! - Works well enough for common loops
//! - This can go arbitrarily deep into the abyss of Scalar Evolution Analysis.
//!   Let's just stop at constant induction variables.

use std::{cmp::Reverse, collections::HashMap};

use crate::inter::{
    constant::Const,
    ir::{BlockRef, Inst, InstRef, Method},
};

use super::{
    dom::compute_dominance,
    loop_utils::{Loop, LoopAnalysis},
};

#[derive(Debug, Clone, Copy)]
pub struct BaseIndVar {
    pub inst_ref: InstRef,
    pub delta: i64,
}

#[derive(Debug, Clone, Copy)]
pub struct IndVar {
    pub block_ref: BlockRef,
    pub base: BaseIndVar,
    pub mult: i64,
    pub offset: i64,
}

#[derive(Debug)]
pub struct IndVars {
    base: HashMap<InstRef, BaseIndVar>,
    all: HashMap<InstRef, IndVar>,
}

impl Loop {
    pub fn find_induction_variables(&self, method: &Method, dom_tree: &[Vec<BlockRef>]) -> IndVars {
        let mut ret = IndVars {
            base: HashMap::new(),
            all: HashMap::new(),
        };
        'next_phi: for phi_ref in method.phis(self.header) {
            let mut delta: Option<i64> = None;
            let Inst::Phi(map) = method.inst(phi_ref) else {
                unreachable!();
            };
            for (src_block, src_inst_ref) in map.iter() {
                if !self.body.contains(src_block) {
                    continue;
                }
                let (lhs, rhs, sign) = match method.inst(*src_inst_ref) {
                    Inst::Add(lhs, rhs) if *lhs == phi_ref || *rhs == phi_ref => (lhs, rhs, 1),
                    Inst::Sub(lhs, rhs) if *lhs == phi_ref => (lhs, rhs, -1),
                    _ => continue 'next_phi,
                };
                let other = if *lhs == phi_ref { *rhs } else { *lhs };
                match method.inst(other) {
                    Inst::LoadConst(Const::Int(n)) => {
                        delta = match (delta, *n * sign) {
                            (None, n) => Some(n),
                            (Some(inc), n) if inc == n => Some(n),
                            _ => continue 'next_phi,
                        };
                    }
                    _ => continue 'next_phi,
                }
            }
            let delta = delta.unwrap();
            let base_var = BaseIndVar {
                inst_ref: phi_ref,
                delta,
            };
            ret.all.insert(
                phi_ref,
                IndVar {
                    block_ref: self.header,
                    base: base_var,
                    mult: 1,
                    offset: 0,
                },
            );
            ret.base.insert(phi_ref, base_var);
        }

        fn dfs(
            method: &Method,
            block_ref: BlockRef,
            loop_: &Loop,
            dom_tree: &[Vec<BlockRef>],
            ind_vars: &mut HashMap<InstRef, IndVar>,
        ) {
            for inst_ref in method.block(block_ref).insts.iter().copied() {
                macro_rules! get_const {
                    ($inst_ref:expr) => {
                        match method.inst($inst_ref) {
                            Inst::LoadConst(Const::Int(x)) => *x,
                            _ => continue,
                        }
                    };
                }
                macro_rules! insert {
                    ($base:expr,$mult:expr,$offset:expr) => {
                        ind_vars.insert(
                            inst_ref,
                            IndVar {
                                block_ref,
                                base: $base,
                                mult: $mult,
                                offset: $offset,
                            },
                        );
                    };
                }
                match method.inst(inst_ref) {
                    Inst::Copy(var) if ind_vars.contains_key(var) => {
                        ind_vars.insert(inst_ref, ind_vars[var]);
                    }
                    Inst::Add(lhs, rhs) => match (ind_vars.get(lhs), ind_vars.get(rhs)) {
                        (Some(lhs), Some(rhs)) if lhs.base.inst_ref == rhs.base.inst_ref => {
                            insert!(lhs.base, lhs.mult + rhs.mult, lhs.offset + rhs.offset);
                        }
                        (l @ Some(x), None) | (l @ None, Some(x)) => {
                            let offset = get_const!(if l.is_some() { *rhs } else { *lhs });
                            insert!(x.base, x.mult, x.offset + offset);
                        }
                        _ => continue,
                    },
                    Inst::Sub(lhs, rhs) => match (ind_vars.get(lhs), ind_vars.get(rhs)) {
                        (Some(lhs), Some(rhs)) if lhs.base.inst_ref == rhs.base.inst_ref => {
                            insert!(lhs.base, lhs.mult - rhs.mult, lhs.offset - rhs.offset);
                        }
                        (l @ Some(x), None) | (l @ None, Some(x)) => {
                            let (other, sign) = match l {
                                Some(_) => (*rhs, 1),
                                None => (*lhs, -1),
                            };
                            let offset = get_const!(other);
                            insert!(x.base, x.mult * sign, (x.offset - offset) * sign);
                        }
                        _ => continue,
                    },
                    Inst::Mul(lhs, rhs) => {
                        let (iv, mult) = if let Some(lhs) = ind_vars.get(lhs) {
                            (lhs, get_const!(*rhs))
                        } else if let Some(rhs) = ind_vars.get(rhs) {
                            (rhs, get_const!(*lhs))
                        } else {
                            continue;
                        };
                        insert!(iv.base, iv.mult * mult, iv.offset * mult);
                    }
                    _ => continue,
                }
            }
            for child in dom_tree[block_ref.0]
                .iter()
                .copied()
                .filter(|b| loop_.body.contains(b))
            {
                dfs(method, child, loop_, dom_tree, ind_vars);
            }
        }
        dfs(method, self.header, self, dom_tree, &mut ret.all);
        ret
    }
}

pub fn reduce_induction_variables(method: &mut Method) {
    let mut loops = LoopAnalysis::new(method);

    let mut all_loops = method
        .iter_block_refs()
        .filter_map(|b| match loops.get_loop(b) {
            Some(l) if l.borrow().header == b => Some(l),
            _ => None,
        })
        .collect::<Vec<_>>();

    // Sort loops from innermost to outermost. This way reduced induction
    // variables get a chance to be lifted further up.
    all_loops.sort_by_cached_key(|l| Reverse(l.borrow().depth()));

    let mut dom_tree = compute_dominance(method).dominator_tree();

    for loop_rc in all_loops {
        let ind_var = loop_rc.borrow().find_induction_variables(method, &dom_tree);
        // Do we have interesting induction variables?
        let is_interesting = |inst_ref: InstRef, ind_var: &IndVar| {
            // We only care about induction variables that are not trivial.
            if ind_var.mult != 1 {
                true
            } else {
                match method.inst(inst_ref) {
                    Inst::Phi(_) => false,
                    Inst::Add(lhs, rhs) if *lhs == ind_var.base.inst_ref => {
                        !matches!(method.inst(*rhs), Inst::LoadConst(Const::Int(offset)) if *offset == ind_var.offset)
                    }
                    Inst::Add(lhs, rhs) if *rhs == ind_var.base.inst_ref => {
                        !matches!(method.inst(*lhs), Inst::LoadConst(Const::Int(offset)) if *offset == ind_var.offset)
                    }
                    Inst::Copy(var) if *var == ind_var.base.inst_ref => {
                        assert!(ind_var.offset == 0);
                        false
                    }
                    _ => true,
                }
            }
        };
        let interesting = ind_var
            .all
            .iter()
            .filter(|(inst_ref, ind_var)| is_interesting(**inst_ref, ind_var))
            .map(|(inst_ref, ind_var)| (*inst_ref, *ind_var))
            .collect::<HashMap<_, _>>();
        if interesting.is_empty() {
            continue;
        }
        let header_ref = loop_rc.borrow().header;
        let prev_n_blocks = method.n_blocks();
        let preheader_ref = loops.get_or_insert_pre_header(method, header_ref);

        if method.n_blocks() > prev_n_blocks {
            // A new block is inserted, so we need to recompute the dominance tree.
            dom_tree = compute_dominance(method).dominator_tree();
        }

        // Optimize!
        let mut ind_var_by_mult: HashMap<i64, Vec<(InstRef, IndVar)>> = HashMap::new();
        for (inst_ref, ind_var) in interesting {
            ind_var_by_mult
                .entry(ind_var.mult)
                .or_default()
                .push((inst_ref, ind_var));
        }
        // Pick a representative for each multiplier to be initialized out of the loop
        let mut rep: HashMap<i64, (InstRef, i64)> = HashMap::new();
        let loop_ = loop_rc.borrow();
        for (mult, vars) in ind_var_by_mult.iter() {
            if *mult == 1 {
                // No need to initialize the base induction variable.
                continue;
            }
            let (inst_ref, ind_var) = vars
                .iter()
                .find(|(_, ind_var)| ind_var.offset == 0) // Prefer offset 0, saves us an add in the preheader.
                .unwrap_or_else(|| &vars[0]);
            let base_init_val = match method.inst(ind_var.base.inst_ref) {
                Inst::Phi(map) => map[&preheader_ref],
                _ => unreachable!(),
            };
            let mut init_ref = if ind_var.mult != -1 {
                let mult_ref =
                    method.next_inst(preheader_ref, Inst::LoadConst(Const::Int(ind_var.mult)));
                method.next_inst(preheader_ref, Inst::Mul(base_init_val, mult_ref))
            } else {
                method.next_inst(preheader_ref, Inst::Neg(base_init_val))
            };
            if ind_var.offset != 0 {
                let offset_ref =
                    method.next_inst(preheader_ref, Inst::LoadConst(Const::Int(ind_var.offset)));
                init_ref = method.next_inst(preheader_ref, Inst::Add(init_ref, offset_ref));
            }
            let delta_ref = method.next_inst(
                preheader_ref,
                Inst::LoadConst(Const::Int(ind_var.base.delta * *mult)),
            );
            // Building the phi map for the preheader.
            let var_ref = method.next_inst_prepend(header_ref, Inst::Phi(HashMap::new()));
            rep.insert(*mult, (var_ref, ind_var.offset));
            if let Some(annotation) = method.get_inst_annotation(inst_ref) {
                *method.annotate_inst_mut(var_ref) = annotation.clone();
            }
            let mut map: HashMap<BlockRef, InstRef> = HashMap::from([(preheader_ref, init_ref)]);
            for cont_ref in loop_.continue_.iter().copied() {
                map.insert(
                    cont_ref,
                    method.next_inst(cont_ref, Inst::Add(var_ref, delta_ref)),
                );
            }
            match method.inst_mut(var_ref) {
                Inst::Phi(old_map) => *old_map = map,
                _ => unreachable!(),
            }
        }

        for (mult, vars) in ind_var_by_mult {
            let (rep, rep_offset) = if mult == 1 {
                (vars[0].1.base.inst_ref, 0)
            } else {
                rep[&mult]
            };
            for (inst_ref, ind_var) in vars {
                if ind_var.offset == rep_offset {
                    *method.inst_mut(inst_ref) = Inst::Copy(rep);
                } else {
                    let offset_ref = method.next_inst_before(
                        ind_var.block_ref,
                        Inst::LoadConst(Const::Int(ind_var.offset - rep_offset)),
                        inst_ref,
                    );
                    *method.inst_mut(inst_ref) = Inst::Add(rep, offset_ref);
                }
            }
        }
    }
}
