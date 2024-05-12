//! Induction variable analysis, elimination, and strength reduction.
//!
//! Generally, the multiplier, increment, and offset of an induction variable
//! can be any value as long as it's a loop invariant. This implementation
//! restricts them to constants. For the following reasons:
//! - Easier to code
//! - Works well enough for common loops
//! - This can go arbitrarily deep into the abyss of Scalar Evolution Analysis.
//!   Let's just stop at constant induction variables.

use std::{
    cmp::Reverse,
    collections::{HashMap, HashSet},
    rc::Rc,
};

use crate::{
    inter::{
        constant::Const,
        ir::{Address, BlockRef, Inst, InstRef, Method},
    },
    opt::poly::Poly,
};

use super::{
    dom::compute_dominance,
    loop_utils::{Loop, LoopAnalysis},
};

#[derive(Debug, Clone)]
pub struct BaseIndVar {
    pub inst_ref: InstRef,
    pub delta: Poly,
}

#[derive(Debug, Clone)]
pub struct IndVar {
    pub block_ref: BlockRef,
    pub base: Rc<BaseIndVar>,
    pub mult: Poly,
    pub offset: Poly,
}

#[derive(Debug)]
pub struct IndVars {
    base: HashMap<InstRef, Rc<BaseIndVar>>,
    all: HashMap<InstRef, IndVar>,
}

struct IndVarAnalysis {
    inst_to_block: HashMap<InstRef, BlockRef>,
    inst_to_poly: im::HashMap<InstRef, Poly>,
    dom_tree: Vec<Vec<BlockRef>>,
}

impl IndVarAnalysis {
    pub fn init(method: &Method) -> Self {
        let mut inst_to_block = HashMap::new();
        let mut inst_to_poly = im::HashMap::new();
        let dom = compute_dominance(method);
        for block_ref in dom.preorder(method.entry) {
            for inst_ref in method.block(block_ref).insts.iter().copied() {
                inst_to_block.insert(inst_ref, block_ref);
                inst_to_poly.insert(inst_ref, Poly::from_inst(method, inst_ref, &inst_to_poly));
            }
        }
        Self {
            inst_to_block,
            inst_to_poly,
            dom_tree: dom.dominator_tree(),
        }
    }

    fn is_inst_invariant(&self, inst_ref: InstRef, loop_: &Loop, method: &Method) -> bool {
        let block_ref = self.inst_to_block[&inst_ref];
        match method.inst(inst_ref) {
            Inst::LoadConst(_) => true,
            Inst::Load(addr) | Inst::LoadArray { addr, .. } => {
                !loop_.body.contains(&block_ref) // The load is not in the loop.
                    || (!loop_.tainted_addr.contains(addr) // We haven't tainted the address in the loop.
                        // either a local address or global but there are no calls in the loop.
                    && (matches!(addr, Address::Local(_)) || !loop_.has_call))
            }
            Inst::Phi(_) => !loop_.body.contains(&block_ref),
            inst => {
                if inst.has_side_effects() {
                    return false;
                }
                if !loop_.body.contains(&block_ref) {
                    return true;
                }
                let mut invariant = true;
                inst.for_each_inst_ref_copied(|arg_ref| {
                    invariant &= self.is_inst_invariant(arg_ref, loop_, method);
                });
                invariant
            }
        }
    }

    fn materialize_inst_invariant(
        &mut self,
        inst_ref: InstRef,
        block_ref: BlockRef,
        loop_: &Loop,
        method: &mut Method,
    ) -> InstRef {
        if !loop_.body.contains(&self.inst_to_block[&inst_ref]) {
            return inst_ref;
        }
        let mut inst = method.inst(inst_ref).clone();
        inst.for_each_inst_ref(|arg_ref| {
            *arg_ref = self.materialize_inst_invariant(*arg_ref, block_ref, loop_, method);
        });
        let inst_ref = method.next_inst(block_ref, inst);
        self.on_new_inst(method, block_ref, inst_ref);
        inst_ref
    }

    fn is_poly_invariant(&self, poly: &Poly, loop_: &Loop, method: &Method) -> bool {
        let mut inst_involved: HashSet<InstRef> = HashSet::new();
        for (term, _) in poly.terms() {
            for inst_ref in term.iter() {
                inst_involved.insert(*inst_ref);
            }
        }
        inst_involved
            .iter()
            .all(|inst_ref| self.is_inst_invariant(*inst_ref, loop_, method))
    }

    fn pretty_print_poly(&self, poly: &Poly, method: &Method) -> String {
        let mut ret = String::new();
        let mut inst_to_str: HashMap<InstRef, String> = HashMap::new();
        for (term, _) in poly.terms() {
            for inst_ref in term.iter() {
                if !inst_to_str.contains_key(inst_ref) {
                    let str = method.get_inst_annotation(inst_ref).and_then(|a| {
                        a.ident
                            .as_ref()
                            .map(|i| i.inner.to_string())
                            .or_else(|| a.str.clone())
                    });
                    let maybe_parenthesize = |str: String| {
                        if str.contains(' ') || str.contains('*') {
                            format!("({})", str)
                        } else {
                            str
                        }
                    };
                    let pretty_print = if let Some(str) = str {
                        maybe_parenthesize(str)
                    } else if let Inst::LoadConst(c) = method.inst(*inst_ref) {
                        c.to_string()
                    } else {
                        let p = &self.inst_to_poly[inst_ref];
                        if p.terms().keys().any(|term| term.contains(inst_ref)) {
                            format!("{:?}", inst_ref)
                        } else {
                            maybe_parenthesize(self.pretty_print_poly(p, method))
                        }
                    };
                    inst_to_str.insert(*inst_ref, pretty_print);
                }
            }
        }
        let mut first = true;
        if poly.constant() != 0 {
            ret.push_str(&poly.constant().to_string());
            first = false;
        }
        for (term, c) in poly.terms() {
            if !first {
                ret.push_str(if *c >= 0 { " + " } else { " - " });
            } else if *c < 0 {
                ret.push('-');
            }
            first = false;
            if c.abs() != 1 {
                ret.push_str(&format!("{} * ", c.abs()));
            }
            let term_strs = term
                .iter()
                .map(|inst_ref| inst_to_str[inst_ref].clone())
                .collect::<Vec<_>>();
            ret.push_str(&term_strs.join(" * "));
        }
        ret
    }

    fn materialize_poly_invariant(
        &mut self,
        poly: &Poly,
        block_ref: BlockRef,
        loop_: &Loop,
        method: &mut Method,
    ) -> InstRef {
        if poly.is_constant() {
            let const_ref =
                method.next_inst(block_ref, Inst::LoadConst(Const::Int(poly.constant())));
            self.on_new_inst(method, block_ref, const_ref);
            return const_ref;
        }
        // Find the term x that appears in the most terms.
        // See https://dl.acm.org/doi/pdf/10.1145/980175.980179
        // "Greedy Algorithms for Optimizing Multivariate Horner Schemes"
        let mut appear_count: HashMap<InstRef, usize> = HashMap::new();
        for (term, _) in poly.terms() {
            let mut terms = term.iter().copied().collect::<Vec<_>>();
            terms.dedup(); // Terms are sorted, so we can dedup.
            for term_ref in terms {
                *appear_count.entry(term_ref).or_default() += 1;
            }
        }
        let x = appear_count
            .iter()
            .max_by_key(|(_, count)| *count)
            .map(|(x, _)| *x)
            .unwrap();
        let mut with_x = Poly::from_int(0);
        let mut without_x = Poly::from_int(poly.constant());
        for (term, c) in poly.terms() {
            if let Some(x_pos) = term.iter().position(|t| *t == x) {
                if term.len() == 1 {
                    *with_x.constant_mut() += c;
                } else {
                    let mut term = term.clone();
                    term.remove(x_pos);
                    with_x.terms_mut().insert(term, *c);
                }
            } else {
                without_x.terms_mut().insert(term.clone(), *c);
            }
        }
        let with_x_ref = self.materialize_poly_invariant(&with_x, block_ref, loop_, method);
        let x_ref = self.materialize_inst_invariant(x, block_ref, loop_, method);
        let prod_ref = method.next_inst(block_ref, Inst::Mul(x_ref, with_x_ref));
        self.on_new_inst(method, block_ref, prod_ref);
        if without_x.is_zero() {
            method.annotate_inst_mut(prod_ref).str = Some(self.pretty_print_poly(poly, method));
            prod_ref
        } else {
            let without_x_ref =
                self.materialize_poly_invariant(&without_x, block_ref, loop_, method);
            let sum_ref = method.next_inst(block_ref, Inst::Add(prod_ref, without_x_ref));
            self.on_new_inst(method, block_ref, sum_ref);
            method.annotate_inst_mut(sum_ref).str = Some(self.pretty_print_poly(poly, method));
            sum_ref
        }
    }

    pub fn find_induction_variables(&self, loop_: &Loop, method: &Method) -> IndVars {
        let mut ret = IndVars {
            base: HashMap::new(),
            all: HashMap::new(),
        };
        'next_phi: for phi_ref in method.phis(loop_.header) {
            let mut delta: Option<Poly> = None;
            let Inst::Phi(map) = method.inst(phi_ref) else {
                unreachable!();
            };
            let phi_val = &self.inst_to_poly[&phi_ref];
            for (src_block, src_inst_ref) in map.iter() {
                if !loop_.body.contains(src_block) {
                    continue;
                }
                let Some(maybe_delta) = self.inst_to_poly[src_inst_ref].sub(phi_val) else {
                    continue 'next_phi;
                };
                if !self.is_poly_invariant(&maybe_delta, loop_, method) {
                    continue 'next_phi;
                }
                delta = match delta {
                    None => Some(maybe_delta),
                    Some(delta) if delta == maybe_delta => Some(delta),
                    _ => continue 'next_phi,
                };
            }
            let delta = delta.unwrap();
            let base_var = Rc::new(BaseIndVar {
                inst_ref: phi_ref,
                delta,
            });
            ret.all.insert(
                phi_ref,
                IndVar {
                    block_ref: loop_.header,
                    base: base_var.clone(),
                    mult: Poly::from_int(1),
                    offset: Poly::from_int(0),
                },
            );
            ret.base.insert(phi_ref, base_var);
        }

        fn dfs(
            iv: &IndVarAnalysis,
            method: &Method,
            block_ref: BlockRef,
            loop_: &Loop,
            dom_tree: &[Vec<BlockRef>],
            ind_vars: &mut HashMap<InstRef, IndVar>,
        ) {
            for inst_ref in method.block(block_ref).insts.iter().copied() {
                macro_rules! insert {
                    ($base:expr,$mult:expr,$offset:expr) => {
                        ind_vars.insert(
                            inst_ref,
                            IndVar {
                                block_ref,
                                base: $base.clone(),
                                mult: $mult,
                                offset: $offset,
                            },
                        );
                    };
                }
                match method.inst(inst_ref) {
                    Inst::Copy(var) if ind_vars.contains_key(var) => {
                        ind_vars.insert(inst_ref, ind_vars[var].clone());
                    }
                    Inst::Add(lhs, rhs) => match (ind_vars.get(lhs), ind_vars.get(rhs)) {
                        (Some(lhs), Some(rhs)) if lhs.base.inst_ref == rhs.base.inst_ref => {
                            if let (Some(new_mult), Some(new_offset)) =
                                (lhs.mult.add(&rhs.mult), lhs.offset.add(&rhs.offset))
                            {
                                insert!(lhs.base, new_mult, new_offset);
                            }
                        }
                        (l @ Some(x), None) | (l @ None, Some(x)) => {
                            let offset = &iv.inst_to_poly[if l.is_some() { rhs } else { lhs }];
                            if iv.is_poly_invariant(offset, loop_, method) {
                                if let Some(new_offset) = x.offset.add(offset) {
                                    insert!(x.base, x.mult.clone(), new_offset);
                                }
                            }
                        }
                        _ => continue,
                    },
                    Inst::Sub(lhs, rhs) => match (ind_vars.get(lhs), ind_vars.get(rhs)) {
                        (Some(lhs), Some(rhs)) if lhs.base.inst_ref == rhs.base.inst_ref => {
                            if let (Some(new_mult), Some(new_offset)) =
                                (lhs.mult.sub(&rhs.mult), lhs.offset.sub(&rhs.offset))
                            {
                                insert!(lhs.base, new_mult, new_offset);
                            }
                        }
                        (Some(lhs), None) => {
                            let offset = &iv.inst_to_poly[rhs];
                            if iv.is_poly_invariant(offset, loop_, method) {
                                if let Some(new_offset) = lhs.offset.sub(offset) {
                                    insert!(lhs.base, lhs.mult.clone(), new_offset);
                                }
                            }
                        }
                        (None, Some(rhs)) => {
                            let offset = &iv.inst_to_poly[lhs];
                            if iv.is_poly_invariant(offset, loop_, method) {
                                if let Some(new_offset) = offset.sub(&rhs.offset) {
                                    let new_mult = rhs.mult.mul(&Poly::from_int(-1)).unwrap();
                                    insert!(rhs.base, new_mult, new_offset);
                                }
                            }
                        }
                        _ => continue,
                    },
                    Inst::Mul(lhs, rhs) => {
                        let (iv_, mult) = if let Some(lhs) = ind_vars.get(lhs) {
                            (lhs, &iv.inst_to_poly[rhs])
                        } else if let Some(rhs) = ind_vars.get(rhs) {
                            (rhs, &iv.inst_to_poly[lhs])
                        } else {
                            continue;
                        };
                        if iv.is_poly_invariant(mult, loop_, method) {
                            if let (Some(mult), Some(offset)) =
                                (iv_.mult.mul(mult), iv_.offset.mul(mult))
                            {
                                insert!(iv_.base, mult, offset);
                            }
                        }
                    }
                    _ => continue,
                }
            }
            for child in dom_tree[block_ref.0]
                .iter()
                .copied()
                .filter(|b| loop_.body.contains(b))
            {
                dfs(iv, method, child, loop_, dom_tree, ind_vars);
            }
        }
        dfs(
            self,
            method,
            loop_.header,
            loop_,
            &self.dom_tree,
            &mut ret.all,
        );
        ret
    }

    fn on_new_inst(&mut self, method: &Method, block_ref: BlockRef, inst_ref: InstRef) {
        self.inst_to_block.insert(inst_ref, block_ref);
        self.inst_to_poly.insert(
            inst_ref,
            Poly::from_inst(method, inst_ref, &self.inst_to_poly),
        );
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
    let mut iv = IndVarAnalysis::init(method);

    for loop_rc in all_loops {
        let ind_var = iv.find_induction_variables(&loop_rc.borrow(), method);
        // Do we have interesting induction variables?
        let is_interesting = |inst_ref: InstRef, ind_var: &IndVar| {
            // We only care about induction variables that are not trivial.
            if !ind_var.mult.is_one() {
                true
            } else {
                match method.inst(inst_ref) {
                    Inst::Phi(_) => false,
                    Inst::Add(lhs, rhs) if *lhs == ind_var.base.inst_ref => {
                        loop_rc.borrow().body.contains(&iv.inst_to_block[rhs])
                    }
                    Inst::Add(lhs, rhs) if *rhs == ind_var.base.inst_ref => {
                        loop_rc.borrow().body.contains(&iv.inst_to_block[lhs])
                    }
                    Inst::Copy(var) if *var == ind_var.base.inst_ref => {
                        assert!(
                            ind_var.offset.terms().is_empty() && ind_var.offset.constant() == 0
                        );
                        false
                    }
                    _ => true,
                }
            }
        };
        let interesting = ind_var
            .all
            .into_iter()
            .filter(|(inst_ref, ind_var)| is_interesting(*inst_ref, ind_var))
            .collect::<HashMap<_, _>>();
        if interesting.is_empty() {
            continue;
        }
        let header_ref = loop_rc.borrow().header;
        // println!("{}: {:#?}", header_ref, interesting);
        let prev_n_blocks = method.n_blocks();
        let preheader_ref = loops.get_or_insert_pre_header(method, header_ref);

        if method.n_blocks() > prev_n_blocks {
            // A new block is inserted, so we need to recompute the dominance tree.
            iv.dom_tree = compute_dominance(method).dominator_tree();
        }

        // Optimize!
        #[allow(clippy::mutable_key_type)]
        let mut ind_var_by_mult: HashMap<(InstRef, Poly), Vec<(InstRef, IndVar)>> = HashMap::new();
        for (inst_ref, ind_var) in interesting {
            ind_var_by_mult
                .entry((ind_var.base.inst_ref, ind_var.mult.clone()))
                .or_default()
                .push((inst_ref, ind_var));
        }
        // Pick a representative for each multiplier to be initialized out of the loop
        #[allow(clippy::mutable_key_type)]
        let mut reps: HashMap<(InstRef, Poly), (InstRef, Poly)> = HashMap::new();
        let loop_ = loop_rc.borrow();
        for ((base_ref, mult), vars) in ind_var_by_mult.iter() {
            if *mult == Poly::from_int(1) {
                // No need to initialize the base induction variable.
                continue;
            }
            // We now need to pick a representative to promote to loop header.
            // This representative will be initialized in the preheader, and
            // accumulate in the backedges.
            // The choice of representative can affect performance a lot. Here
            // we use a simple heuristic.
            let mut scores = vars
                .iter()
                .map(|(i, _)| (*i, 0usize))
                .collect::<HashMap<_, _>>();
            // The heuristic we use is to find the first induction variable that
            // is used non-arithmetically. I.e., as an argument for
            // non-arithmetical instructions. For two reasons:
            // - Argument used in arithmetical instructions might be
            //   intermediate values only used to compute some useful values later
            //   on. If we choose it to be the representative, the useful values
            //   are still steps away.
            // - If such arguments turned out to be still useful. Polynomial
            //   Strength Reduction step will ensure that they are still computed
            //   efficiently.
            let rev_postorder = loop_.body_reverse_postorder(method);
            let n_total_insts: usize = loop_
                .body
                .iter()
                .map(|b| method.block(*b).insts.len())
                .sum();
            let mut n_insts = 0;
            for block_ref in rev_postorder.iter().copied() {
                for inst_ref in method.block(block_ref).insts.iter().copied() {
                    if let Some(score) = scores.get_mut(&inst_ref) {
                        *score += n_total_insts - n_insts;
                    }
                    match method.inst(inst_ref) {
                        // Skip phis in the loop header.
                        Inst::Phi(map) if block_ref == header_ref => {
                            for (_, src) in map.iter() {
                                if let Some(score) = scores.get_mut(src) {
                                    // Being used in a phi in the loop header is a good sign.
                                    // The induction variable is an accumulator
                                    // and may be used outside. Give it a high score.
                                    *score += n_total_insts;
                                }
                            }
                        }
                        // Skip trivial uses.
                        Inst::Copy(_)
                        | Inst::Add(_, _)
                        | Inst::Sub(_, _)
                        | Inst::Neg(_)
                        | Inst::Mul(_, _) => continue,
                        inst => inst.for_each_inst_ref_copied(|arg_ref| {
                            if let Some(score) = scores.get_mut(&arg_ref) {
                                *score += n_total_insts * (n_total_insts - n_insts) + 1;
                            }
                        }),
                    }
                    n_insts += 1;
                }
            }
            let inst_ref = scores
                .iter()
                .max_by_key(|(_, score)| *score)
                .map(|(inst_ref, _)| inst_ref)
                .unwrap();
            let ind_var = &vars.iter().find(|(i, _)| i == inst_ref).unwrap().1;
            // let (inst_ref, ind_var) = vars
            //     .iter()
            //     .find(|(_, ind_var)| ind_var.offset.is_zero()) // Prefer offset 0, saves us an add in the preheader.
            //     .unwrap_or_else(|| &vars[0]);
            // if method.name.inner.as_ref() == "filter" && header_ref.0 == 0 {
            //     println!("{}: ", header_ref);
            //     for (inst_ref, ind_var) in vars {
            //         println!(
            //             "  {}: <{}, {}, {}> delta {}",
            //             inst_ref,
            //             iv.pretty_print_poly(&iv.inst_to_poly[&ind_var.base.inst_ref], method),
            //             iv.pretty_print_poly(&ind_var.mult, method),
            //             iv.pretty_print_poly(&ind_var.offset, method),
            //             iv.pretty_print_poly(&ind_var.base.delta, method),
            //         );
            //     }
            //     println!("  rep: {:?}", inst_ref);
            //     crate::utils::show_graphviz(&method.dump_graphviz());
            // }
            let base_init_val = match method.inst(ind_var.base.inst_ref) {
                Inst::Phi(map) => map[&preheader_ref],
                _ => unreachable!(),
            };
            let mut init_ref = if ind_var.mult.is_constant() && ind_var.mult.constant() == -1 {
                method.next_inst(preheader_ref, Inst::Neg(base_init_val))
            } else {
                let mult_ref =
                    iv.materialize_poly_invariant(&ind_var.mult, preheader_ref, &loop_, method);
                method.next_inst(preheader_ref, Inst::Mul(base_init_val, mult_ref))
            };
            iv.on_new_inst(method, preheader_ref, init_ref);
            if !ind_var.offset.is_zero() {
                let offset_ref =
                    iv.materialize_poly_invariant(&ind_var.offset, preheader_ref, &loop_, method);
                init_ref = method.next_inst(preheader_ref, Inst::Add(init_ref, offset_ref));
                iv.on_new_inst(method, preheader_ref, init_ref);
            }
            let delta_ref = iv.materialize_poly_invariant(
                &ind_var.base.delta.mul_nofail(mult),
                preheader_ref,
                &loop_,
                method,
            );
            // Building the phi map for the preheader.
            let var_ref = method.next_inst_prepend(header_ref, Inst::Phi(HashMap::new()));
            iv.on_new_inst(method, header_ref, var_ref);
            reps.insert((*base_ref, mult.clone()), (var_ref, ind_var.offset.clone()));
            if let Some(annotation) = method.get_inst_annotation(inst_ref) {
                *method.annotate_inst_mut(var_ref) = annotation.clone();
            }
            let mut map: HashMap<BlockRef, InstRef> = HashMap::from([(preheader_ref, init_ref)]);
            for cont_ref in loop_.continue_.iter().copied() {
                let cont_inst_ref = method.next_inst(cont_ref, Inst::Add(var_ref, delta_ref));
                iv.on_new_inst(method, cont_ref, cont_inst_ref);
                map.insert(cont_ref, cont_inst_ref);
            }
            match method.inst_mut(var_ref) {
                Inst::Phi(old_map) => *old_map = map,
                _ => unreachable!(),
            }
        }

        for ((base_ref, mult), vars) in ind_var_by_mult {
            let (rep, rep_offset) = if mult.is_one() {
                (vars[0].1.base.inst_ref, Poly::from_int(0))
            } else {
                reps[&(base_ref, mult)].clone()
            };
            for (inst_ref, ind_var) in vars {
                if ind_var.offset == rep_offset {
                    *method.inst_mut(inst_ref) = Inst::Copy(rep);
                } else {
                    let offset_ref = iv.materialize_poly_invariant(
                        &ind_var.offset.sub_nofail(&rep_offset),
                        preheader_ref,
                        &loop_,
                        method,
                    );
                    *method.inst_mut(inst_ref) = Inst::Add(rep, offset_ref);
                }
            }
        }
        // if method.name.inner.as_ref() == "filter" {
        //     crate::utils::show_graphviz(&method.dump_graphviz());
        // }
    }
}
