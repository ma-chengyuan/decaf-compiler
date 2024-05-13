#![allow(dead_code)]

use std::fmt;

use cachedhash::CachedHash;
use im::{ordmap, vector};

use crate::inter::{
    constant::Const,
    ir::{BlockRef, Inst, InstRef, Method},
};

use super::dom::compute_dominance;

// An arbitrary limit to avoid bad program blowing up the memory
const MAX_POLY_TERMS: usize = 64;

/// A polynomial

#[derive(Clone, PartialEq, Eq, Hash, Default)]
pub struct PolyInner {
    /// Constant factor
    pub c: i64,
    /// Terms: InstRefs to coefficients
    pub t: im::OrdMap<CachedHash<im::Vector<InstRef>>, i64>,
}

impl fmt::Debug for PolyInner {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.c)?;
        for (t, c) in self.t.iter() {
            if *c > 0 {
                write!(f, " + ")?;
            } else {
                write!(f, " - ")?;
            }
            write!(f, "{}{:?}", c.abs(), CachedHash::get(t))?;
        }
        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Poly(CachedHash<PolyInner>);

impl fmt::Debug for Poly {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", CachedHash::get(&self.0))
    }
}

impl Poly {
    pub fn new(c: i64, t: im::OrdMap<CachedHash<im::Vector<InstRef>>, i64>) -> Self {
        Self(CachedHash::new(PolyInner { c, t }))
    }

    pub fn constant(&self) -> i64 {
        self.0.c
    }

    pub fn constant_mut(&mut self) -> &mut i64 {
        &mut self.0.c
    }

    pub fn terms(&self) -> &im::OrdMap<CachedHash<im::Vector<InstRef>>, i64> {
        &self.0.t
    }

    pub fn terms_mut(&mut self) -> &mut im::OrdMap<CachedHash<im::Vector<InstRef>>, i64> {
        &mut self.0.t
    }

    pub fn from_int(c: i64) -> Poly {
        Self::new(c, Default::default())
    }

    pub fn from_term(inst_ref: InstRef) -> Self {
        Self::new(0, ordmap! {CachedHash::new(vector![inst_ref]) => 1})
    }

    pub fn add(&self, other: &Self) -> Option<Self> {
        let mut ret = Self::new(self.constant() + other.constant(), Default::default());
        let ret_terms = ret.terms_mut();
        for (t, c1) in self.terms().iter() {
            if let Some(c2) = other.terms().get(t) {
                if c2 + c1 != 0 {
                    ret_terms.insert(t.clone(), c1 + c2);
                }
            } else {
                ret_terms.insert(t.clone(), *c1);
            }
        }
        for (t, c2) in other.terms().iter() {
            if !self.terms().contains_key(t) {
                ret_terms.insert(t.clone(), *c2);
            }
        }
        if ret.terms().len() <= MAX_POLY_TERMS {
            Some(ret)
        } else {
            None
        }
    }

    pub fn sub_nofail(&self, other: &Self) -> Self {
        let mut ret = Self::new(self.constant() - other.constant(), Default::default());
        let ret_terms = ret.terms_mut();
        for (t, c1) in self.terms().iter() {
            if let Some(c2) = other.terms().get(t) {
                if c1 - c2 != 0 {
                    ret_terms.insert(t.clone(), c1 - c2);
                }
            } else {
                ret_terms.insert(t.clone(), *c1);
            }
        }
        for (t, c2) in other.terms().iter() {
            if !self.terms().contains_key(t) {
                ret_terms.insert(t.clone(), -*c2);
            }
        }
        ret
    }

    pub fn sub(&self, other: &Self) -> Option<Self> {
        let ret = self.sub_nofail(other);
        if ret.terms().len() <= MAX_POLY_TERMS {
            Some(ret)
        } else {
            None
        }
    }

    pub fn mul_nofail(&self, other: &Self) -> Self {
        let mut ret = Self::new(self.constant() * other.constant(), Default::default());
        let ret_terms = ret.terms_mut();
        for (t1, c1) in self.terms().iter() {
            ret_terms.insert(t1.clone(), c1 * other.constant());
        }
        for (t2, c2) in other.terms().iter() {
            ret_terms
                .entry(t2.clone())
                .and_modify(|c| *c += c2 * self.constant())
                .or_insert(c2 * self.constant());
            for (t1, c1) in self.terms().iter() {
                let mut t = t1.clone();
                t.append(CachedHash::get(t2).clone());
                t.sort();
                let c_ = c1 * c2;
                ret_terms.entry(t).and_modify(|c| *c += c_).or_insert(c_);
            }
        }
        *ret_terms = ret_terms
            .iter()
            .filter(|(_, c)| **c != 0)
            .map(|(t, c)| (t.clone(), *c))
            .collect();
        ret
    }

    pub fn mul(&self, other: &Self) -> Option<Self> {
        let ret = self.mul_nofail(other);
        if ret.terms().len() <= MAX_POLY_TERMS {
            Some(ret)
        } else {
            None
        }
    }

    pub fn neg(&self) -> Self {
        Self::new(
            -self.constant(),
            self.terms().iter().map(|(t, c)| (t.clone(), -c)).collect(),
        )
    }

    pub fn is_one(&self) -> bool {
        self.constant() == 1 && self.terms().is_empty()
    }

    pub fn is_zero(&self) -> bool {
        self.constant() == 0 && self.terms().is_empty()
    }

    pub fn is_constant(&self) -> bool {
        self.terms().is_empty()
    }

    pub fn from_inst(method: &Method, inst_ref: InstRef, map: &im::HashMap<InstRef, Poly>) -> Self {
        if let Some(poly) = map.get(&inst_ref) {
            return poly.clone();
        }
        match method.inst(inst_ref) {
            Inst::LoadConst(Const::Int(x)) => Self::from_int(*x),
            Inst::LoadConst(Const::Bool(x)) => Self::from_int(*x as i64),
            Inst::Copy(src) => Self::from_inst(method, *src, map),
            Inst::Neg(src) => Self::from_inst(method, *src, map).neg(),
            Inst::Add(lhs, rhs) => Self::from_inst(method, *lhs, map)
                .add(&Self::from_inst(method, *rhs, map))
                .unwrap_or_else(|| Self::from_term(inst_ref)),
            Inst::Sub(lhs, rhs) => Self::from_inst(method, *lhs, map)
                .sub(&Self::from_inst(method, *rhs, map))
                .unwrap_or_else(|| Self::from_term(inst_ref)),
            Inst::Mul(lhs, rhs) => Self::from_inst(method, *lhs, map)
                .mul(&Self::from_inst(method, *rhs, map))
                .unwrap_or_else(|| Self::from_term(inst_ref)),
            // TODO: handle some special cases of division?
            _ => Self::from_term(inst_ref),
        }
    }

    pub fn without_constant(&self) -> Self {
        Self::new(0, self.terms().clone())
    }
}

pub fn polynomial_strength_reduction(method: &mut Method) {
    let dom = compute_dominance(method);
    let dom_tree = dom.dominator_tree();

    fn dfs(
        method: &mut Method,
        block_ref: BlockRef,
        dom_tree: &[Vec<BlockRef>],
        // Map from instruction to polynomial
        mut map: im::HashMap<InstRef, Poly>,
        // Map from polynomial to the first instruction that computes it, plus
        // its distance to the top of the method CFG along the dominator tree
        mut avail: im::HashMap<Poly, (InstRef, usize)>,
        // Map a constant-free polynomial to the first instruction that computes
        // it, plus the constant part
        mut avail_offset: im::HashMap<Poly, (InstRef, i64)>,
    ) {
        for inst_ref in method.block(block_ref).insts.clone() {
            let val = Poly::from_inst(method, inst_ref, &map);
            let inst = method.inst_mut(inst_ref);
            if val.is_constant() {
                // If the value is a constant, we can replace the instruction
                // with a load constant instruction.
                *inst = Inst::LoadConst(Const::Int(val.constant()));
            }
            match inst {
                Inst::Neg(_) => {
                    if let Some((src, _)) = avail.get(&val) {
                        // Check if the operation can be replaced with a copy.
                        *inst = Inst::Copy(*src);
                    }
                }
                Inst::Mul(_, _) | Inst::Add(_, _) | Inst::Sub(_, _) => {
                    if let Some((src, _)) = avail.get(&val) {
                        // Check if the operation can be replaced with a copy.
                        *inst = Inst::Copy(*src);
                    } else if let Some((src, _)) = avail.get(&val.neg()) {
                        // Check if the operation can be replaced with a negation.
                        *inst = Inst::Neg(*src);
                    } else if let Some((src, offset)) = avail_offset.get(&val.without_constant()) {
                        // Check if the operation can be replaced with an addition with constant.
                        let offset_ref = method.next_inst_before(
                            block_ref,
                            Inst::LoadConst(Const::Int(-*offset + val.constant())),
                            inst_ref,
                        );
                        *method.inst_mut(inst_ref) = Inst::Add(*src, offset_ref);
                    } else if let Inst::Mul(_, _) = inst {
                        // Check if the operation can be replaced with an
                        // addition or subtraction of two values.
                        // The algorithm here is deterministic in order to make
                        // the pass idempotent.
                        // If there are multiple possible replacements, we
                        // choose the one with the smallest "order." That is, we
                        // choose the one that is closest
                        // to the top of the method CFG. Hopefully many of
                        // instructions that were previously interdependent will
                        // be replaced by those that only depend on a select few
                        // instructions that are close to the top of the method
                        // CFG. Then most of them will be eliminated by the dead
                        // code elimination pass.
                        let mut best = (usize::MAX, usize::MAX);
                        for (p1, (lhs_ref, lhs_ord)) in avail.iter() {
                            if let Some(p2) = val.sub(p1) {
                                // val = p1 + p2
                                if let Some((rhs_ref, rhs_ord)) = avail.get(&p2) {
                                    let cur = (*lhs_ord.max(rhs_ord), 0);
                                    if cur < best {
                                        best = cur;
                                        *inst = if lhs_ref < rhs_ref {
                                            Inst::Add(*lhs_ref, *rhs_ref)
                                        } else {
                                            Inst::Add(*rhs_ref, *lhs_ref)
                                        };
                                    }
                                }
                            }
                            if let Some(p2) = p1.sub(&val) {
                                // val = p1 - p2
                                if let Some((rhs_ref, rhs_ord)) = avail.get(&p2) {
                                    let cur = (*lhs_ord.max(rhs_ord), 1);
                                    if cur < best {
                                        best = cur;
                                        *inst = Inst::Sub(*lhs_ref, *rhs_ref);
                                    }
                                }
                            }
                            if let Some(p2) = val.add(p1) {
                                // val = p2 - p1
                                if let Some((rhs_ref, rhs_ord)) = avail.get(&p2) {
                                    let cur = (*lhs_ord.max(rhs_ord), 2);
                                    if cur < best {
                                        best = cur;
                                        *inst = Inst::Sub(*rhs_ref, *lhs_ref);
                                    }
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
            map.insert(inst_ref, val.clone());
            if !avail.contains_key(&val) {
                avail.insert(val.clone(), (inst_ref, avail.len()));
            }
            let (c, t) = (val.constant(), val.without_constant());
            avail_offset.entry(t).or_insert((inst_ref, c));
        }
        // println!("at the end of {}: {:#?}", block_ref, map);
        for child in dom_tree[block_ref.0].iter() {
            dfs(
                method,
                *child,
                dom_tree,
                map.clone(),
                avail.clone(),
                avail_offset.clone(),
            );
        }
    }

    dfs(
        method,
        method.entry,
        &dom_tree,
        im::HashMap::new(),
        im::HashMap::new(),
        im::HashMap::new(),
    );
}
