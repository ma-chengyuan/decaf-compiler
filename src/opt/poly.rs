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
        mut map: im::HashMap<InstRef, Poly>,
        mut avail: im::HashMap<Poly, InstRef>,
        // mut avail_list: im::Vector<Poly>,
        mut avail_offset: im::HashMap<Poly, (InstRef, i64)>,
    ) {
        for inst_ref in method.block(block_ref).insts.clone() {
            let val = Poly::from_inst(method, inst_ref, &map);
            let inst = method.inst_mut(inst_ref);
            match inst {
                Inst::Mul(_, _) | Inst::Add(_, _) | Inst::Sub(_, _) => {
                    if let Some(src) = avail.get(&val) {
                        // Check if the operation can be replaced with a copy.
                        *inst = Inst::Copy(*src);
                    } else if let Some(src) = avail.get(&val.neg()) {
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
                        // Check if the operation can be replaced with an addition or subtraction two values.
                        'outer: for (p1, lhs_ref) in avail.iter() {
                            if let Some(p2) = val.sub(p1) {
                                // val = p1 + p2
                                if let Some(rhs_ref) = avail.get(&p2) {
                                    let (mut lhs, mut rhs) = (lhs_ref, rhs_ref);
                                    if lhs > rhs {
                                        std::mem::swap(&mut lhs, &mut rhs);
                                    }
                                    *inst = Inst::Add(*lhs, *rhs);
                                    break 'outer;
                                }
                            }
                            if let Some(p2) = val.add(p1) {
                                // val = p2 - p1
                                if let Some(rhs_ref) = avail.get(&p2) {
                                    *inst = Inst::Sub(*rhs_ref, *lhs_ref);
                                    break 'outer;
                                }
                            }
                            if let Some(p2) = p1.sub(&val) {
                                // val = p1 - p2
                                if let Some(rhs_ref) = avail.get(&p2) {
                                    *inst = Inst::Sub(*lhs_ref, *rhs_ref);
                                    break 'outer;
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
            map.insert(inst_ref, val.clone());
            if !avail.contains_key(&val) {
                avail.insert(val.clone(), inst_ref);
                // avail_list.push_back(val.clone());
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
                // avail_list.clone(),
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
        // im::Vector::new(),
        im::HashMap::new(),
    );
}
