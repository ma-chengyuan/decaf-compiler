use core::fmt;

use lazy_static::lazy_static;
use num_bigint::BigInt;
use num_traits::ToPrimitive;

use crate::parse::ast::{Initializer, RuntimeLiteral};

use super::{
    error::SemanticError,
    types::{PrimitiveType, Type, BOOL_SIZE, INT_SIZE},
};

/// A constant value in the intermediate representation.

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Const {
    Int(i64),
    Bool(bool),
    Array(Vec<Const>),
}

lazy_static! {
    pub static ref INT_0: BigInt = BigInt::from(0);
    pub static ref INT_MAX: BigInt = BigInt::from(i64::MAX);
    pub static ref INT_MIN: BigInt = BigInt::from(i64::MIN);
}

impl fmt::Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Const::Int(i) => write!(f, "{}", i),
            Const::Bool(b) => write!(f, "{}", b),
            Const::Array(arr) => {
                write!(f, "[")?;
                for (i, c) in arr.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", c)?;
                }
                write!(f, "]")
            }
        }
    }
}

impl Const {
    pub fn from_ast_literal(lit: &RuntimeLiteral) -> Result<Self, SemanticError> {
        match lit {
            RuntimeLiteral::Int(i) => match i.inner.to_i64() {
                Some(i) => Ok(Self::Int(i)),
                None => Err(SemanticError::InvalidIntLiteral(i.clone())),
            },
            RuntimeLiteral::Bool(b) => Ok(Self::Bool(b.inner)),
            RuntimeLiteral::Char(c) => Ok(Self::Int(c.inner as i64)),
        }
    }

    pub fn from_ast_initializer(init: &Initializer) -> Result<Self, SemanticError> {
        match init {
            Initializer::Literal(lit) => Self::from_ast_literal(lit),
            Initializer::Array(spanned) => {
                let inits = spanned
                    .inner
                    .iter()
                    .map(Self::from_ast_initializer)
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Self::Array(inits))
            }
        }
    }

    pub fn default_for(ty: &Type) -> Self {
        match ty {
            Type::Primitive(ty) => match ty {
                PrimitiveType::Int => Self::Int(0),
                PrimitiveType::Bool => Self::Bool(false),
            },
            Type::Array { base, length } => {
                let base_default = Self::default_for(base);
                Self::Array(vec![base_default; *length])
            }
            Type::Invalid => Self::Int(0), // This is not a valid type, but we need to return something.
            Type::Void => unreachable!(),
        }
    }

    pub fn size(&self) -> usize {
        match self {
            Const::Int(_) => INT_SIZE,
            Const::Bool(_) => BOOL_SIZE,
            Const::Array(arr) => arr.iter().map(Self::size).sum(),
        }
    }
}
