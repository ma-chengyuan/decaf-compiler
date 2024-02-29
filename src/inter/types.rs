use core::fmt;

use crate::{
    parse::ast::{self, Initializer, RuntimeLiteral},
    scan::location::Spanned,
};

use super::error::SemanticError;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PrimitiveType {
    Int,
    Bool,
}

impl fmt::Display for PrimitiveType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PrimitiveType::Int => write!(f, "int"),
            PrimitiveType::Bool => write!(f, "bool"),
        }
    }
}

impl From<&ast::Type> for PrimitiveType {
    fn from(ty: &ast::Type) -> Self {
        match ty {
            ast::Type::Int => Self::Int,
            ast::Type::Bool => Self::Bool,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Type {
    Void,
    Primitive(PrimitiveType),
    Array { base: Box<Type>, length: usize },
    Invalid,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Void => write!(f, "void"),
            Type::Primitive(ty) => write!(f, "{}", ty),
            Type::Array { base, length } => write!(f, "{}[{}]", base, length),
            Type::Invalid => write!(f, "<invalid type>"),
        }
    }
}

impl Type {
    pub fn from_ast_literal(lit: &RuntimeLiteral) -> Self {
        match lit {
            RuntimeLiteral::Int(_) | RuntimeLiteral::Char(_) => Self::Primitive(PrimitiveType::Int),
            RuntimeLiteral::Bool(_) => Self::Primitive(PrimitiveType::Bool),
        }
    }

    pub fn from_ast_initializer(init: &Initializer) -> Result<Self, SemanticError> {
        match init {
            Initializer::Literal(lit) => Ok(Self::from_ast_literal(lit)),
            Initializer::Array(elements) => {
                // By the Decaf spec, initializers have at least one element.
                // Non-conformant initializers will be rejected at parse time,
                // so [0] is safe.
                let first_type = Self::from_ast_initializer(&elements.inner[0])?;
                for element in &elements.inner[1..] {
                    let element_type = Self::from_ast_initializer(element)?;
                    if first_type != element_type {
                        return Err(SemanticError::NonhomogeneousArrayInitializer {
                            first: Spanned {
                                inner: first_type,
                                span: elements.inner[0].span().clone(),
                            },
                            second: Spanned {
                                inner: element_type,
                                span: element.span().clone(),
                            },
                        });
                    }
                }
                Ok(Self::Array {
                    base: Box::new(first_type),
                    length: elements.inner.len(),
                })
            }
        }
    }
}
