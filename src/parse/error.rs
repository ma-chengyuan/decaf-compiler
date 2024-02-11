use std::fmt;

use crate::scan::{location::Spanned, token::Token};

use super::parser::ParserContext;

#[derive(Debug, Clone)]
pub struct ParserError {
    pub kind: Box<ParserErrorKind>,
    /// The parser contexts in which the error occurred, from the innermost to the outermost.
    pub contexts: Vec<ParserContext>,
}

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)?;
        if !self.contexts.is_empty() {
            write!(f, " in ")?;
            for (i, ctx) in self.contexts.iter().rev().enumerate() {
                if i > 0 {
                    write!(f, " -> ")?;
                }
                write!(f, "{:?}", ctx)?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub enum ParserErrorKind {
    UnexpectedToken {
        expected: Vec<Token>,
        found: Spanned<Token>,
    },
    IntegerOutOfRange(Spanned<Token>),
}

impl fmt::Display for ParserErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParserErrorKind::UnexpectedToken { expected, found } => {
                write!(
                    f,
                    "{:?}: unexpected token {:?}, expected one of {:?}",
                    found.span.start, found.inner, expected
                )
            }
            ParserErrorKind::IntegerOutOfRange(token) => {
                write!(
                    f,
                    "{:?}: integer literal out of range: {:?}",
                    token.span.start, token.inner
                )
            }
        }
    }
}

pub trait ParseErrorExt {
    fn with_context(self, ctx: ParserContext) -> Self;
}

impl ParseErrorExt for ParserError {
    fn with_context(mut self, ctx: ParserContext) -> Self {
        self.contexts.push(ctx);
        self
    }
}

impl<T> ParseErrorExt for Result<T, ParserError> {
    fn with_context(self, ctx: ParserContext) -> Self {
        self.map_err(|e| e.with_context(ctx))
    }
}
