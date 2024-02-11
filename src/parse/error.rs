use std::fmt;

use crate::scan::{location::Spanned, token::Token};

use super::parser::{ParseScope, ParserContext};

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
    /// Unexpected token (general case, will be moved to a more specific error kind later)
    UnexpectedToken {
        expecting: Vec<Token>,
        found: Spanned<Token>,
    },
    // Empty initializer in array declaration, token points to the opening brace
    EmptyInitializer(Spanned<Token>),
    // Empty field declaration, token points to the semicolon
    EmptyFieldDecl(Spanned<Token>),
}

impl fmt::Display for ParserErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParserErrorKind::UnexpectedToken { expecting, found } => {
                write!(
                    f,
                    "{}: unexpected token {:?}, expected one of {:?}",
                    found.span.start, found.inner, expecting
                )
            }
            ParserErrorKind::EmptyInitializer(token) => {
                write!(
                    f,
                    "{}: empty initializer in array declaration",
                    token.span.start
                )
            }
            ParserErrorKind::EmptyFieldDecl(token) => {
                write!(f, "{}: empty field declaration", token.span.start)
            }
        }
    }
}

pub(super) trait ParseErrorExt: Sized {
    fn with_context(self, ctx: ParserContext) -> Self;

    fn with_scope(self, scope: &ParseScope) -> Self {
        self.with_context(scope.context.clone())
    }
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
