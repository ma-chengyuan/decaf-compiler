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
                fn format_expected(t: &Token) -> String {
                    match t {
                        Token::Identifier(_) => String::from("<identifier>"),
                        Token::IntLiteral(_) => String::from("<int literal>"),
                        Token::BoolLiteral(_) => String::from("<bool literal>"),
                        Token::StringLiteral(_) => String::from("<string literal>"),
                        Token::CharLiteral(_) => String::from("<char literal>"),
                        _ => format!("{}", t),
                    }
                }

                if expecting.len() == 1 {
                    write!(
                        f,
                        "{}: unexpected token {}, expecting {}",
                        found.span.start,
                        found.inner,
                        format_expected(&expecting[0])
                    )
                } else {
                    let expecting = expecting
                        .iter()
                        .map(format_expected)
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(
                        f,
                        "{}: unexpected token {}, expecting one of [{}]",
                        found.span.start, found.inner, expecting
                    )
                }
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
