use std::fmt;

use colored::{Color, Colorize};

use crate::{
    scan::{location::Spanned, token::Token},
    utils::diagnostics::{Diagnostic, DiagnosticItem},
};

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

fn format_expecting_tokens(tokens: &[Token]) -> String {
    fn format_expecting_token(t: &Token) -> String {
        match t {
            Token::Identifier(_) => String::from("<identifier>"),
            Token::IntLiteral(_) => String::from("<int literal>"),
            Token::BoolLiteral(_) => String::from("<bool literal>"),
            Token::StringLiteral(_) => String::from("<string literal>"),
            Token::CharLiteral(_) => String::from("<char literal>"),
            _ => format!("{}", t),
        }
    }
    if tokens.len() == 1 {
        format_expecting_token(&tokens[0])
    } else {
        format!(
            "one of [{}]",
            tokens
                .iter()
                .map(format_expecting_token)
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl fmt::Display for ParserErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParserErrorKind::UnexpectedToken { expecting, found } => {
                write!(
                    f,
                    "{}: unexpected token {}, expecting {}",
                    found.span.start,
                    found.inner,
                    format_expecting_tokens(expecting),
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

impl From<&ParserError> for Diagnostic {
    fn from(error: &ParserError) -> Self {
        let mut diag = Diagnostic::new();
        let error_str = "error(parser)".red().bold();
        match &*error.kind {
            ParserErrorKind::UnexpectedToken { expecting, found } => {
                diag = diag
                    .with_pre_text(&format!("{}: unexpected token {}", error_str, found.inner))
                    .add_item(DiagnosticItem {
                        span: found.span.clone(),
                        message: format!("expecting {}", format_expecting_tokens(expecting)),
                        color: Some(Color::Red),
                    });
            }
            ParserErrorKind::EmptyInitializer(token) => {
                diag = diag
                    .with_pre_text(&format!(
                        "{}: empty initializer in array declaration",
                        error_str
                    ))
                    .add_item(DiagnosticItem {
                        span: token.span.clone(),
                        message: "empty initializer".to_string(),
                        color: Some(Color::Red),
                    });
            }
            ParserErrorKind::EmptyFieldDecl(token) => {
                diag = diag
                    .with_pre_text(&format!("{}: empty field declaration", error_str))
                    .add_item(DiagnosticItem {
                        span: token.span.clone(),
                        message: "empty field declaration".to_string(),
                        color: Some(Color::Red),
                    });
            }
        }
        diag = error
            .contexts
            .iter()
            .fold(diag, |diag, ctx| diag.add_item(ctx.into()));
        diag
    }
}
