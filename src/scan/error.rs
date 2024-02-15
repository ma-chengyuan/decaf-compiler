use std::fmt;

use colored::Colorize;
use thiserror::Error;

use crate::utils::diagnostics::{Diagnostic, DiagnosticItem};

use super::location::{Location, Span};

#[derive(Debug, Clone, Error)]
pub struct ScannerError {
    pub(super) location: Location,
    pub(super) context: ScannerErrorContext,
    pub(super) expecting: ScannerExpecting,
    pub(super) found: Option<char>,
}

impl fmt::Display for ScannerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let found = match self.found {
            Some(c) => format!("{:?}", c),
            None => "end of file".to_string(),
        };
        write!(
            f,
            "{}: expecting {}, found {} ({})",
            self.location, self.expecting, found, self.context
        )
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ScannerExpecting {
    Char(char),
    OneOf(&'static str),
    PrintableOrExcape,
    EscapeSequence,
}

impl fmt::Display for ScannerExpecting {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ScannerExpecting::Char(c) => write!(f, "{:?}", c),
            ScannerExpecting::OneOf(s) => write!(f, "one of \"{}\"", s),
            ScannerExpecting::PrintableOrExcape => write!(f, "printable character or '\\'"),
            ScannerExpecting::EscapeSequence => {
                write!(f, "escape sequence (one of n, t, \\, \", \')")
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScannerErrorContext {
    CharLiteral,
    StringLiteral,
    CharClosingQuote,
    StringClosingQuote,
    OperatorToken,
    SingleCharToken,
    ClosingBlockComment,
}

impl fmt::Display for ScannerErrorContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ScannerErrorContext::CharLiteral => write!(f, "invalid character in char literal"),
            ScannerErrorContext::StringLiteral => write!(f, "invalid charcter in string literal"),
            ScannerErrorContext::CharClosingQuote => {
                write!(f, "expecting closing quote of char literal")
            }
            ScannerErrorContext::StringClosingQuote => {
                write!(f, "expecting closing quote of string literal")
            }
            ScannerErrorContext::OperatorToken => write!(f, "invalid start of operator token"),
            ScannerErrorContext::SingleCharToken => write!(f, "invalid single character token"),
            ScannerErrorContext::ClosingBlockComment => {
                write!(f, "expecting closing */ of block comment")
            }
        }
    }
}

impl From<&ScannerError> for Diagnostic {
    fn from(value: &ScannerError) -> Self {
        let pre_text = format!("{}: {}", "error(scanner)".red().bold(), value.context);
        Diagnostic::new()
            .with_pre_text(&pre_text)
            .add_item(DiagnosticItem {
                span: Span {
                    start: value.location.clone(),
                    end: value.location.clone(),
                },
                message: format!("expecting {}", value.expecting),
                color: Some(colored::Color::Red),
            })
    }
}
