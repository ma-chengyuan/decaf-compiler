use std::rc::Rc;

use crate::{
    parse::ast::Ident,
    scan::location::{Location, Source, Span},
};

pub mod cli;
pub mod diagnostics;
pub mod formatting;

pub fn make_internal_ident(s: &str) -> Ident {
    let file = Rc::new(Source {
        filename: "<compiler internal>".to_string(),
        content: s.chars().collect(),
    });
    let span = Span::new(
        Location {
            offset: 0,
            line: 0,
            column: 0,
            source: file.clone(),
        },
        Location {
            offset: file.content.len(),
            line: 0, // TODO: line and column should be calculated
            column: file.content.len(),
            source: file,
        },
    );
    Ident {
        inner: s.into(),
        span,
    }
}
