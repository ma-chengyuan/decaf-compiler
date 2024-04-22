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

/// Opens and shows a graphviz dot file in the default viewer.
pub fn show_graphviz(dot: &str) {
    use std::io::Write;
    use std::process::{Command, Stdio};
    use tempfile::Builder;

    let process = Command::new("dot")
        .arg("-Tsvg")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("can't spawn dot");
    process
        .stdin
        .as_ref()
        .unwrap()
        .write_all(dot.as_bytes())
        .unwrap();
    let output = process.wait_with_output().expect("can't read dot output");
    let mut tempfile = Builder::new()
        .prefix("decaf-compiler")
        .suffix(".svg")
        .tempfile()
        .expect("can't create temp file");
    tempfile
        .write_all(&output.stdout)
        .expect("can't write to temp file");
    tempfile.flush().expect("can't flush temp file");
    let (_, path) = tempfile.keep().expect("can't keep temp file");
    opener::open(path).expect("can't open temp file");
}
