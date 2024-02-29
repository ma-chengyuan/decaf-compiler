#![allow(dead_code)]
use colored::{Color, Colorize};

use crate::{
    parse::ast::{Ident, IntLiteral},
    scan::location::{Span, Spanned},
    utils::diagnostics::{Diagnostic, DiagnosticItem},
};

use super::types::Type;

#[derive(Debug, Clone)]
pub enum SemanticError {
    DuplicateDecls {
        first: Ident,
        second: Ident,
    },
    InvalidMainMethod(Option<Ident>),
    MismatchedInitializerType {
        ident: Ident,
        init_type: Type,
    },
    NonhomogeneousArrayInitializer {
        first: Spanned<Type>,
        second: Spanned<Type>,
    },
    CoexistingArrayLengthAndInitializer(Ident),
    InvalidArrayLength {
        ident: Ident,
        length: IntLiteral,
    },
    MissingArrayLength(Ident),
    InvalidCall {
        decl_site: Ident,
        call_site: Ident,
    },
    NoReturn {
        decl_site: Ident,
        call_site: Ident,
    },
    InvalidArgForNonImport {
        span: Ident,
    },
    InvalidReturnType {
        return_type: Spanned<Type>,
        expr_type: Spanned<Type>,
        method: Ident,
    },
    UnknownVar(Ident),
    UnknownMethod(Ident),
    InvalidArrayBaseType {
        ident: Ident,
        ty: Type,
    },
    InvalidArrayIndexType {
        ident: Ident,
        ty: Type,
    },
    InvalidLen {
        ident: Ident,
        ty: Type,
    },
    InvalidCondition(Spanned<Type>),
    UnexpectedTypeForOp {
        ty: Spanned<Type>,
        expected_types: Vec<Type>,
    },
    IncompatibleTypes {
        lhs: Spanned<Type>,
        rhs: Spanned<Type>,
    },
    MissingConstInitializer(Ident),
    ReassigningConst {
        decl_site: Ident,
        assign_site: Ident,
    },
    InvalidBreak(Span),
    InvalidContinue(Span),
    InvalidIntLiteral(IntLiteral),
}

impl From<&SemanticError> for Diagnostic {
    fn from(value: &SemanticError) -> Self {
        let error_str = "error(semantics)".red().bold();
        match value {
            SemanticError::DuplicateDecls { first, second } => Diagnostic::new()
                .with_pre_text(&format!("{}: duplicate declaration", error_str))
                .add_item(DiagnosticItem {
                    message: "first declaration".to_string(),
                    span: first.span.clone(),
                    color: Some(Color::Red),
                })
                .add_item(DiagnosticItem {
                    message: "second declaration".to_string(),
                    span: second.span.clone(),
                    color: Some(Color::Yellow),
                }),
            SemanticError::InvalidMainMethod(method) => {
                let diag = Diagnostic::new()
                    .with_pre_text(&format!("{}: invalid or missing main method", error_str));
                match method {
                    Some(method) => diag.add_item(DiagnosticItem {
                        message: "main method should return void and take no argments".to_string(),
                        span: method.span.clone(),
                        color: Some(Color::Red),
                    }),
                    None => diag,
                }
            }
            SemanticError::MismatchedInitializerType { ident, .. } => Diagnostic::new()
                .with_pre_text(&format!("{}: mismatched initializer type", error_str))
                .add_item(DiagnosticItem {
                    message: "initializer type should match the declared type of this variable"
                        .to_string(),
                    span: ident.span.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::NonhomogeneousArrayInitializer { first, second } => Diagnostic::new()
                .with_pre_text(&format!("{}: nonhomogeneous array initializer", error_str))
                .add_item(DiagnosticItem {
                    message: format!("type: {}", first.inner),
                    span: first.span.clone(),
                    color: Some(Color::Red),
                })
                .add_item(DiagnosticItem {
                    message: format!("type: {}", second.inner),
                    span: second.span.clone(),
                    color: Some(Color::Yellow),
                }),
            SemanticError::CoexistingArrayLengthAndInitializer(ident) => Diagnostic::new()
                .with_pre_text(&format!(
                    "{}: coexisting array length and initializer",
                    error_str
                ))
                .add_item(DiagnosticItem {
                    message: Default::default(),
                    span: ident.span.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::InvalidArrayLength { length, .. } => Diagnostic::new()
                .with_pre_text(&format!("{}: invalid array length", error_str))
                .add_item(DiagnosticItem {
                    message: "should be in (0, 9223372036854775807]".to_string(),
                    span: length.span.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::MissingArrayLength(ident) => Diagnostic::new()
                .with_pre_text(&format!("{}: missing array length", error_str))
                .add_item(DiagnosticItem {
                    message: "length of array without initializer must be specified".to_string(),
                    span: ident.span.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::MissingConstInitializer(ident) => Diagnostic::new()
                .with_pre_text(&format!("{}: missing const initializer", error_str))
                .add_item(DiagnosticItem {
                    message: "const variable should be initialized".to_string(),
                    span: ident.span.clone(),
                    color: Some(Color::Red),
                }),
            other => Diagnostic::new().with_pre_text(&format!("{}: {:?}", error_str, other)),
        }
    }
}
