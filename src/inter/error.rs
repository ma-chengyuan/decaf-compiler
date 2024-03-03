use colored::{Color, Colorize};

use crate::{
    parse::ast::{BinOp, Ident, IntLiteral, UnaryOp},
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
        init_ty: Type,
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
    InvalidArgForNonImport {
        decl_site: Ident,
        call_site: Ident,
        offending_arg: Span,
    },
    MismatchedArgCount {
        decl_site: Ident,
        call_site: Ident,
        expected: usize,
        found: usize,
    },
    MismatchedArgType {
        param: Ident,
        arg: Span,
        param_ty: Type,
        arg_ty: Type,
    },
    InvalidReturnType {
        return_ty: Type,
        expr_ty: Spanned<Type>,
        method: Ident,
    },
    UnknownVar(Ident),
    UnknownMethod(Ident),
    IndexingScalar {
        ident: Ident,
        ty: Type,
    },
    InvalidArrayIndex(Spanned<Type>),
    InvalidLen {
        ident: Ident,
        ty: Type,
    },
    InvalidCondition(Spanned<Type>),
    InvalidBinOpTypes {
        op: BinOp,
        lhs: Spanned<Type>,
        rhs: Spanned<Type>,
    },
    InvalidUnaryOpType {
        op: UnaryOp,
        ty: Spanned<Type>,
    },
    MismatchedAssignmentTypes {
        rhs_ty: Spanned<Type>,
        lhs_ty: Type,
        decl_site: Ident,
    },
    NonNumericUpdate(Spanned<Type>),
    NonScalarAssignment {
        decl_site: Ident,
        update_site: Ident,
    },
    MissingConstInitializer(Ident),
    ReassigningConst {
        decl_site: Ident,
        assign_site: Ident,
    },
    InvalidBreak(Span),
    InvalidContinue(Span),
    InvalidIntLiteral(IntLiteral),
    InvalidLoopVariable {
        decl_site: Ident,
        use_site: Ident,
        ty: Type,
    },
    InvalidCall {
        decl_site: Ident,
        use_site: Ident,
    },
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
                    color: Some(Color::Blue),
                })
                .add_item(DiagnosticItem {
                    message: "second declaration".to_string(),
                    span: second.span.clone(),
                    color: Some(Color::Red),
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
                    color: Some(Color::Blue),
                })
                .add_item(DiagnosticItem {
                    message: format!("type: {}", second.inner),
                    span: second.span.clone(),
                    color: Some(Color::Red),
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
            SemanticError::InvalidArgForNonImport {
                decl_site,
                call_site,
                offending_arg,
            } => Diagnostic::new()
                .with_pre_text(&format!(
                    "{}: invalid argument for non-import method \"{}\"",
                    error_str, decl_site.inner,
                ))
                .add_item(DiagnosticItem {
                    message: "defined here".to_string(),
                    span: decl_site.span.clone(),
                    color: Some(Color::Blue),
                })
                .add_item(DiagnosticItem {
                    message: "called here".to_string(),
                    span: call_site.span.clone(),
                    color: Some(Color::Blue),
                })
                .add_item(DiagnosticItem {
                    message: "expecting int or bool".to_string(),
                    span: offending_arg.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::MismatchedArgCount {
                decl_site,
                call_site,
                expected,
                found,
            } => Diagnostic::new()
                .with_pre_text(&format!("{}: mismatched argument count", error_str))
                .add_item(DiagnosticItem {
                    message: format!("expected {}, found {}", expected, found),
                    span: call_site.span.clone(),
                    color: Some(Color::Red),
                })
                .add_item(DiagnosticItem {
                    message: "defined here".to_string(),
                    span: decl_site.span.clone(),
                    color: Some(Color::Blue),
                }),
            SemanticError::MismatchedArgType {
                param,
                arg,
                param_ty,
                arg_ty,
            } => Diagnostic::new()
                .with_pre_text(&format!("{}: mismatched argument type", error_str))
                .add_item(DiagnosticItem {
                    message: format!("defined here with type: {}", param_ty),
                    span: param.span.clone(),
                    color: Some(Color::Blue),
                })
                .add_item(DiagnosticItem {
                    message: format!("found type: {}", arg_ty),
                    span: arg.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::InvalidReturnType {
                return_ty,
                expr_ty,
                method,
            } => Diagnostic::new()
                .with_pre_text(&format!("{}: invalid return type", error_str))
                .add_item(DiagnosticItem {
                    message: format!("declared return type: {}", return_ty),
                    span: method.span.clone(),
                    color: Some(Color::Blue),
                })
                .add_item(DiagnosticItem {
                    message: format!("found type: {}", expr_ty.inner),
                    span: expr_ty.span.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::UnknownVar(var) => Diagnostic::new()
                .with_pre_text(&format!(
                    "{}: unknown variable \"{}\"",
                    error_str, var.inner
                ))
                .add_item(DiagnosticItem {
                    message: "undefined variable".to_string(),
                    span: var.span.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::UnknownMethod(method) => Diagnostic::new()
                .with_pre_text(&format!(
                    "{}: unknown method \"{}\"",
                    error_str, method.inner
                ))
                .add_item(DiagnosticItem {
                    message: "undefined method".to_string(),
                    span: method.span.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::IndexingScalar { ident, ty } => Diagnostic::new()
                .with_pre_text(&format!(
                    "{}: indexing a scalar variable \"{}\"",
                    error_str, ident.inner
                ))
                .add_item(DiagnosticItem {
                    message: format!("type: {}", ty),
                    span: ident.span.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::InvalidArrayIndex(ty) => Diagnostic::new()
                .with_pre_text(&format!("{}: invalid array index", error_str))
                .add_item(DiagnosticItem {
                    message: format!("expecting int, found: {}", ty.inner),
                    span: ty.span.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::InvalidLen { ident, ty } => Diagnostic::new()
                .with_pre_text(&format!("{}: invalid len", error_str))
                .add_item(DiagnosticItem {
                    message: format!("expecting array, found: {}", ty),
                    span: ident.span.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::InvalidCondition(expr) => Diagnostic::new()
                .with_pre_text(&format!("{}: invalid condition", error_str))
                .add_item(DiagnosticItem {
                    message: format!("expecting bool, found: {}", expr.inner),
                    span: expr.span.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::InvalidBinOpTypes { op, lhs, rhs } => Diagnostic::new()
                .with_pre_text(&format!(
                    "{}: invalid types for binary operation {}",
                    error_str, op
                ))
                .add_item(DiagnosticItem {
                    message: format!("lhs type: {}", lhs.inner),
                    span: lhs.span.clone(),
                    color: Some(Color::Red),
                })
                .add_item(DiagnosticItem {
                    message: format!("rhs type: {}", rhs.inner),
                    span: rhs.span.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::InvalidUnaryOpType { op, ty } => Diagnostic::new()
                .with_pre_text(&format!(
                    "{}: invalid type for unary operation {}",
                    error_str, op
                ))
                .add_item(DiagnosticItem {
                    message: format!("type: {}", ty.inner),
                    span: ty.span.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::MismatchedAssignmentTypes {
                rhs_ty,
                lhs_ty,
                decl_site,
            } => Diagnostic::new()
                .with_pre_text(&format!("{}: mismatched assignment types", error_str))
                .add_item(DiagnosticItem {
                    message: format!("declared type: {}", lhs_ty),
                    span: decl_site.span.clone(),
                    color: Some(Color::Blue),
                })
                .add_item(DiagnosticItem {
                    message: format!("found type: {}", rhs_ty.inner),
                    span: rhs_ty.span.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::NonNumericUpdate(ty) => Diagnostic::new()
                .with_pre_text(&format!(
                    "{}: non-numeric update (+=, -=, *=, /=, %=, ++, --)",
                    error_str
                ))
                .add_item(DiagnosticItem {
                    message: format!("expecting int, found: {}", ty.inner),
                    span: ty.span.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::NonScalarAssignment {
                decl_site,
                update_site,
            } => Diagnostic::new()
                .with_pre_text(&format!("{}: non-scalar assignment", error_str))
                .add_item(DiagnosticItem {
                    message: "expecting scalar variable".to_string(),
                    span: decl_site.span.clone(),
                    color: Some(Color::Blue),
                })
                .add_item(DiagnosticItem {
                    message: "found non-scalar variable".to_string(),
                    span: update_site.span.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::ReassigningConst {
                decl_site,
                assign_site,
            } => Diagnostic::new()
                .with_pre_text(&format!("{}: reassigning const variable", error_str))
                .add_item(DiagnosticItem {
                    message: "const variable".to_string(),
                    span: decl_site.span.clone(),
                    color: Some(Color::Blue),
                })
                .add_item(DiagnosticItem {
                    message: "reassigned here".to_string(),
                    span: assign_site.span.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::InvalidBreak(span) => Diagnostic::new()
                .with_pre_text(&format!("{}: invalid break", error_str))
                .add_item(DiagnosticItem {
                    message: "break statement outside of loop".to_string(),
                    span: span.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::InvalidContinue(span) => Diagnostic::new()
                .with_pre_text(&format!("{}: invalid continue", error_str))
                .add_item(DiagnosticItem {
                    message: "continue statement outside of loop".to_string(),
                    span: span.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::InvalidIntLiteral(lit) => Diagnostic::new()
                .with_pre_text(&format!("{}: invalid int literal", error_str))
                .add_item(DiagnosticItem {
                    message: "should be in [-9223372036854775808, 9223372036854775807]".to_string(),
                    span: lit.span.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::InvalidLoopVariable {
                decl_site,
                use_site,
                ty,
            } => Diagnostic::new()
                .with_pre_text(&format!("{}: loop variable must be int", error_str))
                .add_item(DiagnosticItem {
                    message: format!("declared type: {}", ty),
                    span: decl_site.span.clone(),
                    color: Some(Color::Blue),
                })
                .add_item(DiagnosticItem {
                    message: "used here".to_string(),
                    span: use_site.span.clone(),
                    color: Some(Color::Red),
                }),
            SemanticError::InvalidCall {
                decl_site,
                use_site,
            } => Diagnostic::new()
                .with_pre_text(&format!(
                    "{}: \"{}\" is not a method",
                    error_str, decl_site.inner
                ))
                .add_item(DiagnosticItem {
                    message: "defined here".to_string(),
                    span: decl_site.span.clone(),
                    color: Some(Color::Blue),
                })
                .add_item(DiagnosticItem {
                    message: "attempted call here".to_string(),
                    span: use_site.span.clone(),
                    color: Some(Color::Red),
                }),
        }
    }
}
