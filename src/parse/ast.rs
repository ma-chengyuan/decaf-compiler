#![allow(dead_code)]
use num_bigint::BigInt;

use crate::scan::location::Spanned;

pub type Ident = Spanned<String>;
pub type IntLiteral = Spanned<BigInt>;
pub type BoolLiteral = Spanned<bool>;
pub type CharLiteral = Spanned<char>;
pub type StringLiteral = Spanned<String>;

/// Literal value of runtime values.
#[derive(Debug, Clone)]
pub enum RuntimeLiteral {
    Int(IntLiteral),
    Bool(BoolLiteral),
    Char(CharLiteral),
    // No string literal for now.
}

/// A memory location, or "lvalue" in C/C++ terminology.
#[derive(Debug, Clone)]
pub enum Location {
    Ident(Ident),
    ArrayAccess {
        // Decaf supports 1D array for now, but use Box<Location> for future support.
        ident: Box<Location>,
        index: Box<Expr>,
    },
}

/// Argument to a method call. String literal is only supported for external calls.
#[derive(Debug, Clone)]
pub enum MethodCallArg {
    Expr(Expr),
    StringLiteral(StringLiteral),
}

/// A method call.
#[derive(Debug, Clone)]
pub struct MethodCall {
    pub name: Ident,
    pub args: Vec<MethodCallArg>,
}

/// A expression in the language. Corresponds to `expr` in the spec.
#[derive(Debug, Clone)]
pub enum Expr {
    Location(Location),
    Call(MethodCall),
    Literal(RuntimeLiteral),
    Len(Ident),
    BinOp {
        lhs: Box<Expr>,
        op: BinOp,
        rhs: Box<Expr>,
    },
    UnaryOp {
        op: UnaryOp,
        expr: Box<Expr>,
    },
}

/// Binary operators.
#[derive(Debug, Clone)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Equal,
    NotEqual,
    And,
    Or,
}

/// Unary operators.
#[derive(Debug, Clone)]
pub enum UnaryOp {
    Neg,
    Not,
}

/// Runtime type of a value.
#[derive(Debug, Clone)]
pub enum Type {
    Int,
    Bool,
}

// Field declarations

/// Corresponds to field_decl in the spec.
#[derive(Debug, Clone)]
pub struct FieldDecl {
    pub is_const: bool,
    pub r#type: Type,
    pub decls: Vec<FieldDeclaration>,
}

/// Defines the name and the dimensions of the field to be declared.
#[derive(Debug, Clone)]
pub enum FieldDeclarator {
    Ident(Ident),
    Array {
        base: Box<FieldDeclarator>,
        size: Option<IntLiteral>,
    }, // Use Box<FieldDeclarator> for future support.
}

impl FieldDeclarator {
    pub fn ident(&self) -> &Ident {
        match self {
            FieldDeclarator::Ident(ident) => ident,
            FieldDeclarator::Array { base, .. } => base.ident(),
        }
    }
}

/// Initializer for a field declaration.
#[derive(Debug, Clone)]
pub enum Initializer {
    Literal(RuntimeLiteral),
    Array(Vec<Initializer>),
}

/// A declaration of a field includes a declarator and an optional initializer.
///
/// Need to awkwardly separate FieldDecl and FieldDeclaration a declaration
/// statement can declare multiple fields.
#[derive(Debug, Clone)]
pub struct FieldDeclaration {
    pub declarator: FieldDeclarator,
    pub initializer: Option<Initializer>,
}

/// A statement in the language. Corresponds to `statement` in the spec.
#[derive(Debug, Clone)]
pub enum Stmt {
    Update {
        location: Location,
        op: UpdateOp,
    },
    Call(MethodCall),
    If {
        condition: Expr,
        then_block: Block,
        else_block: Option<Block>,
    },
    For {
        loop_var_name: Ident,
        init: Expr,
        cond: Expr,
        update: Box<Stmt>, // Constrained to location assign and method call by the parser, for now.
        block: Block,
    },
    While {
        condition: Expr,
        block: Block,
    },
    Return(Option<Expr>),
    Break,
    Continue,
}

/// Corresponds to `block` in the spec.
#[derive(Debug, Clone)]
pub struct Block {
    pub field_decls: Vec<FieldDecl>,
    pub stmts: Vec<Stmt>,
}

/// Corresponds to `assign_expr` in the spec.
#[derive(Debug, Clone)]
pub enum UpdateOp {
    Increment,
    Decrement,
    Assign(Expr),
    AddAssign(Expr),
    SubAssign(Expr),
    MulAssign(Expr),
    DivAssign(Expr),
    ModAssign(Expr),
}

/// Corresponds to `import_decl` in the spec.
#[derive(Debug, Clone)]
pub struct ImportDecl(pub Ident);

#[derive(Debug, Clone)]
pub struct MethodParam {
    pub r#type: Type,
    pub name: Ident,
}

/// Corresponds to `method_decl` in the spec.
#[derive(Debug, Clone)]
pub struct MethodDecl {
    pub name: Ident,
    pub return_type: Option<Type>,
    pub params: Vec<MethodParam>,
    pub body: Block,
}

/// Corresponds to `program` in the spec.
#[derive(Debug, Clone)]
pub struct Program {
    pub import_decls: Vec<ImportDecl>,
    pub field_decls: Vec<FieldDecl>,
    pub method_decls: Vec<MethodDecl>,
}
