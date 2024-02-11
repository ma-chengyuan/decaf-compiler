use num_bigint::BigInt;

use super::location::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    // Keywords
    Bool,
    Break,
    Const,
    Import,
    Continue,
    Else,
    For,
    While,
    If,
    Int,
    Return,
    Len,
    Void,

    // Fillers
    // WhiteSpace,
    // Comment,

    // Identifier
    Identifier(String),

    // Literals
    IntLiteral(BigInt), // BigInt is used to represent arbitrary precision integers, we defer range checking to future stages
    CharLiteral(char),
    StringLiteral(String),
    BoolLiteral(bool),

    // Symbols,
    Semicolon,
    Comma,
    OpenParen,
    CloseParen,
    OpenBrace,
    CloseBrace,
    OpenBracket,
    CloseBracket,

    // Arithmetic Operators
    Add,
    Sub, // Both unary and binary
    Mul,
    Div,
    Mod,

    // Logical Operators
    Not,
    And,
    Or,

    // Self-Assignment Operators
    Assign,
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    ModAssign,
    Increment,
    Decrement,

    // Comparison Operators
    Equal,
    Unequal,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,

    // A special token to represent the end of file
    EndOfFile,
}

#[derive(Debug, Clone)]
pub struct TokenWithSpan {
    pub token: Token,
    pub span: Span,
}
