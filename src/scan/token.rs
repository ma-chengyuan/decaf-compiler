use num_bigint::BigInt;
use std::fmt;

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

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Bool => write!(f, "bool"),
            Token::Break => write!(f, "break"),
            Token::Const => write!(f, "const"),
            Token::Import => write!(f, "import"),
            Token::Continue => write!(f, "continue"),
            Token::Else => write!(f, "else"),
            Token::For => write!(f, "for"),
            Token::While => write!(f, "while"),
            Token::If => write!(f, "if"),
            Token::Int => write!(f, "int"),
            Token::Return => write!(f, "return"),
            Token::Len => write!(f, "len"),
            Token::Void => write!(f, "void"),
            Token::Identifier(s) => write!(f, "{}", s),
            Token::IntLiteral(i) => write!(f, "{}", i),
            Token::CharLiteral(c) => write!(f, "{:?}", c),
            Token::StringLiteral(s) => write!(f, "{:?}", s),
            Token::BoolLiteral(b) => write!(f, "{}", b),
            Token::Semicolon => write!(f, ";"),
            Token::Comma => write!(f, ","),
            Token::OpenParen => write!(f, "("),
            Token::CloseParen => write!(f, ")"),
            Token::OpenBrace => write!(f, "{{"),
            Token::CloseBrace => write!(f, "}}"),
            Token::OpenBracket => write!(f, "["),
            Token::CloseBracket => write!(f, "]"),
            Token::Add => write!(f, "+"),
            Token::Sub => write!(f, "-"),
            Token::Mul => write!(f, "*"),
            Token::Div => write!(f, "/"),
            Token::Mod => write!(f, "%"),
            Token::Not => write!(f, "!"),
            Token::And => write!(f, "&&"),
            Token::Or => write!(f, "||"),
            Token::Assign => write!(f, "="),
            Token::AddAssign => write!(f, "+="),
            Token::SubAssign => write!(f, "-="),
            Token::MulAssign => write!(f, "*="),
            Token::DivAssign => write!(f, "/="),
            Token::ModAssign => write!(f, "%="),
            Token::Increment => write!(f, "++"),
            Token::Decrement => write!(f, "--"),
            Token::Equal => write!(f, "=="),
            Token::Unequal => write!(f, "!="),
            Token::LessThan => write!(f, "<"),
            Token::LessThanOrEqual => write!(f, "<="),
            Token::GreaterThan => write!(f, ">"),
            Token::GreaterThanOrEqual => write!(f, ">="),
            Token::EndOfFile => write!(f, "<EOF>"),
        }
    }
}
