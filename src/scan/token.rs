use num_bigint::BigInt;

use super::location::Span;

#[rustfmt::skip]
#[derive(Debug, Clone, PartialEq, Eq, strum::Display)]
pub enum Token {
    // Keywords
    #[strum(to_string = "bool"    )]    Bool,
    #[strum(to_string = "break"   )]    Break,
    #[strum(to_string = "const"   )]    Const,
    #[strum(to_string = "import"  )]    Import,
    #[strum(to_string = "continue")]    Continue,
    #[strum(to_string = "else"    )]    Else,
    #[strum(to_string = "for"     )]    For,
    #[strum(to_string = "while"   )]    While,
    #[strum(to_string = "if"      )]    If,
    #[strum(to_string = "int"     )]    Int,
    #[strum(to_string = "return"  )]    Return,
    #[strum(to_string = "len"     )]    Len,
    #[strum(to_string = "void"    )]    Void,

    // Fillers
    // WhiteSpace,
    // Comment,

    // Identifier
    #[strum(to_string = "IDENTIFIER {0}")] 
    Identifier(String),

    // Literals
    #[strum(to_string = "INTLITERAL {0}")]
    IntLiteral(BigInt), // BigInt is used to represent arbitrary precision integers, we defer range checking to future stages
    #[strum(to_string = "CHARLITERAL '{0}'")]
    CharLiteral(char),
    #[strum(to_string = "STRINGLITERAL \"{0}\"")]
    StringLiteral(String),
    #[strum(to_string = "BOOLLITERAL {0}")]
    BoolLiteral(bool),

    // Symbols,
    #[strum(to_string = ";")]   Semicolon,
    #[strum(to_string = ",")]   Comma,
    #[strum(to_string = "(")]   OpenParen,
    #[strum(to_string = ")")]   CloseParen,
    #[strum(to_string = "{")]   OpenBrace,
    #[strum(to_string = "}")]   CloseBrace,
    #[strum(to_string = "[")]   OpenBracket,
    #[strum(to_string = "]")]   CloseBracket,

    // Arithmetic Operators
    #[strum(to_string = "+")]   Add,
    #[strum(to_string = "-")]   Sub, // Both unary and binary
    #[strum(to_string = "*")]   Mul,
    #[strum(to_string = "/")]   Div,
    #[strum(to_string = "%")]   Mod,

    // Logical Operators
    #[strum(to_string = "!" )]  Not,
    #[strum(to_string = "&&")]  And,
    #[strum(to_string = "||")]  Or,

    // Self-Assignment Operators
    #[strum(to_string = "=" )]  Assign,
    #[strum(to_string = "+=")]  AddAssign,
    #[strum(to_string = "-=")]  SubAssign,
    #[strum(to_string = "*=")]  MulAssign,
    #[strum(to_string = "/=")]  DivAssign,
    #[strum(to_string = "%=")]  ModAssign,
    #[strum(to_string = "++")]  Increment,
    #[strum(to_string = "--")]  Decrement,

    // Comparison Operators
    #[strum(to_string = "==")]  Equal,
    #[strum(to_string = "!=")]  Unequal,
    #[strum(to_string = "<" )]  LessThan,
    #[strum(to_string = "<=")]  LessThanOrEqual,
    #[strum(to_string = ">" )]  GreaterThan,
    #[strum(to_string = ">=")]  GreaterThanOrEqual,
}

#[derive(Debug, Clone)]
pub struct TokenWithSpan {
    pub token: Token,
    pub span: Span,
}
