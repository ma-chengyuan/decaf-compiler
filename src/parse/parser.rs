#![allow(dead_code)]
use std::fmt;

use crate::{
    parse::ast::{BinOp, MethodCallArg},
    scan::{
        location::{Span, Spanned},
        token::Token,
    },
};

use super::ast::{
    BoolLiteral, CharLiteral, Expr, Ident, IntLiteral, Location, MethodCall, RuntimeLiteral,
    UnaryOp,
};

#[derive(Debug, Clone)]
pub enum ParserError {
    UnexpectedToken {
        expected: Vec<Token>,
        found: Spanned<Token>,
    },
    IntegerOutOfRange(Spanned<Token>),
}

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParserError::UnexpectedToken { expected, found } => {
                write!(
                    f,
                    "{:?}: unexpected token {:?}, expected one of {:?}",
                    found.span.start, found.inner, expected
                )
            }
            ParserError::IntegerOutOfRange(token) => {
                write!(
                    f,
                    "{:?}: integer literal out of range: {:?}",
                    token.span.start, token.inner
                )
            }
        }
    }
}

pub struct Parser {
    /// The token stream to parse.
    tokens: Vec<Spanned<Token>>,
    /// The current position in the token stream.
    pos: usize,
    /// A list of recovered errors.
    errors: Vec<ParserError>,
}

macro_rules! unexpected {
    ($self:ident, $($p:expr),+) => {
        return Err(ParserError::UnexpectedToken {
            expected: vec![$($p),+],
            found: $self.current().clone(),
        })
    };
}

macro_rules! expect_advance {
    ($self:ident, $t:path) => {
        match &$self.current().inner {
            $t => {
                $self.advance();
            }
            _ => unexpected!($self, $t),
        }
    };
}

impl Parser {
    pub fn new(mut tokens: Vec<Spanned<Token>>) -> Self {
        // Add an EOF token to the end of the token stream for easier parsing.
        match tokens.last() {
            Some(Spanned {
                inner: Token::EndOfFile,
                ..
            }) => {}
            Some(tok) => tokens.push(Spanned {
                inner: Token::EndOfFile,
                span: Span {
                    start: tok.span.end.clone(),
                    end: tok.span.end.clone(),
                },
            }),
            None => panic!("empty token stream"),
        }
        Self {
            tokens,
            pos: 0,
            errors: Vec::new(),
        }
    }

    pub fn advance(&mut self) {
        self.pos = (self.pos + 1).min(self.tokens.len() - 1);
    }

    pub fn lookahead(&self, by: usize) -> &Spanned<Token> {
        &self.tokens[(self.pos + by).min(self.tokens.len() - 1)]
    }

    pub fn current(&self) -> &Spanned<Token> {
        self.lookahead(0)
    }

    pub fn parse_ident(&mut self) -> Result<Ident, ParserError> {
        match &self.current().inner {
            Token::Identifier(ident) => {
                let ident = Ident {
                    inner: ident.clone(),
                    span: self.current().span.clone(),
                };
                self.advance();
                Ok(ident)
            }
            _ => unexpected!(self, Token::Identifier(Default::default())),
        }
    }

    pub fn parse_location(&mut self) -> Result<Location, ParserError> {
        let ident = self.parse_ident()?;
        match &self.current().inner {
            Token::OpenBracket => {
                self.advance();
                let expr = self.parse_expr()?;
                expect_advance!(self, Token::CloseBracket);
                Ok(Location::ArrayAccess {
                    ident: Box::new(Location::Ident(ident)),
                    index: Box::new(expr),
                })
            }
            _ => Ok(Location::Ident(ident)),
        }
    }

    pub fn parse_call(&mut self) -> Result<MethodCall, ParserError> {
        let name = self.parse_ident()?;
        let mut args = Vec::new();
        expect_advance!(self, Token::OpenParen);
        loop {
            match &self.current().inner {
                Token::CloseParen => {
                    self.advance();
                    break;
                }
                Token::StringLiteral(value) => {
                    args.push(MethodCallArg::StringLiteral(Spanned {
                        inner: value.clone(),
                        span: self.current().span.clone(),
                    }));
                    self.advance();
                    match self.current().inner {
                        Token::Comma => self.advance(),
                        Token::CloseParen => continue,
                        _ => unexpected!(self, Token::Comma, Token::CloseParen),
                    }
                }
                _ => {
                    args.push(MethodCallArg::Expr(self.parse_expr()?));
                    match self.current().inner {
                        Token::Comma => self.advance(),
                        Token::CloseParen => continue,
                        _ => unexpected!(self, Token::Comma, Token::CloseParen),
                    }
                }
            }
        }
        Ok(MethodCall { name, args })
    }

    pub fn parse_literal(&mut self) -> Result<RuntimeLiteral, ParserError> {
        match &self.current().inner {
            Token::IntLiteral(value) => {
                let lit = IntLiteral {
                    inner: value
                        .try_into()
                        .map_err(|_| ParserError::IntegerOutOfRange(self.current().clone()))?,
                    span: self.current().span.clone(),
                };
                self.advance();
                Ok(RuntimeLiteral::Int(lit))
            }
            Token::BoolLiteral(value) => {
                let lit = BoolLiteral {
                    inner: *value,
                    span: self.current().span.clone(),
                };
                self.advance();
                Ok(RuntimeLiteral::Bool(lit))
            }
            Token::CharLiteral(value) => {
                let lit = CharLiteral {
                    inner: *value,
                    span: self.current().span.clone(),
                };
                Ok(RuntimeLiteral::Char(lit))
            }
            _ => unexpected!(
                self,
                Token::IntLiteral(Default::default()),
                Token::BoolLiteral(Default::default()),
                Token::CharLiteral(Default::default())
            ),
        }
    }

    pub fn parse_expr(&mut self) -> Result<Expr, ParserError> {
        let lhs = self.parse_expr_atom()?;
        self.parse_expr_op_prec(lhs, 0)
    }

    pub fn parse_expr_op_prec(
        &mut self,
        mut lhs: Expr,
        min_precedence: i32,
    ) -> Result<Expr, ParserError> {
        // Our beloved operator-precedence parsing algorithm.
        // See https://en.wikipedia.org/wiki/Operator-precedence_parser
        loop {
            let (op, cur_prec) = token_to_op_and_prec(&self.current().inner);
            if cur_prec < min_precedence {
                break;
            }
            self.advance();
            let mut rhs = self.parse_expr_atom()?;
            loop {
                let (_, new_prec) = token_to_op_and_prec(&self.current().inner);
                if new_prec <= cur_prec {
                    break;
                } else {
                    rhs = self.parse_expr_op_prec(rhs, cur_prec + 1)?;
                }
            }
            lhs = Expr::BinOp {
                lhs: Box::new(lhs),
                op,
                rhs: Box::new(rhs),
            };
        }
        return Ok(lhs);

        fn token_to_op_and_prec(t: &Token) -> (BinOp, i32) {
            match t {
                Token::Or => (BinOp::Or, 0),
                Token::And => (BinOp::And, 1),
                Token::Equal => (BinOp::Equal, 2),
                Token::Unequal => (BinOp::NotEqual, 2),
                Token::LessThan => (BinOp::Less, 3),
                Token::LessThanOrEqual => (BinOp::LessEqual, 3),
                Token::GreaterThan => (BinOp::Greater, 3),
                Token::GreaterThanOrEqual => (BinOp::GreaterEqual, 3),
                Token::Add => (BinOp::Add, 4),
                Token::Sub => (BinOp::Sub, 4),
                Token::Mul => (BinOp::Mul, 5),
                Token::Div => (BinOp::Div, 5),
                Token::Mod => (BinOp::Mod, 5),
                // The exact binop does not matter here, as it will be ignored due to the min_precedence check.
                _ => (BinOp::Or, i32::min_value()),
            }
        }
    }

    pub fn parse_expr_atom(&mut self) -> Result<Expr, ParserError> {
        match self.current().inner {
            Token::Identifier(_) => {
                if matches!(self.lookahead(1).inner, Token::OpenParen) {
                    Ok(Expr::Call(self.parse_call()?))
                } else {
                    Ok(Expr::Location(self.parse_location()?))
                }
            }
            Token::IntLiteral(_) | Token::BoolLiteral(_) | Token::CharLiteral(_) => {
                Ok(Expr::Literal(self.parse_literal()?))
            }
            Token::Len => {
                self.advance();
                expect_advance!(self, Token::OpenParen);
                let ident = self.parse_ident()?;
                expect_advance!(self, Token::CloseParen);
                Ok(Expr::Len(ident))
            }
            Token::OpenParen => {
                self.advance();
                let expr = self.parse_expr()?;
                expect_advance!(self, Token::CloseParen);
                Ok(expr)
            }
            Token::Sub => {
                self.advance();
                let expr = self.parse_expr_atom()?;
                Ok(Expr::UnaryOp {
                    op: UnaryOp::Neg,
                    expr: Box::new(expr),
                })
            }
            Token::Not => {
                self.advance();
                let expr = self.parse_expr_atom()?;
                Ok(Expr::UnaryOp {
                    op: UnaryOp::Not,
                    expr: Box::new(expr),
                })
            }
            _ => todo!(),
        }
    }
}
