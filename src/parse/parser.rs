#![allow(dead_code)]
use std::fmt;

use crate::{
    parse::ast::{BinOp, MethodCallArg},
    scan::{
        location::Span,
        token::{Token, TokenWithSpan},
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
        found: TokenWithSpan,
    },
    IntegerOutOfRange(TokenWithSpan),
}

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParserError::UnexpectedToken { expected, found } => {
                write!(
                    f,
                    "{:?}: unexpected token {:?}, expected one of {:?}",
                    found.span.start, found.token, expected
                )
            }
            ParserError::IntegerOutOfRange(token) => {
                write!(
                    f,
                    "{:?}: integer literal out of range: {:?}",
                    token.span.start, token.token
                )
            }
        }
    }
}

pub struct Parser {
    /// The token stream to parse.
    tokens: Vec<TokenWithSpan>,
    /// The current position in the token stream.
    pos: usize,
    /// A list of recovered errors.
    errors: Vec<ParserError>,
}

macro_rules! token {
    ($p:pat) => {
        TokenWithSpan { token: $p, .. }
    };
    ($p:pat, $s:ident) => {
        TokenWithSpan {
            token: $p,
            span: $s,
        }
    };
}

macro_rules! unexpected {
    ($tws:expr, $($p:expr),+) => {
        return Err(ParserError::UnexpectedToken {
            expected: vec![$($p),+],
            found: $tws.clone(),
        })
    };
}

macro_rules! expect_advance {
    ($self:ident, $t:path) => {
        match $self.current() {
            token![$t] => {
                $self.advance();
            }
            t => unexpected!(t, $t),
        }
    };
}

impl Parser {
    pub fn new(mut tokens: Vec<TokenWithSpan>) -> Self {
        // Add an EOF token to the end of the token stream for easier parsing.
        match tokens.last() {
            Some(TokenWithSpan {
                token: Token::EndOfFile,
                ..
            }) => {}
            Some(tok) => tokens.push(TokenWithSpan {
                token: Token::EndOfFile,
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

    pub fn lookahead(&self, by: usize) -> &TokenWithSpan {
        &self.tokens[(self.pos + by).min(self.tokens.len() - 1)]
    }

    pub fn current(&self) -> &TokenWithSpan {
        self.lookahead(0)
    }

    pub fn parse_ident(&mut self) -> Result<Ident, ParserError> {
        match self.current() {
            token![Token::Identifier(ident), span] => {
                let ident = Ident {
                    value: ident.clone(),
                    span: span.clone(),
                };
                self.advance();
                Ok(ident)
            }
            t => unexpected!(t, Token::Identifier(Default::default())),
        }
    }

    pub fn parse_location(&mut self) -> Result<Location, ParserError> {
        let ident = self.parse_ident()?;
        match self.current() {
            token![Token::OpenBracket] => {
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
            match self.current() {
                token![Token::CloseParen] => {
                    self.advance();
                    break;
                }
                token![Token::StringLiteral(value), span] => {
                    args.push(MethodCallArg::StringLiteral {
                        value: value.clone(),
                        span: span.clone(),
                    });
                    self.advance();
                    match self.current() {
                        token![Token::Comma] => self.advance(),
                        token![Token::CloseParen] => continue,
                        t => unexpected!(t, Token::Comma, Token::CloseParen),
                    }
                }
                _ => {
                    args.push(MethodCallArg::Expr(self.parse_expr()?));
                    match self.current() {
                        token![Token::Comma] => self.advance(),
                        token![Token::CloseParen] => continue,
                        t => unexpected!(t, Token::Comma, Token::CloseParen),
                    }
                }
            }
        }
        Ok(MethodCall { name, args })
    }

    pub fn parse_literal(&mut self) -> Result<RuntimeLiteral, ParserError> {
        match self.current() {
            token![Token::IntLiteral(value), span] => {
                let lit = IntLiteral {
                    value: value
                        .try_into()
                        .map_err(|_| ParserError::IntegerOutOfRange(self.current().clone()))?,
                    span: span.clone(),
                };
                self.advance();
                Ok(RuntimeLiteral::Int(lit))
            }
            token![Token::BoolLiteral(value), span] => {
                let lit = BoolLiteral {
                    value: *value,
                    span: span.clone(),
                };
                self.advance();
                Ok(RuntimeLiteral::Bool(lit))
            }
            token![Token::CharLiteral(value), span] => {
                let lit = CharLiteral {
                    value: *value,
                    span: span.clone(),
                };
                Ok(RuntimeLiteral::Char(lit))
            }
            t => unexpected!(
                t,
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
            let (op, cur_prec) = token_to_op_and_prec(self.current());
            if cur_prec < min_precedence {
                break;
            }
            self.advance();
            let mut rhs = self.parse_expr_atom()?;
            loop {
                let (_, new_prec) = token_to_op_and_prec(self.current());
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

        fn token_to_op_and_prec(t: &TokenWithSpan) -> (BinOp, i32) {
            match t {
                token![Token::Or] => (BinOp::Or, 0),
                token![Token::And] => (BinOp::And, 1),
                token![Token::Equal] => (BinOp::Equal, 2),
                token![Token::Unequal] => (BinOp::NotEqual, 2),
                token![Token::LessThan] => (BinOp::Less, 3),
                token![Token::LessThanOrEqual] => (BinOp::LessEqual, 3),
                token![Token::GreaterThan] => (BinOp::Greater, 3),
                token![Token::GreaterThanOrEqual] => (BinOp::GreaterEqual, 3),
                token![Token::Add] => (BinOp::Add, 4),
                token![Token::Sub] => (BinOp::Sub, 4),
                token![Token::Mul] => (BinOp::Mul, 5),
                token![Token::Div] => (BinOp::Div, 5),
                token![Token::Mod] => (BinOp::Mod, 5),
                // The exact binop does not matter here, as it will be ignored due to the min_precedence check.
                _ => (BinOp::Or, i32::min_value()),
            }
        }
    }

    pub fn parse_expr_atom(&mut self) -> Result<Expr, ParserError> {
        match self.current() {
            token![Token::Identifier(_)] => {
                if matches!(self.lookahead(1), token![Token::OpenParen]) {
                    Ok(Expr::Call(self.parse_call()?))
                } else {
                    Ok(Expr::Location(self.parse_location()?))
                }
            }
            token![Token::IntLiteral(_)]
            | token![Token::BoolLiteral(_)]
            | token![Token::CharLiteral(_)] => Ok(Expr::Literal(self.parse_literal()?)),
            token![Token::Len] => {
                self.advance();
                expect_advance!(self, Token::OpenParen);
                let ident = self.parse_ident()?;
                expect_advance!(self, Token::CloseParen);
                Ok(Expr::Len(ident))
            }
            token![Token::OpenParen] => {
                self.advance();
                let expr = self.parse_expr()?;
                expect_advance!(self, Token::CloseParen);
                Ok(expr)
            }
            token![Token::Sub] => {
                self.advance();
                let expr = self.parse_expr_atom()?;
                Ok(Expr::UnaryOp {
                    op: UnaryOp::Neg,
                    expr: Box::new(expr),
                })
            }
            token![Token::Not] => {
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
