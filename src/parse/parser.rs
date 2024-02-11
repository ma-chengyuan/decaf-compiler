#![allow(dead_code)]

use std::{cell::RefCell, rc::Rc};

use crate::{
    parse::ast::{BinOp, MethodCallArg, MethodParam},
    scan::{
        location::{Span, Spanned},
        token::Token,
    },
};

use super::{
    ast::{
        Block, BoolLiteral, CharLiteral, Expr, FieldDecl, FieldDeclaration, FieldDeclarator, Ident,
        ImportDecl, Initializer, IntLiteral, Location, MethodCall, MethodDecl, Program,
        RuntimeLiteral, Stmt, Type, UnaryOp, UpdateOp,
    },
    error::{ParseErrorExt, ParserError, ParserErrorKind},
};

#[derive(Debug, Clone)]
pub enum ParserContext {
    MethodDecl(Ident),
    FieldDecl(Ident),
    MethodCall(Ident),
}

pub struct Parser {
    /// The token stream to parse.
    tokens: Vec<Spanned<Token>>,
    /// The current position in the token stream.
    pos: usize,
    /// A list of recovered errors.
    errors: Rc<RefCell<Vec<ParserError>>>,
}

macro_rules! unexpected {
    ($self:ident, $($p:expr),+) => {
        return Err(ParserError {
            kind: Box::new(ParserErrorKind::UnexpectedToken {
                expecting: vec![$($p),+],
                found: $self.current().clone(),
            }),
            contexts: vec![]
        })
    };
    ($self:ident[$scope:ident], $($p:expr),+) => {
        return Err(ParserError {
            kind: Box::new(ParserErrorKind::UnexpectedToken {
                expecting: vec![$($p),+],
                found: $self.current().clone(),
            }),
            contexts: vec![$scope.context.clone()]
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
    ($self:ident[$scope:ident], $t:path) => {
        match &$self.current().inner {
            $t => {
                $self.advance();
            }
            _ => unexpected!($self[$scope], $t),
        }
    };
}

macro_rules! delimited {
    ($self:ident, $delimiter:path, $close:path, $($matcher:pat $(if $pred:expr)* => $result:expr),*) => {{
        let mut empty = true;
        loop {
            match &$self.current().inner {
                $close if empty => { $self.advance(); break; }
                $($matcher $(if $pred)* => {
                    $result;
                    match &$self.current().inner {
                        $delimiter => { $self.advance(); empty = false; continue; }
                        $close => { $self.advance(); break; },
                        _ => unexpected!($self, $delimiter, $close),
                    }
                },)*
                #[allow(unreachable_patterns)]
                _ => unexpected!($self, $delimiter, $close),
            }
        }
    }};
    ($self:ident[$scope:ident], $delimiter:path, $close:path, $($matcher:pat $(if $pred:expr)* => $result:expr),*) => {{
        let mut empty = true;
        loop {
            match &$self.current().inner {
                $close if empty => { $self.advance(); break; }
                $($matcher $(if $pred)* => {
                    $result;
                    match &$self.current().inner {
                        $delimiter => { $self.advance(); empty = false; continue; }
                        $close => { $self.advance(); break; },
                        _ => unexpected!($self[$scope], $delimiter, $close),
                    }
                },)*
                #[allow(unreachable_patterns)]
                _ => unexpected!($self[$scope], $delimiter, $close),
            }
        }
    }};
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
            errors: Default::default(),
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
        let scope = ParseScope::new(self, ParserContext::MethodCall(name.clone()));
        let mut args = Vec::new();
        expect_advance!(self[scope], Token::OpenParen);
        delimited! {
            self[scope], Token::Comma, Token::CloseParen,
            Token::StringLiteral(value) => {
                args.push(MethodCallArg::StringLiteral(Spanned {
                    inner: value.clone(),
                    span: self.current().span.clone(),
                }));
                self.advance();
            },
            _ => args.push(MethodCallArg::Expr(self.parse_expr().with_scope(&scope)?))
        }
        Ok(MethodCall { name, args })
    }

    pub fn parse_literal(&mut self) -> Result<RuntimeLiteral, ParserError> {
        match &self.current().inner {
            Token::IntLiteral(value) => {
                let lit = IntLiteral {
                    inner: value.try_into().map_err(|_| ParserError {
                        kind: Box::new(ParserErrorKind::IntegerOutOfRange(self.current().clone())),
                        contexts: vec![],
                    })?,
                    span: self.current().span.clone(),
                };
                self.advance();
                Ok(RuntimeLiteral::Int(lit))
            }
            Token::Sub => {
                self.advance();
                match &self.current().inner {
                    Token::IntLiteral(value) => {
                        let lit = IntLiteral {
                            inner: -value.try_into().map_err(|_| ParserError {
                                kind: Box::new(ParserErrorKind::IntegerOutOfRange(
                                    self.current().clone(),
                                )),
                                contexts: vec![],
                            })?,
                            span: self.current().span.clone(),
                        };
                        self.advance();
                        Ok(RuntimeLiteral::Int(lit))
                    }
                    _ => unexpected!(self, Token::IntLiteral(Default::default())),
                }
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
                self.advance();
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
            Token::Sub | Token::Not => {
                let op = match self.current().inner {
                    Token::Sub => UnaryOp::Neg,
                    Token::Not => UnaryOp::Not,
                    _ => unreachable!(),
                };
                self.advance();
                Ok(Expr::UnaryOp {
                    op,
                    expr: Box::new(self.parse_expr_atom()?),
                })
            }
            _ => unexpected!(
                self,
                Token::Identifier(Default::default()),
                Token::IntLiteral(Default::default()),
                Token::BoolLiteral(Default::default()),
                Token::CharLiteral(Default::default()),
                Token::Len,
                Token::OpenParen,
                Token::Sub,
                Token::Not
            ),
        }
    }

    pub fn parse_update_stmt(&mut self) -> Result<Stmt, ParserError> {
        let location = self.parse_location()?;
        match self.current().inner {
            Token::Increment | Token::Decrement => {
                let op = match self.current().inner {
                    Token::Increment => UpdateOp::Increment,
                    Token::Decrement => UpdateOp::Decrement,
                    _ => unreachable!(),
                };
                self.advance();
                Ok(Stmt::Update { location, op })
            }
            Token::Assign
            | Token::AddAssign
            | Token::SubAssign
            | Token::MulAssign
            | Token::DivAssign
            | Token::ModAssign => {
                let token = self.current().inner.clone();
                self.advance();
                let rhs = self.parse_expr()?;
                let op = match token {
                    Token::Assign => UpdateOp::Assign(rhs),
                    Token::AddAssign => UpdateOp::AddAssign(rhs),
                    Token::SubAssign => UpdateOp::SubAssign(rhs),
                    Token::MulAssign => UpdateOp::MulAssign(rhs),
                    Token::DivAssign => UpdateOp::DivAssign(rhs),
                    Token::ModAssign => UpdateOp::ModAssign(rhs),
                    _ => unreachable!(),
                };
                Ok(Stmt::Update { location, op })
            }
            _ => unexpected!(
                self,
                Token::Increment,
                Token::Decrement,
                Token::Assign,
                Token::AddAssign,
                Token::SubAssign,
                Token::MulAssign,
                Token::DivAssign,
                Token::ModAssign
            ),
        }
    }

    // Parsing statements

    pub fn parse_stmt(&mut self) -> Result<Stmt, ParserError> {
        match &self.current().inner {
            Token::Identifier(_) => {
                let ret = self.parse_for_update()?;
                expect_advance!(self, Token::Semicolon);
                Ok(ret)
            }
            Token::If => self.parse_if_stmt(),
            Token::While => self.parse_while_stmt(),
            Token::Return => self.parse_return_stmt(),
            Token::For => self.parse_for_stmt(),
            Token::Break => {
                self.advance();
                expect_advance!(self, Token::Semicolon);
                Ok(Stmt::Break)
            }
            Token::Continue => {
                self.advance();
                expect_advance!(self, Token::Semicolon);
                Ok(Stmt::Continue)
            }
            _ => unexpected!(
                self,
                Token::Identifier(Default::default()),
                Token::If,
                Token::While,
                Token::Return,
                Token::For,
                Token::Break,
                Token::Continue
            ),
        }
    }

    pub fn parse_for_update(&mut self) -> Result<Stmt, ParserError> {
        if self.lookahead(1).inner == Token::OpenParen {
            Ok(Stmt::Call(self.parse_call()?))
        } else {
            self.parse_update_stmt()
        }
    }

    pub fn parse_if_stmt(&mut self) -> Result<Stmt, ParserError> {
        expect_advance!(self, Token::If);
        expect_advance!(self, Token::OpenParen);
        let condition = self.parse_expr()?;
        expect_advance!(self, Token::CloseParen);
        let then_block = self.parse_block()?;
        let else_block = match &self.current().inner {
            Token::Else => {
                self.advance();
                Some(self.parse_block()?)
            }
            _ => None,
        };
        Ok(Stmt::If {
            condition,
            then_block,
            else_block,
        })
    }

    pub fn parse_while_stmt(&mut self) -> Result<Stmt, ParserError> {
        expect_advance!(self, Token::While);
        expect_advance!(self, Token::OpenParen);
        let condition = self.parse_expr()?;
        expect_advance!(self, Token::CloseParen);
        let block = self.parse_block()?;
        Ok(Stmt::While { condition, block })
    }

    pub fn parse_for_stmt(&mut self) -> Result<Stmt, ParserError> {
        expect_advance!(self, Token::For);
        expect_advance!(self, Token::OpenParen);
        let loop_var_name = self.parse_ident()?;
        expect_advance!(self, Token::Assign);
        let init = self.parse_expr()?;
        expect_advance!(self, Token::Semicolon);
        let cond = self.parse_expr()?;
        expect_advance!(self, Token::Semicolon);
        let update = self.parse_for_update()?;
        expect_advance!(self, Token::CloseParen);
        let block = self.parse_block()?;
        Ok(Stmt::For {
            loop_var_name,
            init,
            cond,
            update: Box::new(update),
            block,
        })
    }

    pub fn parse_return_stmt(&mut self) -> Result<Stmt, ParserError> {
        expect_advance!(self, Token::Return);
        let expr = match &self.current().inner {
            Token::Semicolon => None,
            _ => Some(self.parse_expr()?),
        };
        expect_advance!(self, Token::Semicolon);
        Ok(Stmt::Return(expr))
    }

    pub fn parse_block(&mut self) -> Result<Block, ParserError> {
        expect_advance!(self, Token::OpenBrace);
        let mut field_decls = Vec::new();
        let mut stmts = Vec::new();

        loop {
            match &self.current().inner {
                Token::CloseBrace => {
                    self.advance();
                    break;
                }
                Token::Int | Token::Bool | Token::Const if stmts.is_empty() => {
                    match self.parse_field_decl() {
                        Ok(decl) => field_decls.push(decl),
                        Err(e) => self.panic_recovery(e),
                    }
                }
                Token::EndOfFile => unexpected!(self, Token::CloseBrace),
                _ => match self.parse_stmt() {
                    Ok(stmt) => stmts.push(stmt),
                    Err(e) => self.panic_recovery(e),
                },
            }
        }
        Ok(Block { field_decls, stmts })
    }

    // Parsing field and method declaration

    pub fn parse_type(&mut self) -> Result<Type, ParserError> {
        match &self.current().inner {
            Token::Int => {
                self.advance();
                Ok(Type::Int)
            }
            Token::Bool => {
                self.advance();
                Ok(Type::Bool)
            }
            _ => unexpected!(self, Token::Int, Token::Bool),
        }
    }

    pub fn parse_field_declarator(&mut self) -> Result<FieldDeclarator, ParserError> {
        let declarator = FieldDeclarator::Ident(self.parse_ident()?);
        match self.current().inner {
            Token::OpenBracket => {
                self.advance();
                let scope =
                    ParseScope::new(self, ParserContext::FieldDecl(declarator.ident().clone()));
                let size = match &self.current().inner {
                    Token::IntLiteral(value) => {
                        let spanned = Spanned {
                            inner: value
                                .try_into()
                                .map_err(|_| ParserError {
                                    kind: Box::new(ParserErrorKind::IntegerOutOfRange(
                                        self.current().clone(),
                                    )),
                                    contexts: vec![],
                                })
                                .with_scope(&scope)?,
                            span: self.current().span.clone(),
                        };

                        self.advance();
                        Some(spanned)
                    }
                    Token::CloseBracket => None,
                    _ => unexpected!(
                        self[scope],
                        Token::IntLiteral(Default::default()),
                        Token::CloseBracket
                    ),
                };
                expect_advance!(self[scope], Token::CloseBracket);
                Ok(FieldDeclarator::Array {
                    base: Box::new(declarator),
                    size,
                })
            }
            _ => Ok(declarator),
        }
    }

    pub fn parse_initializer(&mut self) -> Result<Initializer, ParserError> {
        match &self.current().inner {
            Token::OpenBrace => {
                let token = self.current().clone();
                self.advance();
                let mut initializers = Vec::new();
                delimited! {
                    self, Token::Comma, Token::CloseBrace,
                    // TODO: support nested initializers
                    _ => initializers.push(Initializer::Literal(self.parse_literal()?))
                };
                if initializers.is_empty() {
                    return Err(ParserError {
                        kind: Box::new(ParserErrorKind::EmptyInitializer(token)),
                        contexts: vec![],
                    });
                }
                Ok(Initializer::Array(initializers))
            }
            _ => Ok(Initializer::Literal(self.parse_literal()?)),
        }
    }

    pub fn parse_field_decl(&mut self) -> Result<FieldDecl, ParserError> {
        let is_const = match self.current().inner {
            Token::Const => {
                self.advance();
                true
            }
            _ => false,
        };
        let r#type = self.parse_type()?;
        let mut decls = vec![];
        delimited! {
            self, Token::Comma, Token::Semicolon,
            _ => {
                let declarator = self.parse_field_declarator()?;
                let scope =
                    ParseScope::new(self, ParserContext::FieldDecl(declarator.ident().clone()));
                let initializer = match self.current().inner {
                    Token::Assign => {
                        self.advance();
                        Some(self.parse_initializer().with_scope(&scope)?)
                    }
                    _ => None,
                };
                decls.push(FieldDeclaration {
                    declarator,
                    initializer,
                });
            }
        }
        if decls.is_empty() {
            return Err(ParserError {
                kind: Box::new(ParserErrorKind::EmptyFieldDecl(self.current().clone())),
                contexts: vec![],
            });
        }
        Ok(FieldDecl {
            is_const,
            r#type,
            decls,
        })
    }

    // Parsing method declaration

    pub fn parse_method_decl(&mut self) -> Result<MethodDecl, ParserError> {
        let return_type = match &self.current().inner {
            Token::Void => {
                self.advance();
                None
            }
            _ => Some(self.parse_type()?),
        };
        let name = self.parse_ident()?;
        let scope = ParseScope::new(self, ParserContext::MethodDecl(name.clone()));
        expect_advance!(self[scope], Token::OpenParen);
        let mut params = vec![];
        delimited! {
            self[scope], Token::Comma, Token::CloseParen,
            _ => {
                let r#type = self.parse_type().with_scope(&scope)?;
                let name = self.parse_ident().with_scope(&scope)?;
                params.push(MethodParam { r#type, name });
            }
        }
        let body = self.parse_block().with_scope(&scope)?;
        Ok(MethodDecl {
            name,
            return_type,
            params,
            body,
        })
    }

    // Parsing import decl

    pub fn parse_import_decl(&mut self) -> Result<ImportDecl, ParserError> {
        expect_advance!(self, Token::Import);
        let ident = self.parse_ident()?;
        expect_advance!(self, Token::Semicolon);
        Ok(ImportDecl(ident))
    }

    // Parsing the entire program

    pub fn parse_program(&mut self) -> (Program, Vec<ParserError>) {
        let mut import_decls = vec![];
        let mut field_decls = vec![];
        let mut method_decls = vec![];

        loop {
            match &self.current().inner {
                Token::EndOfFile => break,
                Token::Import if field_decls.is_empty() && method_decls.is_empty() => {
                    match self.parse_import_decl() {
                        Ok(decl) => import_decls.push(decl),
                        Err(e) => self.panic_recovery(e),
                    }
                }
                Token::Const => match self.parse_field_decl() {
                    Ok(decl) => field_decls.push(decl),
                    Err(e) => self.panic_recovery(e),
                },
                Token::Void => match self.parse_method_decl() {
                    Ok(decl) => method_decls.push(decl),
                    Err(e) => self.panic_recovery(e),
                },
                Token::Int | Token::Bool => {
                    let method = !method_decls.is_empty()
                        || matches!(self.lookahead(2).inner, Token::OpenParen);
                    if method {
                        match self.parse_method_decl() {
                            Ok(decl) => method_decls.push(decl),
                            Err(e) => self.panic_recovery(e),
                        }
                    } else {
                        match self.parse_field_decl() {
                            Ok(decl) => field_decls.push(decl),
                            Err(e) => self.panic_recovery(e),
                        }
                    }
                }
                _ => {
                    let mut expected = vec![Token::Int, Token::Bool, Token::Void];
                    if field_decls.is_empty() && method_decls.is_empty() {
                        expected.push(Token::Import);
                    }
                    if method_decls.is_empty() {
                        expected.push(Token::Const);
                    }
                    self.panic_recovery(ParserError {
                        kind: Box::new(ParserErrorKind::UnexpectedToken {
                            expecting: expected,
                            found: self.current().clone(),
                        }),
                        contexts: vec![],
                    });
                    self.advance();
                }
            }
        }
        let mut errors = self.errors.borrow_mut();
        let all_errors = errors.clone();
        errors.clear();
        (
            Program {
                import_decls,
                field_decls,
                method_decls,
            },
            all_errors,
        )
    }

    // Error recovery

    pub fn panic_recovery(&mut self, err: ParserError) {
        self.advance();
        loop {
            match &self.current().inner {
                // Silently gobble the semicolon and continue parsing.
                Token::Semicolon => {
                    self.advance();
                    break;
                }
                Token::CloseBrace // In a block: jump to the closing brace.
                | Token::EndOfFile // For statements: jump to the next starting statement.
                | Token::If
                | Token::While
                | Token::For
                | Token::Return
                | Token::Break
                | Token::Continue
                | Token::Const // Or the next declaration?
                | Token::Bool
                | Token::Int => break,
                _ => self.advance(),
            }
        }
        self.errors.borrow_mut().push(err);
    }
}

pub(super) struct ParseScope {
    prev_error_pos: usize,
    errors: Rc<RefCell<Vec<ParserError>>>,
    pub(super) context: ParserContext,
}

impl ParseScope {
    fn new(parser: &Parser, context: ParserContext) -> Self {
        Self {
            prev_error_pos: parser.errors.borrow().len(),
            errors: parser.errors.clone(),
            context,
        }
    }
}

impl Drop for ParseScope {
    fn drop(&mut self) {
        let mut errors = self.errors.borrow_mut();
        let new_errors = errors.split_off(self.prev_error_pos);
        errors.extend(
            new_errors
                .into_iter()
                .map(|e| e.with_context(self.context.clone())),
        );
    }
}
