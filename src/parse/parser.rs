#![allow(dead_code)]

use std::{cell::RefCell, rc::Rc};

use colored::Color;

use crate::{
    parse::ast::{BinOp, MethodCallArg, MethodParam},
    scan::{
        location::{Span, Spanned},
        token::Token,
    },
    utils::diagnostics::DiagnosticItem,
};

use super::{
    ast::{
        Block, BoolLiteral, CharLiteral, Expr, FieldDecl, FieldDeclaration, FieldDeclarator, Ident,
        ImportDecl, Initializer, IntLiteral, Location, MethodCall, MethodDecl, Program,
        RuntimeLiteral, Stmt, Type, UnaryOp, UpdateOp,
    },
    error::{ParserError, ParserErrorKind},
};

#[derive(Debug, Clone)]
pub enum ParserContext {
    MethodDecl(Ident),
    FieldDecl(Ident),
    MethodCall(Ident),
}

impl From<&ParserContext> for DiagnosticItem {
    fn from(value: &ParserContext) -> Self {
        let color = Some(Color::Green);
        match value {
            ParserContext::MethodDecl(ident) => DiagnosticItem {
                span: ident.span.clone(),
                message: format!("in method '{}'", ident.inner),
                color,
            },
            ParserContext::FieldDecl(ident) => DiagnosticItem {
                span: ident.span.clone(),
                message: format!("in field '{}'", ident.inner),
                color,
            },
            ParserContext::MethodCall(ident) => DiagnosticItem {
                span: ident.span.clone(),
                message: format!("in call to '{}'", ident.inner),
                color,
            },
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
    /// A list of parser contexts, from the outermost to the innermost.
    contexts: Rc<RefCell<Vec<ParserContext>>>,
}

macro_rules! unexpected {
    ($self:ident, $($p:expr),+) => {
        return Err($self.make_error(ParserErrorKind::UnexpectedToken {
            expecting: vec![$($p),+],
            found: $self.current().clone(),
        }))
    };
}

/// Expects and consumes the current token if it is of the given type.
macro_rules! parse_token {
    ($self:ident, $t:path) => {
        match &$self.current().inner {
            $t => {
                $self.advance();
            }
            _ => unexpected!($self, $t),
        }
    };
}

/// Parses a list of items delimited by a given delimiter and closed by a given
/// closing token. No trailing delimiter is allowed. The closing token will be
/// consumed.
macro_rules! parse_delimited {
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
}

macro_rules! parse_spanned {
    ($self:ident . $method:ident ( $($args:tt)* )) => {
        {
            let start = $self.current().span.start().clone();
            let inner = $self.$method($($args)*)?;
            let end = $self.tokens[$self.pos - 1].span.end().clone();
            Spanned {
                inner,
                span: Span::new(start, end),
            }
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
                span: Span::new(tok.span.end().clone(), tok.span.end().clone()),
            }),
            None => panic!("empty token stream"),
        }
        Self {
            tokens,
            pos: 0,
            errors: vec![],
            contexts: Default::default(),
        }
    }

    fn make_error(&self, kind: ParserErrorKind) -> ParserError {
        ParserError {
            kind: Box::new(kind),
            contexts: self.contexts.borrow().clone(),
        }
    }

    fn advance(&mut self) {
        self.pos = (self.pos + 1).min(self.tokens.len() - 1);
    }

    fn lookahead(&self, by: usize) -> &Spanned<Token> {
        &self.tokens[(self.pos + by).min(self.tokens.len() - 1)]
    }

    fn current(&self) -> &Spanned<Token> {
        self.lookahead(0)
    }

    fn parse_ident(&mut self) -> Result<Ident, ParserError> {
        match &self.current().inner {
            Token::Identifier(ident) => {
                let ident = Ident {
                    inner: ident.clone(),
                    span: self.current().span.clone(),
                };
                self.advance();
                Ok(ident)
            }
            _ => unexpected!(self, Token::Identifier("".into())),
        }
    }

    fn parse_location(&mut self) -> Result<Location, ParserError> {
        let ident = self.parse_ident()?;
        match &self.current().inner {
            Token::OpenBracket => {
                self.advance();
                let expr = self.parse_expr()?;
                parse_token!(self, Token::CloseBracket);
                Ok(Location::ArrayAccess {
                    ident: Box::new(Location::Ident(ident)),
                    index: Box::new(expr),
                })
            }
            _ => Ok(Location::Ident(ident)),
        }
    }

    fn parse_call(&mut self) -> Result<MethodCall, ParserError> {
        let name = self.parse_ident()?;
        let _scope = ParseScope::new(self, ParserContext::MethodCall(name.clone()));
        let mut args = Vec::new();
        parse_token!(self, Token::OpenParen);
        parse_delimited! {
            self, Token::Comma, Token::CloseParen,
            Token::StringLiteral(value) => {
                args.push(MethodCallArg::StringLiteral(Spanned {
                    inner: value.clone(),
                    span: self.current().span.clone(),
                }));
                self.advance();
            },
            _ => args.push(MethodCallArg::Expr(self.parse_expr()?))
        }
        Ok(MethodCall { name, args })
    }

    fn parse_literal(&mut self) -> Result<RuntimeLiteral, ParserError> {
        match &self.current().inner {
            Token::IntLiteral(value) => {
                let lit = IntLiteral {
                    inner: value.clone(),
                    span: self.current().span.clone(),
                };
                self.advance();
                Ok(RuntimeLiteral::Int(lit))
            }
            Token::Sub => {
                let start = self.current().span.start().clone();
                self.advance();
                match &self.current().inner {
                    Token::IntLiteral(value) => {
                        let span = self.current().span.clone();
                        let span = Span::new(start, span.end().clone());
                        let lit = IntLiteral {
                            inner: -value,
                            span,
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

    fn parse_expr(&mut self) -> Result<Spanned<Expr>, ParserError> {
        let lhs = parse_spanned!(self.parse_expr_atom());
        self.parse_expr_op_prec(lhs, 0)
    }

    fn parse_expr_op_prec(
        &mut self,
        mut lhs: Spanned<Expr>,
        min_precedence: i32,
    ) -> Result<Spanned<Expr>, ParserError> {
        // Our beloved operator-precedence parsing algorithm.
        // See https://en.wikipedia.org/wiki/Operator-precedence_parser
        loop {
            let (op, cur_prec) = token_to_op_and_prec(&self.current().inner);
            if cur_prec < min_precedence {
                break;
            }
            self.advance();
            let mut rhs = parse_spanned!(self.parse_expr_atom());
            loop {
                let (_, new_prec) = token_to_op_and_prec(&self.current().inner);
                if new_prec <= cur_prec {
                    break;
                } else {
                    rhs = self.parse_expr_op_prec(rhs, cur_prec + 1)?;
                }
            }
            let span = lhs.span.merge(&rhs.span);
            lhs = Spanned {
                inner: Expr::BinOp {
                    lhs: Box::new(lhs),
                    op,
                    rhs: Box::new(rhs),
                },
                span,
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

    fn parse_expr_atom(&mut self) -> Result<Expr, ParserError> {
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
                parse_token!(self, Token::OpenParen);
                let ident = self.parse_ident()?;
                parse_token!(self, Token::CloseParen);
                Ok(Expr::Len(ident))
            }
            Token::OpenParen => {
                self.advance();
                let expr = self.parse_expr()?;
                parse_token!(self, Token::CloseParen);
                Ok(expr.inner)
            }
            Token::Sub | Token::Not => {
                let op = match self.current().inner {
                    Token::Sub => UnaryOp::Neg,
                    Token::Not => UnaryOp::Not,
                    _ => unreachable!(),
                };
                self.advance();
                let expr = parse_spanned!(self.parse_expr_atom());
                if let Expr::Literal(RuntimeLiteral::Int(lit)) = expr.inner {
                    Ok(Expr::Literal(RuntimeLiteral::Int(Spanned {
                        inner: -lit.inner,
                        span: expr.span,
                    })))
                } else {
                    Ok(Expr::UnaryOp {
                        op,
                        expr: Box::new(expr),
                    })
                }
            }
            _ => unexpected!(
                self,
                Token::Identifier("".into()),
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

    fn parse_update_stmt(&mut self) -> Result<Stmt, ParserError> {
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

    fn parse_stmt(&mut self) -> Result<Stmt, ParserError> {
        match &self.current().inner {
            Token::Identifier(_) => {
                let ret = self.parse_for_update()?;
                parse_token!(self, Token::Semicolon);
                Ok(ret)
            }
            Token::If => self.parse_if_stmt(),
            Token::While => self.parse_while_stmt(),
            Token::Return => self.parse_return_stmt(),
            Token::For => self.parse_for_stmt(),
            Token::Break => {
                let span = self.current().span.clone();
                self.advance();
                parse_token!(self, Token::Semicolon);
                Ok(Stmt::Break(span))
            }
            Token::Continue => {
                let span = self.current().span.clone();
                self.advance();
                parse_token!(self, Token::Semicolon);
                Ok(Stmt::Continue(span))
            }
            _ => unexpected!(
                self,
                Token::Identifier("".into()),
                Token::If,
                Token::While,
                Token::Return,
                Token::For,
                Token::Break,
                Token::Continue
            ),
        }
    }

    fn parse_for_update(&mut self) -> Result<Stmt, ParserError> {
        if self.lookahead(1).inner == Token::OpenParen {
            Ok(Stmt::Call(self.parse_call()?))
        } else {
            self.parse_update_stmt()
        }
    }

    fn parse_if_stmt(&mut self) -> Result<Stmt, ParserError> {
        parse_token!(self, Token::If);
        parse_token!(self, Token::OpenParen);
        let condition = self.parse_expr()?;
        parse_token!(self, Token::CloseParen);
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

    fn parse_while_stmt(&mut self) -> Result<Stmt, ParserError> {
        parse_token!(self, Token::While);
        parse_token!(self, Token::OpenParen);
        let condition = self.parse_expr()?;
        parse_token!(self, Token::CloseParen);
        let block = self.parse_block()?;
        Ok(Stmt::While { condition, block })
    }

    fn parse_for_stmt(&mut self) -> Result<Stmt, ParserError> {
        parse_token!(self, Token::For);
        parse_token!(self, Token::OpenParen);
        let loop_var_name = self.parse_ident()?;
        parse_token!(self, Token::Assign);
        let init = self.parse_expr()?;
        parse_token!(self, Token::Semicolon);
        let cond = self.parse_expr()?;
        parse_token!(self, Token::Semicolon);
        let update = self.parse_for_update()?;
        parse_token!(self, Token::CloseParen);
        let block = self.parse_block()?;
        Ok(Stmt::For {
            loop_var_name,
            init,
            cond,
            update: Box::new(update),
            block,
        })
    }

    fn parse_return_stmt(&mut self) -> Result<Stmt, ParserError> {
        let span = self.current().span.clone();
        parse_token!(self, Token::Return);
        let expr = match &self.current().inner {
            Token::Semicolon => None,
            _ => Some(self.parse_expr()?),
        };
        parse_token!(self, Token::Semicolon);
        Ok(Stmt::Return { span, expr })
    }

    fn parse_block(&mut self) -> Result<Block, ParserError> {
        parse_token!(self, Token::OpenBrace);
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

    fn parse_type(&mut self) -> Result<Type, ParserError> {
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

    fn parse_field_declarator(&mut self) -> Result<FieldDeclarator, ParserError> {
        let declarator = FieldDeclarator::Ident(self.parse_ident()?);
        match self.current().inner {
            Token::OpenBracket => {
                self.advance();
                let _scope =
                    ParseScope::new(self, ParserContext::FieldDecl(declarator.ident().clone()));
                let size = match &self.current().inner {
                    Token::IntLiteral(value) => {
                        let spanned = Spanned {
                            inner: value.clone(),
                            span: self.current().span.clone(),
                        };

                        self.advance();
                        Some(spanned)
                    }
                    Token::CloseBracket => None,
                    _ => unexpected!(
                        self,
                        Token::IntLiteral(Default::default()),
                        Token::CloseBracket
                    ),
                };
                parse_token!(self, Token::CloseBracket);
                Ok(FieldDeclarator::Array {
                    base: Box::new(declarator),
                    size,
                })
            }
            _ => Ok(declarator),
        }
    }

    fn parse_array_initializer(&mut self) -> Result<Vec<Initializer>, ParserError> {
        let token = self.current().clone();
        self.advance();
        let mut initializers = Vec::new();
        parse_delimited! {
            self, Token::Comma, Token::CloseBrace,
            // TODO: support nested initializers
            _ => initializers.push(Initializer::Literal(self.parse_literal()?))
        };
        if initializers.is_empty() {
            return Err(self.make_error(ParserErrorKind::EmptyInitializer(token)));
        }
        Ok(initializers)
    }

    fn parse_initializer(&mut self) -> Result<Initializer, ParserError> {
        match &self.current().inner {
            Token::OpenBrace => Ok(Initializer::Array(parse_spanned!(
                self.parse_array_initializer()
            ))),
            _ => Ok(Initializer::Literal(self.parse_literal()?)),
        }
    }

    fn parse_field_decl(&mut self) -> Result<FieldDecl, ParserError> {
        let is_const = match self.current().inner {
            Token::Const => {
                self.advance();
                true
            }
            _ => false,
        };
        let ty = self.parse_type()?;
        let mut decls = vec![];
        parse_delimited! {
            self, Token::Comma, Token::Semicolon,
            _ => {
                let declarator = self.parse_field_declarator()?;
                let _scope =
                    ParseScope::new(self, ParserContext::FieldDecl(declarator.ident().clone()));
                let initializer = match self.current().inner {
                    Token::Assign => {
                        self.advance();
                        Some(self.parse_initializer()?)
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
            return Err(self.make_error(ParserErrorKind::EmptyFieldDecl(self.current().clone())));
        }
        Ok(FieldDecl {
            is_const,
            ty,
            decls,
        })
    }

    // Parsing method declaration

    fn parse_method_decl(&mut self) -> Result<MethodDecl, ParserError> {
        let return_ty = match &self.current().inner {
            Token::Void => {
                self.advance();
                None
            }
            _ => Some(self.parse_type()?),
        };
        let name = self.parse_ident()?;
        let _scope = ParseScope::new(self, ParserContext::MethodDecl(name.clone()));
        parse_token!(self, Token::OpenParen);
        let mut params = vec![];
        parse_delimited! {
            self, Token::Comma, Token::CloseParen,
            _ => {
                let ty = self.parse_type()?;
                let name = self.parse_ident()?;
                params.push(MethodParam { ty, name });
            }
        }
        let body = self.parse_block()?;
        Ok(MethodDecl {
            name,
            return_ty,
            params,
            body,
        })
    }

    // Parsing import decl

    fn parse_import_decl(&mut self) -> Result<ImportDecl, ParserError> {
        parse_token!(self, Token::Import);
        let ident = self.parse_ident()?;
        parse_token!(self, Token::Semicolon);
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
                    self.panic_recovery(self.make_error(ParserErrorKind::UnexpectedToken {
                        expecting: expected,
                        found: self.current().clone(),
                    }));
                    self.advance();
                }
            }
        }
        let all_errors = self.errors.clone();
        self.errors.clear();
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

    fn panic_recovery(&mut self, err: ParserError) {
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
        self.errors.push(err);
    }
}

struct ParseScope {
    contexts: Rc<RefCell<Vec<ParserContext>>>,
}

impl ParseScope {
    fn new(parser: &Parser, context: ParserContext) -> Self {
        {
            let mut contexts = parser.contexts.borrow_mut();
            contexts.push(context);
        }
        Self {
            contexts: parser.contexts.clone(),
        }
    }
}

impl Drop for ParseScope {
    fn drop(&mut self) {
        let mut contexts = self.contexts.borrow_mut();
        contexts.pop();
    }
}
