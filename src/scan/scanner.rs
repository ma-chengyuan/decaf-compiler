#![allow(dead_code)]

use std::rc::Rc;

use num_bigint::BigInt;
use std::fmt;
use thiserror::Error;

use super::{
    location::{Location, Source, Span, Spanned},
    token::Token,
};

#[derive(Debug, Clone, Error)]
pub struct ScannerError {
    location: Location,
    context: ScannerErrorContext,
    expecting: ScannerExpecting,
    found: Option<char>,
}

impl fmt::Display for ScannerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let found = match self.found {
            Some(c) => format!("{:?}", c),
            None => "end of file".to_string(),
        };
        write!(
            f,
            "{}: expecting {}, found {} ({})",
            self.location, self.expecting, found, self.context
        )
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ScannerExpecting {
    Char(char),
    OneOf(&'static str),
    PrintableOrExcape,
    EscapeSequence,
}

impl fmt::Display for ScannerExpecting {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ScannerExpecting::Char(c) => write!(f, "{:?}", c),
            ScannerExpecting::OneOf(s) => write!(f, "one of \"{}\"", s),
            ScannerExpecting::PrintableOrExcape => write!(f, "printable character or '\\'"),
            ScannerExpecting::EscapeSequence => {
                write!(f, "escape sequence (one of n, t, \\, \", \')")
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScannerErrorContext {
    CharLiteral,
    StringLiteral,
    CharClosingQuote,
    StringClosingQuote,
    EscapeSequence,
    OperatorToken,
    SingleCharToken,
    ClosingBlockComment,
}

impl fmt::Display for ScannerErrorContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ScannerErrorContext::CharLiteral => write!(f, "invalid character in char literal"),
            ScannerErrorContext::StringLiteral => write!(f, "invalid charcter in string literal"),
            ScannerErrorContext::CharClosingQuote => {
                write!(f, "expecting closing quote of char literal")
            }
            ScannerErrorContext::StringClosingQuote => {
                write!(f, "expecting closing quote of string literal")
            }
            ScannerErrorContext::EscapeSequence => write!(f, "malformed escape sequence"),
            ScannerErrorContext::OperatorToken => write!(f, "invalid start of operator token"),
            ScannerErrorContext::SingleCharToken => write!(f, "invalid single character token"),
            ScannerErrorContext::ClosingBlockComment => {
                write!(f, "expecting closing */ of block comment")
            }
        }
    }
}

pub struct Scanner {
    cur_char: Option<char>,
    cur_loc: Location,
    all_chars: Vec<char>,
    source: Rc<Source>,
}

impl Scanner {
    pub fn new(source: Rc<Source>) -> Self {
        let mut lexer = Scanner {
            cur_char: None,
            cur_loc: Location {
                source: source.clone(),
                offset: 0,
                line: 1,
                column: 1,
            },
            all_chars: source.content.chars().collect(),
            source,
        };
        lexer.cur_char = lexer.all_chars.first().cloned();
        lexer
    }

    fn advance(&mut self) {
        if self.cur_char.is_some() {
            self.cur_char = self.all_chars.get(self.cur_loc.offset + 1).cloned();
            self.cur_loc.offset += 1;
            if let Some('\n') = self.cur_char {
                self.cur_loc.line += 1;
                self.cur_loc.column = 1;
            } else {
                self.cur_loc.column += 1;
            }
        }
    }

    fn next_keyword_bool_id(&mut self) -> Result<Spanned<Token>, ScannerError> {
        let start = self.cur_loc.clone();
        let mut identifier = String::new();
        identifier.push(self.cur_char.unwrap());
        self.advance();
        loop {
            match self.cur_char {
                Some(c) if c.is_alphanumeric() || c == '_' => {
                    identifier.push(c);
                    self.advance();
                }
                _ => break,
            }
        }
        let token = match identifier.as_str() {
            "bool" => Token::Bool,
            "break" => Token::Break,
            "const" => Token::Const,
            "import" => Token::Import,
            "continue" => Token::Continue,
            "else" => Token::Else,
            "false" => Token::BoolLiteral(false),
            "for" => Token::For,
            "while" => Token::While,
            "if" => Token::If,
            "int" => Token::Int,
            "return" => Token::Return,
            "len" => Token::Len,
            "true" => Token::BoolLiteral(true),
            "void" => Token::Void,
            _ => Token::Identifier(identifier),
        };
        Ok(Spanned {
            inner: token,
            span: Span {
                start,
                end: self.cur_loc.clone(),
            },
        })
    }

    fn next_int(&mut self) -> Result<Spanned<Token>, ScannerError> {
        let start = self.cur_loc.clone();
        let mut value = String::new();
        value.push(self.cur_char.unwrap());
        self.advance();
        let mut base = 10;
        if let Some('x') = self.cur_char {
            // Parse hex literal
            value.pop(); // Remove '0'
            self.advance(); // Skip 'x'
            base = 16;
        }
        loop {
            match self.cur_char {
                Some(c) if c.is_digit(base) => {
                    value.push(c);
                    self.advance();
                }
                _ => break,
            }
        }
        Ok(Spanned {
            inner: Token::IntLiteral(BigInt::parse_bytes(value.as_bytes(), base).unwrap()),
            span: Span {
                start,
                end: self.cur_loc.clone(),
            },
        })
    }

    fn next_char_internal(&mut self, context: ScannerErrorContext) -> Result<char, ScannerError> {
        match self.cur_char {
            Some('\\') => {
                self.advance();
                match self.cur_char {
                    Some(c @ ('n' | 't' | '\\' | '\'' | '"')) => {
                        self.advance();
                        match c {
                            'n' => Ok('\n'),
                            't' => Ok('\t'),
                            _ => Ok(c),
                        }
                    }
                    found => Err(ScannerError {
                        location: self.cur_loc.clone(),
                        context,
                        expecting: ScannerExpecting::EscapeSequence,
                        found,
                    }),
                }
            }
            // Printable ASCII character except for single quote and double quote
            Some(c) if (0x20..0x7F).contains(&(c as u32)) && c != '\'' && c != '"' => {
                self.advance();
                Ok(c)
            }
            found => Err(ScannerError {
                location: self.cur_loc.clone(),
                context,
                expecting: ScannerExpecting::PrintableOrExcape,
                found,
            }),
        }
    }

    fn next_char(&mut self) -> Result<Spanned<Token>, ScannerError> {
        let start = self.cur_loc.clone();
        self.advance(); // Skip opening quote
        let c = self.next_char_internal(ScannerErrorContext::CharLiteral)?;
        match self.cur_char {
            Some('\'') => {
                self.advance();
                Ok(Spanned {
                    inner: Token::CharLiteral(c),
                    span: Span {
                        start,
                        end: self.cur_loc.clone(),
                    },
                })
            }
            found => Err(ScannerError {
                location: self.cur_loc.clone(),
                context: ScannerErrorContext::CharClosingQuote,
                expecting: ScannerExpecting::Char('\''),
                found,
            }),
        }
    }

    fn next_string(&mut self) -> Result<Spanned<Token>, ScannerError> {
        let start = self.cur_loc.clone();
        self.advance(); // Skip opening quote
        let mut value = String::new();
        loop {
            match self.cur_char {
                None => {
                    return Err(ScannerError {
                        location: self.cur_loc.clone(),
                        context: ScannerErrorContext::StringLiteral,
                        expecting: ScannerExpecting::Char('"'),
                        found: None,
                    })
                }
                Some('\"') => {
                    self.advance();
                    break;
                }
                Some(_) => value.push(self.next_char_internal(ScannerErrorContext::StringLiteral)?),
            }
        }
        Ok(Spanned {
            inner: Token::StringLiteral(value),
            span: Span {
                start,
                end: self.cur_loc.clone(),
            },
        })
    }

    pub fn next_single_char(&mut self, c: char) -> Result<Spanned<Token>, ScannerError> {
        let start = self.cur_loc.clone();
        let token = match c {
            '(' => Token::OpenParen,
            ')' => Token::CloseParen,
            '[' => Token::OpenBracket,
            ']' => Token::CloseBracket,
            '{' => Token::OpenBrace,
            '}' => Token::CloseBrace,
            ';' => Token::Semicolon,
            ',' => Token::Comma,
            _ => {
                return Err(ScannerError {
                    location: self.cur_loc.clone(),
                    context: ScannerErrorContext::SingleCharToken,
                    expecting: ScannerExpecting::OneOf("()[]{};,"),
                    found: Some(c),
                })
            }
        };
        self.advance();
        Ok(Spanned {
            inner: token,
            span: Span {
                start,
                end: self.cur_loc.clone(),
            },
        })
    }

    pub fn next_div_or_comment(&mut self) -> Result<Spanned<Token>, ScannerError> {
        let start = self.cur_loc.clone();
        self.advance();
        match self.cur_char {
            Some('/') => {
                // Line comment
                loop {
                    match self.cur_char {
                        Some(c) if c != '\n' => self.advance(),
                        _ => break,
                    }
                }
                self.next()
            }
            Some('*') => {
                // Block comment
                self.advance();
                loop {
                    match self.cur_char {
                        None => {
                            return Err(ScannerError {
                                location: self.cur_loc.clone(),
                                context: ScannerErrorContext::ClosingBlockComment,
                                expecting: ScannerExpecting::Char('*'),
                                found: None,
                            })
                        }
                        Some('*') => {
                            self.advance();
                            if let Some('/') = self.cur_char {
                                self.advance();
                                break;
                            }
                        }
                        Some(_) => self.advance(),
                    }
                }
                self.next()
            }
            Some('=') => {
                self.advance();
                Ok(Spanned {
                    inner: Token::DivAssign,
                    span: Span {
                        start,
                        end: self.cur_loc.clone(),
                    },
                })
            }
            _ => Ok(Spanned {
                inner: Token::Div,
                span: Span {
                    start,
                    end: self.cur_loc.clone(),
                },
            }),
        }
    }

    pub fn next_op(&mut self, c: char) -> Result<Spanned<Token>, ScannerError> {
        let start = self.cur_loc.clone();
        self.advance();
        let token = match (c, self.cur_char) {
            ('+', Some('=')) => {
                self.advance();
                Token::AddAssign
            }
            ('+', Some('+')) => {
                self.advance();
                Token::Increment
            }
            ('+', _) => Token::Add,
            ('-', Some('=')) => {
                self.advance();
                Token::SubAssign
            }
            ('-', Some('-')) => {
                self.advance();
                Token::Decrement
            }
            ('-', _) => Token::Sub,
            ('*', Some('=')) => {
                self.advance();
                Token::MulAssign
            }
            ('*', _) => Token::Mul,
            ('%', Some('=')) => {
                self.advance();
                Token::ModAssign
            }
            ('%', _) => Token::Mod,
            ('!', Some('=')) => {
                self.advance();
                Token::Unequal
            }
            ('!', _) => Token::Not,
            ('=', Some('=')) => {
                self.advance();
                Token::Equal
            }
            ('=', _) => Token::Assign,
            ('&', Some('&')) => {
                self.advance();
                Token::And
            }
            ('&', found) => {
                return Err(ScannerError {
                    location: self.cur_loc.clone(),
                    context: ScannerErrorContext::OperatorToken,
                    expecting: ScannerExpecting::Char('&'),
                    found,
                })
            }
            ('|', Some('|')) => {
                self.advance();
                Token::Or
            }
            ('|', found) => {
                return Err(ScannerError {
                    location: self.cur_loc.clone(),
                    context: ScannerErrorContext::OperatorToken,
                    expecting: ScannerExpecting::Char('|'),
                    found,
                })
            }
            ('<', Some('=')) => {
                self.advance();
                Token::LessThanOrEqual
            }
            ('<', _) => Token::LessThan,
            ('>', Some('=')) => {
                self.advance();
                Token::GreaterThanOrEqual
            }
            ('>', _) => Token::GreaterThan,
            _ => {
                return Err(ScannerError {
                    location: self.cur_loc.clone(),
                    context: ScannerErrorContext::OperatorToken,
                    expecting: ScannerExpecting::OneOf("+-*/%!&|<>=,"),
                    found: Some(c),
                })
            }
        };
        Ok(Spanned {
            inner: token,
            span: Span {
                start,
                end: self.cur_loc.clone(),
            },
        })
    }

    fn next_whitespace(&mut self) -> Result<Spanned<Token>, ScannerError> {
        while matches!(self.cur_char, Some(c) if c.is_whitespace()) {
            self.advance();
        }
        self.next()
    }

    pub fn next(&mut self) -> Result<Spanned<Token>, ScannerError> {
        // Tokenize the next token
        let result = match self.cur_char {
            None => Ok(Spanned {
                inner: Token::EndOfFile,
                span: Span {
                    start: self.cur_loc.clone(),
                    end: self.cur_loc.clone(),
                },
            }),
            Some(c) => match c {
                c if c.is_whitespace() => self.next_whitespace(),
                c if c.is_alphabetic() || c == '_' => self.next_keyword_bool_id(),
                c if c.is_ascii_digit() => self.next_int(),
                '\'' => self.next_char(),
                '\"' => self.next_string(),
                '/' => self.next_div_or_comment(),
                c @ ('+' | '-' | '*' | '%' | '!' | '=' | '&' | '|' | '<' | '>') => self.next_op(c),
                _ => self.next_single_char(c),
            },
        };
        // Error recovery
        match result {
            Ok(tok) => Ok(tok),
            Err(e) => {
                self.advance();
                Err(e)
            }
        }
    }
}