#![allow(dead_code)]

use std::rc::Rc;

use num_bigint::BigInt;
use std::fmt;
use thiserror::Error;

use super::{
    location::{Location, Source, Span},
    token::{Token, TokenWithSpan},
};

#[derive(Debug, Clone, Error)]
pub enum LexerError {
    #[error("unexpected character '{0}' at {1} (in {2})")]
    UnexpectedChar(char, Location, LexerErrorContext),
    #[error("unexpected end of file in {0} while (in {1})")]
    UnexpectedEndOfFile(Rc<Source>, LexerErrorContext),
    #[error("end of file")]
    EndOfFile,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LexerErrorContext {
    ClosingQuote,
    CharStringLiteral,
    EscapeSequence,
    Token,
    SingleCharToken,
    ClosingBlockComment,
}

impl fmt::Display for LexerErrorContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LexerErrorContext::ClosingQuote => write!(f, "closing quote of char/string literal"),
            LexerErrorContext::CharStringLiteral => write!(f, "char/string literal"),
            LexerErrorContext::EscapeSequence => write!(f, "escape sequence"),
            LexerErrorContext::Token => write!(f, "new token"),
            LexerErrorContext::SingleCharToken => write!(f, "single character token"),
            LexerErrorContext::ClosingBlockComment => write!(f, "closing */ of block comment"),
        }
    }
}

pub struct Lexer {
    cur_char: Option<char>,
    cur_loc: Location,
    all_chars: Vec<char>,
    source: Rc<Source>,
}

impl Lexer {
    pub fn new(source: Rc<Source>) -> Self {
        let mut lexer = Lexer {
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
        self.cur_char = self.all_chars.get(self.cur_loc.offset + 1).cloned();
        self.cur_loc.offset += 1;
        if let Some('\n') = self.cur_char {
            self.cur_loc.line += 1;
            self.cur_loc.column = 1;
        } else {
            self.cur_loc.column += 1;
        }
    }

    fn next_keyword_bool_id(&mut self) -> Result<TokenWithSpan, LexerError> {
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
        Ok(TokenWithSpan {
            token,
            span: Span {
                start,
                end: self.cur_loc.clone(),
            },
        })
    }

    fn next_int(&mut self) -> Result<TokenWithSpan, LexerError> {
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
        Ok(TokenWithSpan {
            token: Token::IntLiteral(BigInt::parse_bytes(value.as_bytes(), base).unwrap()),
            span: Span {
                start,
                end: self.cur_loc.clone(),
            },
        })
    }

    fn next_char_internal(&mut self) -> Result<char, LexerError> {
        match self.cur_char {
            None => Err(LexerError::UnexpectedEndOfFile(
                self.source.clone(),
                LexerErrorContext::CharStringLiteral,
            )),
            Some('\\') => {
                self.advance();
                match self.cur_char {
                    None => Err(LexerError::UnexpectedEndOfFile(
                        self.source.clone(),
                        LexerErrorContext::EscapeSequence,
                    )),
                    // TODO: double quote
                    Some(c @ ('n' | 't' | '\\' | '\'' | '"')) => {
                        self.advance();
                        match c {
                            'n' => Ok('\n'),
                            't' => Ok('\t'),
                            _ => Ok(c),
                        }
                    }
                    Some(_) => Err(LexerError::UnexpectedChar(
                        self.cur_char.unwrap(),
                        self.cur_loc.clone(),
                        LexerErrorContext::EscapeSequence,
                    )),
                }
            }
            // Printable ASCII character except for single quote and double quote
            Some(c) if (0x20..0x7F).contains(&(c as u32)) && c != '\'' && c != '"' => {
                self.advance();
                Ok(c)
            }
            _ => Err(LexerError::UnexpectedChar(
                self.cur_char.unwrap(),
                self.cur_loc.clone(),
                LexerErrorContext::CharStringLiteral,
            )),
        }
    }

    fn next_char(&mut self) -> Result<TokenWithSpan, LexerError> {
        let start = self.cur_loc.clone();
        self.advance(); // Skip opening quote
        let c = self.next_char_internal()?;
        match self.cur_char {
            Some('\'') => {
                self.advance();
                Ok(TokenWithSpan {
                    token: Token::CharLiteral(c),
                    span: Span {
                        start,
                        end: self.cur_loc.clone(),
                    },
                })
            }
            _ => Err(LexerError::UnexpectedChar(
                self.cur_char.unwrap(),
                self.cur_loc.clone(),
                LexerErrorContext::ClosingQuote,
            )),
        }
    }

    fn next_string(&mut self) -> Result<TokenWithSpan, LexerError> {
        let start = self.cur_loc.clone();
        self.advance(); // Skip opening quote
        let mut value = String::new();
        loop {
            match self.cur_char {
                None => {
                    return Err(LexerError::UnexpectedEndOfFile(
                        self.source.clone(),
                        LexerErrorContext::ClosingQuote,
                    ))
                }
                Some('\"') => {
                    self.advance();
                    break;
                }
                Some(_) => value.push(self.next_char_internal()?),
            }
        }
        Ok(TokenWithSpan {
            token: Token::StringLiteral(value),
            span: Span {
                start,
                end: self.cur_loc.clone(),
            },
        })
    }

    pub fn next_single_char(&mut self, c: char) -> Result<TokenWithSpan, LexerError> {
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
                return Err(LexerError::UnexpectedChar(
                    c,
                    self.cur_loc.clone(),
                    LexerErrorContext::SingleCharToken,
                ))
            }
        };
        self.advance();
        Ok(TokenWithSpan {
            token,
            span: Span {
                start,
                end: self.cur_loc.clone(),
            },
        })
    }

    pub fn next_div_or_comment(&mut self) -> Result<TokenWithSpan, LexerError> {
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
                            return Err(LexerError::UnexpectedEndOfFile(
                                self.source.clone(),
                                LexerErrorContext::ClosingBlockComment,
                            ))
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
                Ok(TokenWithSpan {
                    token: Token::DivAssign,
                    span: Span {
                        start,
                        end: self.cur_loc.clone(),
                    },
                })
            }
            _ => Ok(TokenWithSpan {
                token: Token::Div,
                span: Span {
                    start,
                    end: self.cur_loc.clone(),
                },
            }),
        }
    }

    pub fn next_op(&mut self, c: char) -> Result<TokenWithSpan, LexerError> {
        let start = self.cur_loc.clone();
        self.advance();
        let tok = match (c, self.cur_char) {
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
            ('|', Some('|')) => {
                self.advance();
                Token::Or
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
                return Err(LexerError::UnexpectedChar(
                    c,
                    start.clone(),
                    LexerErrorContext::Token,
                ))
            }
        };
        Ok(TokenWithSpan {
            token: tok,
            span: Span {
                start,
                end: self.cur_loc.clone(),
            },
        })
    }

    fn next_whitespace(&mut self) -> Result<TokenWithSpan, LexerError> {
        while matches!(self.cur_char, Some(c) if c.is_whitespace()) {
            self.advance();
        }
        self.next()
    }

    pub fn next(&mut self) -> Result<TokenWithSpan, LexerError> {
        // Tokenize the next token
        let result = match self.cur_char {
            None => Err(LexerError::EndOfFile),
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
            // Can't recover from end of file
            Err(e @ (LexerError::EndOfFile | LexerError::UnexpectedEndOfFile(_, _))) => Err(e),
            // Skip the offending character and try again
            Err(e @ LexerError::UnexpectedChar(_, _, _)) => {
                self.advance();
                Err(e)
            }
        }
    }
}
