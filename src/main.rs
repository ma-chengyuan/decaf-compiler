use std::{path::Path, rc::Rc};

mod add;
mod utils;

mod parse;
mod scan;

use parse::parser::Parser;
use scan::{error::ScannerError, location::Spanned, scanner::Scanner, token::Token};
use utils::diagnostics::Diagnostic;

use crate::scan::location::Source;

fn get_writer(output: &Option<std::path::PathBuf>) -> Box<dyn std::io::Write> {
    match output {
        Some(path) => Box::new(std::fs::File::create(path.as_path()).unwrap()),
        None => Box::new(std::io::stdout()),
    }
}

fn main() {
    let args = utils::cli::parse();
    let _input = std::fs::read_to_string(&args.input).expect("Filename is incorrect.");

    if args.debug {
        eprintln!(
            "Filename: {:?}\nDebug: {:?}\nOptimizations: {:?}\nOutput File: {:?}\nTarget: {:?}",
            args.input, args.debug, args.opt, args.output, args.target
        );
    }

    // Use writeln!(writer, "template string") to write to stdout ot file.
    let _writer = get_writer(&args.output);
    match args.target {
        utils::cli::CompilerAction::Default => {
            panic!("Invalid target");
        }
        utils::cli::CompilerAction::Scan => main_scan(args, _writer),
        utils::cli::CompilerAction::Parse => main_parse(args, _writer),
        utils::cli::CompilerAction::Inter => {
            todo!("inter");
        }
        utils::cli::CompilerAction::Assembly => {
            todo!("assembly");
        }
    }
}

fn main_scan(args: utils::cli::Args, mut writer: Box<dyn std::io::Write>) {
    let content = std::fs::read_to_string(&args.input).expect("error reading file");
    let chars = content.chars().collect::<Vec<_>>();
    let source = Rc::new(Source {
        filename: args.input.to_string_lossy().to_string(),
        content,
    });
    let mut lexer = Scanner::new(source);
    let mut has_error = false;
    loop {
        match lexer.next() {
            Ok(Spanned {
                inner: Token::EndOfFile,
                ..
            }) => break,
            Ok(tok) => {
                let prefix = match &tok.inner {
                    scan::token::Token::Identifier(_) => "IDENTIFIER ",
                    scan::token::Token::IntLiteral(_) => "INTLITERAL ",
                    scan::token::Token::CharLiteral(_) => "CHARLITERAL ",
                    scan::token::Token::StringLiteral(_) => "STRINGLITERAL ",
                    scan::token::Token::BoolLiteral(_) => "BOOLEANLITERAL ",
                    _ => "",
                };
                let content = chars[tok.span.start().offset..tok.span.end().offset]
                    .iter()
                    .collect::<String>();
                writeln!(writer, "{} {}{}", tok.span.start().line, prefix, content).unwrap();
            }
            Err(e) => {
                has_error = true;
                let diag = Diagnostic::from(&e);
                diag.write(&mut std::io::stderr()).unwrap();
            }
        }
    }
    if has_error {
        std::process::exit(1);
    }
}

fn main_parse(args: utils::cli::Args, _writer: Box<dyn std::io::Write>) {
    let (tokens, errors) = scan(args.input);
    if !errors.is_empty() {
        for e in errors {
            eprintln!("{}", e);
        }
        std::process::exit(1);
    }
    let mut parser = Parser::new(tokens);
    let (_, errors) = parser.parse_program();
    if !errors.is_empty() {
        for e in errors {
            let diag = Diagnostic::from(&e);
            diag.write(&mut std::io::stderr()).unwrap();
        }
        std::process::exit(1);
    }
}

fn scan(path: impl AsRef<Path>) -> (Vec<Spanned<Token>>, Vec<ScannerError>) {
    let filename = path.as_ref().to_string_lossy().to_string();
    let content = std::fs::read_to_string(path).expect("error reading file");
    let source = Rc::new(Source { filename, content });
    let mut lexer = Scanner::new(source);
    let mut tokens = vec![];
    let mut errors = vec![];
    let mut eof = false;
    while !eof {
        match lexer.next() {
            Ok(tok) => {
                eof |= matches!(tok.inner, Token::EndOfFile);
                tokens.push(tok);
            }
            Err(e) => errors.push(e),
        }
    }
    (tokens, errors)
}
