use std::{path::Path, rc::Rc};

mod assembler;
mod inter;
mod opt;
mod parse;
mod scan;
mod utils;

use assembler::Assembler;
use inter::IrBuilder;
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
    if args.version {
        println!("1.0.0");
        return;
    }
    let _input =
        std::fs::read_to_string(&args.input.clone().unwrap()).expect("Filename is incorrect.");

    if args.debug {
        eprintln!(
            "Filename: {:?}\nDebug: {:?}\nOptimizations: {:?}\nOutput File: {:?}\nTarget: {:?}",
            args.input.clone().unwrap(),
            args.debug,
            args.opt,
            args.output,
            args.target
        );
    }

    // Use writeln!(writer, "template string") to write to stdout ot file.
    let writer = get_writer(&args.output);
    match args.target {
        utils::cli::CompilerAction::Scan => main_scan(args, writer),
        utils::cli::CompilerAction::Parse => main_parse(args, writer),
        utils::cli::CompilerAction::Inter => main_inter(args, writer),
        utils::cli::CompilerAction::Default | utils::cli::CompilerAction::Assembly => {
            main_assembler(args, writer)
        }
    }
}

fn main_scan(args: utils::cli::Args, mut writer: Box<dyn std::io::Write>) {
    let content =
        std::fs::read_to_string(&args.input.clone().unwrap()).expect("error reading file");
    let chars: Rc<[char]> = content.chars().collect::<Vec<_>>().into();
    let source = Rc::new(Source {
        filename: args.input.clone().unwrap().to_string_lossy().to_string(),
        content: chars.clone(),
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
    let (tokens, errors) = scan(args.input.clone().unwrap());
    dump_errors_and_exit(errors);
    let mut parser = Parser::new(tokens);
    let (_, errors) = parser.parse_program();
    dump_errors_and_exit(errors);
}

fn main_inter(args: utils::cli::Args, mut writer: Box<dyn std::io::Write>) {
    // TODO: Deduplicate this code with main_parse
    let (tokens, errors) = scan(args.input.clone().unwrap());
    dump_errors_and_exit(errors);
    let mut parser = Parser::new(tokens);
    let (ast, errors) = parser.parse_program();
    dump_errors_and_exit(errors);
    let mut checker = IrBuilder::new();
    let res = checker.check_program(&ast);
    match res {
        Ok(mut program) => {
            program = opt::optimize(program, &args.opt);
            writeln!(writer, "{}", program).unwrap();
        }
        Err(errors) => dump_errors_and_exit(errors),
    }
}

fn main_assembler(args: utils::cli::Args, mut writer: Box<dyn std::io::Write>) {
    // TODO: Deduplicate
    let (tokens, errors) = scan(args.input.clone().unwrap());
    dump_errors_and_exit(errors);
    let mut parser = Parser::new(tokens);
    let (ast, errors) = parser.parse_program();
    dump_errors_and_exit(errors);
    let mut checker = IrBuilder::new();
    let res = checker.check_program(&ast);
    let mut program = match res {
        Ok(program) => program,
        Err(errors) => {
            dump_errors_and_exit(errors);
            unreachable!()
        }
    };
    program = opt::optimize(program, &args.opt);
    let mut assembler = Assembler::new(program, &args.opt);
    let file_name = args
        .input
        .clone()
        .unwrap()
        .as_os_str()
        .to_string_lossy()
        .to_string();
    let res = assembler.assemble_lowered(&file_name);
    // let res = assembler.assemble(&file_name);
    writeln!(writer, "{}", res).unwrap();
}

fn dump_errors_and_exit<T>(errors: Vec<T>)
where
    for<'a> Diagnostic: From<&'a T>,
{
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
    let source = Rc::new(Source {
        filename,
        content: content.chars().collect(),
    });
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
