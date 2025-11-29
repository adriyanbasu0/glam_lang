use miette::{Diagnostic, IntoDiagnostic, Result};
use thiserror::Error;

#[derive(Error, Diagnostic, Debug)]
pub enum OxError {
    #[error(transparent)]
    #[diagnostic(code(ox_lang::io_error))]
    IoError(#[from] io::Error),

    #[error("Parser error: {0}")]
    #[diagnostic(code(ox_lang::parser_error))]
    ParserError(String),

    #[error("Parser error: {message}")]
    #[diagnostic(code(ox_lang::parser_error_with_span))]
    ParserErrorWithSpan {
        message: String,
        #[label("Here")]
        span: miette::SourceSpan,
    },
    #[error(transparent)]
    #[diagnostic(code(ox_lang::eval_error))]
    EvalError(#[from] evaluator::EvalError),
    #[error(transparent)]
    #[diagnostic(code(ox_lang::lexer_error))]
    LexerError(#[from] lexer::LexerError),
}

mod ast;
mod evaluator;
mod lexer;
mod parser;
mod token;

use crate::evaluator::{Environment, eval};
// use crate::lexer::Lexer;
use crate::parser::Parser;
use std::cell::RefCell;
use std::fs;
use std::io::{self, Read};
use std::rc::Rc;

fn main() -> Result<()> {
    println!("Ox Lang Interpreter initialised.");

    let file_path = "main.lm";
    let mut file = fs::File::open(file_path).into_diagnostic()?;
    let mut input = String::new();
    file.read_to_string(&mut input).into_diagnostic()?;

    // Create a NamedSource for miette to use
    let source = miette::NamedSource::new(file_path.to_string(), input.clone());

    let p = Parser::new();
    let program = match p.parse(&input) {
        Ok(program) => program,
        Err(e) => {
            // The error from the parser is a String. We need to convert it to a miette::Report.
            // For now, let's just print the error and exit.
            eprintln!("Parser error: {}", e);
            // We can't easily get a span from the LALRPOP error without more work.
            // We will just create a generic error for now.
            return Err(miette::Report::new(OxError::ParserError(e)).with_source_code(source));
        }
    };

    let mut env = Rc::new(RefCell::new(Environment::new(Rc::new(RefCell::new(
        io::stdout(),
    )))));
    let evaluated = eval(program, &mut env)?;

    println!("Evaluated result: {}", evaluated);
    Ok(())
}
