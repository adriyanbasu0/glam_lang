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
use crate::lexer::Lexer;
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

    let l = Lexer::new(input); // Pass input to lexer
    let mut p = Parser::new(l);
    let program = p.parse_program();

    if !p.errors.is_empty() {
        let error = p.errors.remove(0); // Get the OxError directly
        return Err(miette::Report::new(error).with_source_code(source).into());
    }

    let mut env = Rc::new(RefCell::new(Environment::new(Rc::new(RefCell::new(
        io::stdout(),
    )))));
    let evaluated = eval(program, &mut env)?;

    println!("Evaluated result: {}", evaluated);
    Ok(())
}
