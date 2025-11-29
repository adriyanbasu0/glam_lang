use lalrpop_util::lalrpop_mod;
use crate::ast::Program;
use crate::lexer::Lexer;
use crate::token::Token;

// The lalrpop macro generates a module named `ox`.
lalrpop_mod!(pub glam);

pub struct Parser {
    parser: glam::ProgramParser,
}

impl Parser {
    pub fn new() -> Self {
        Parser {
            parser: glam::ProgramParser::new(),
        }
    }

    pub fn parse(&self, source: &str) -> Result<Program, String> {
        let lexer = Lexer::new(source.to_string());
        let tokens = lexer.map(|token_result| {
            token_result.map(|token| {
                let start = token.start;
                let end = start + token.len;
                (start, token, end)
            })
        });
        // The lalrpop parser expects an iterator of `Result<(usize, Token, usize), Error>`.
        // The lexer now returns `Result<Token, OxError>`. We need to adapt this.
        // The error type also needs to be compatible. The grammar expects `String`.
        let mapped_tokens = tokens.map(|res| res.map_err(|err| format!("{:?}", err)));
        self.parser.parse(mapped_tokens).map_err(|e| format!("{:?}", e))
    }
}