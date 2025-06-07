use lalrpop_util::lalrpop_mod;

use crate::{
    cst::Program,
    lex::{Lexer, Token},
    parsing::grammar::ProgramParser,
};

lalrpop_mod!(
    #[allow(clippy::ptr_arg)]
    #[rustfmt::skip]
    pub grammar
);

pub fn parse(input: &[u8]) -> Option<Program> {
    let lexer = Lexer::new(input);
    let parser = ProgramParser::new();
    let result = parser.parse(input, lexer);
    match result {
        Ok(program) => Some(program),
        Err(err) => {
            eprintln!("Error: {err:?}");
            None
        }
    }
}
