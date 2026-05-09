use lalrpop_util::lalrpop_mod;
use lalrpop_util::ParseError as LalrpopParseError;

use crate::{lex::Lexer, parsing::grammar::ProgramParser, syntax::Program, lex::Token};

lalrpop_mod!(
    #[allow(clippy::ptr_arg)]
    #[rustfmt::skip]
    pub grammar
);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseResult {
    pub program: Option<Program>,
    pub errors: Vec<ParseErrorInfo>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseErrorInfo {
    pub offset: usize,
    pub message: String,
}

impl ParseErrorInfo {
    fn from_lalrpop_error(err: &LalrpopParseError<usize, Token, &str>, _input: &[u8]) -> Self {
        match err {
            LalrpopParseError::InvalidToken { location } => {
                ParseErrorInfo {
                    offset: *location,
                    message: "Invalid token".to_string(),
                }
            }
            LalrpopParseError::UnrecognizedEof { location, expected } => {
                let msg = if expected.is_empty() {
                    "Unexpected end of file".to_string()
                } else {
                    format!("Unexpected end of file, expected one of: {}", expected.join(", "))
                };
                ParseErrorInfo {
                    offset: *location,
                    message: msg,
                }
            }
            LalrpopParseError::UnrecognizedToken { token: (start, token, _end), expected } => {
                let token_str = format!("{:?}", token);
                let msg = if expected.is_empty() {
                    format!("Unexpected token: {}", token_str)
                } else {
                    format!("Unexpected token: {}, expected one of: {}", token_str, expected.join(", "))
                };
                ParseErrorInfo {
                    offset: *start,
                    message: msg,
                }
            }
            LalrpopParseError::ExtraToken { token: (start, token, _end) } => {
                ParseErrorInfo {
                    offset: *start,
                    message: format!("Extra token: {:?}", token),
                }
            }
            LalrpopParseError::User { error } => {
                ParseErrorInfo {
                    offset: 0,
                    message: error.to_string(),
                }
            }
        }
    }
}

pub fn parse_with_errors(input: &[u8]) -> ParseResult {
    let lexer = Lexer::new(input);
    let parser = ProgramParser::new();
    match parser.parse(input, lexer) {
        Ok(program) => ParseResult {
            program: Some(program),
            errors: Vec::new(),
        },
        Err(err) => ParseResult {
            program: None,
            errors: vec![ParseErrorInfo::from_lalrpop_error(&err, input)],
        },
    }
}

pub fn parse(input: &[u8]) -> Option<Program> {
    let result = parse_with_errors(input);
    // Note: Parse errors are now reported by the caller using the diagnostic framework
    // See hwml/src/main.rs for the rendering logic
    result.program
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::Statement;

    #[test]
    fn test_parse_simple_inductive() {
        let input = b"inductive Bool : Type where | true : Bool | false : Bool";
        let program = parse(input).expect("parse failed");
        assert_eq!(program.statements.len(), 1);

        match &program.statements[0] {
            Statement::Inductive(ind) => {
                assert_eq!(&*ind.name.value, "Bool");
                assert_eq!(ind.parameters.groups.len(), 0);
                assert_eq!(ind.indices.groups.len(), 0);
                assert_eq!(ind.constructors.len(), 2);
                assert_eq!(&*ind.constructors[0].name.value, "true");
                assert_eq!(&*ind.constructors[1].name.value, "false");
            }
            _ => panic!("Expected Inductive statement"),
        }
    }

    #[test]
    fn test_parse_parameterized_inductive() {
        let input =
            b"inductive List (A : Type) : Type where | nil : List A | cons : A -> List A -> List A";
        let program = parse(input).expect("parse failed");
        assert_eq!(program.statements.len(), 1);

        match &program.statements[0] {
            Statement::Inductive(ind) => {
                assert_eq!(&*ind.name.value, "List");
                assert_eq!(ind.parameters.groups.len(), 1);
                assert_eq!(ind.indices.groups.len(), 0);
                assert_eq!(ind.constructors.len(), 2);
            }
            _ => panic!("Expected Inductive statement"),
        }
    }

    #[test]
    fn test_parse_indexed_inductive() {
        let input = b"inductive Vec (A : Type) : (n : Nat) -> Type where | vnil : Vec A 0 | vcons : (n : Nat) -> A -> Vec A n -> Vec A (n + 1)";
        let program = parse(input).expect("parse failed");
        assert_eq!(program.statements.len(), 1);

        match &program.statements[0] {
            Statement::Inductive(ind) => {
                assert_eq!(&*ind.name.value, "Vec");
                assert_eq!(ind.parameters.groups.len(), 1);
                assert_eq!(ind.indices.groups.len(), 1);
                assert_eq!(ind.constructors.len(), 2);
            }
            _ => panic!("Expected Inductive statement"),
        }
    }

    #[test]
    fn test_parse_equality_inductive() {
        let input = b"inductive Eq (A : Type) (a : A) : (b : A) -> Type where | refl : Eq A a a";
        let program = parse(input).expect("parse failed");
        assert_eq!(program.statements.len(), 1);

        match &program.statements[0] {
            Statement::Inductive(ind) => {
                assert_eq!(&*ind.name.value, "Eq");
                assert_eq!(ind.parameters.groups.len(), 2); // (A : Type) (a : A)
                assert_eq!(ind.indices.groups.len(), 1); // (b : A)
                assert_eq!(ind.constructors.len(), 1);
                assert_eq!(&*ind.constructors[0].name.value, "refl");
            }
            _ => panic!("Expected Inductive statement"),
        }
    }

    #[test]
    fn test_parse_simple_namespace() {
        let input = b"namespace Foo { def x := 1 }";
        let program = parse(input).expect("parse failed");
        assert_eq!(program.statements.len(), 1);

        match &program.statements[0] {
            Statement::Namespace(ns) => {
                assert_eq!(&*ns.name.value, "Foo");
                let segments: Vec<_> = ns.name.segments().collect();
                assert_eq!(segments.len(), 1);
                assert_eq!(segments[0], "Foo");
                assert_eq!(ns.statements.len(), 1);
            }
            _ => panic!("Expected Namespace statement"),
        }
    }

    #[test]
    fn test_parse_qualified_namespace() {
        let input = b"namespace Foo.Bar.Baz { prim Bit : Signal }";
        let program = parse(input).expect("parse failed");
        assert_eq!(program.statements.len(), 1);

        match &program.statements[0] {
            Statement::Namespace(ns) => {
                assert_eq!(&*ns.name.value, "Foo.Bar.Baz");
                let segments: Vec<_> = ns.name.segments().collect();
                assert_eq!(segments.len(), 3);
                assert_eq!(segments[0], "Foo");
                assert_eq!(segments[1], "Bar");
                assert_eq!(segments[2], "Baz");
                assert_eq!(ns.statements.len(), 1);
            }
            _ => panic!("Expected Namespace statement"),
        }
    }

    #[test]
    fn test_parse_nested_namespace() {
        let input = b"namespace Outer { namespace Inner { def x := 1 } }";
        let program = parse(input).expect("parse failed");
        assert_eq!(program.statements.len(), 1);

        match &program.statements[0] {
            Statement::Namespace(outer) => {
                assert_eq!(&*outer.name.value, "Outer");
                let segments: Vec<_> = outer.name.segments().collect();
                assert_eq!(segments.len(), 1);
                assert_eq!(segments[0], "Outer");
                assert_eq!(outer.statements.len(), 1);

                match &outer.statements[0] {
                    Statement::Namespace(inner) => {
                        assert_eq!(&*inner.name.value, "Inner");
                        let segments: Vec<_> = inner.name.segments().collect();
                        assert_eq!(segments.len(), 1);
                        assert_eq!(segments[0], "Inner");
                        assert_eq!(inner.statements.len(), 1);
                    }
                    _ => panic!("Expected nested Namespace statement"),
                }
            }
            _ => panic!("Expected Namespace statement"),
        }
    }
}
