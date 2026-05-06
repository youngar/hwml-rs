use hwml_support::LineInfo;
use lalrpop_util::lalrpop_mod;

use crate::{lex::Lexer, parsing::grammar::ProgramParser, syntax::Program};

lalrpop_mod!(
    #[allow(clippy::ptr_arg)]
    #[rustfmt::skip]
    pub grammar
);

/// Helper struct to track line information during parsing.
///
/// **NEW APPROACH**: Because HWML uses a lossless grammar, the lexer now
/// tracks line:column natively as it streams tokens (see `LocLexer`).
/// This ParserContext now uses lazy LineInfo only as a fallback for
/// byte-offset-based grammar rules during migration.
pub struct ParserContext {
    /// Lazy-initialized LineInfo (only created if needed for byte offset conversion)
    line_info: Option<LineInfo>,
    /// Source input (for lazy LineInfo construction)
    input: Vec<u8>,
}

impl ParserContext {
    pub fn new(input: &[u8]) -> Self {
        ParserContext {
            line_info: None,
            input: input.to_vec(),
        }
    }

    /// Convert a byte offset to (line, column) - both 0-based
    ///
    /// **DEPRECATED**: Prefer using `LocLexer` which tracks line:column natively.
    /// This is only for backward compatibility during migration.
    pub fn offset_to_line_col(&mut self, offset: usize) -> (usize, usize) {
        let line_info = self
            .line_info
            .get_or_insert_with(|| LineInfo::from_bytes(&self.input));
        line_info.loc(offset)
    }

    /// Convert a byte range to (start_line, start_col, end_line, end_col) - all 0-based
    ///
    /// **DEPRECATED**: Prefer using `LocLexer` which provides start location directly.
    /// This is only for backward compatibility during migration.
    pub fn range_to_line_col(&mut self, start: usize, end: usize) -> (usize, usize, usize, usize) {
        let line_info = self
            .line_info
            .get_or_insert_with(|| LineInfo::from_bytes(&self.input));
        let (start_line, start_col) = line_info.loc(start);
        let (end_line, end_col) = line_info.loc(end);
        (start_line, start_col, end_line, end_col)
    }
}

pub fn parse(input: &[u8]) -> Option<Program> {
    let mut ctx = ParserContext::new(input);
    let lexer = Lexer::new(input);
    let parser = ProgramParser::new();
    let result = parser.parse(input, &mut ctx, lexer);
    match result {
        Ok(program) => Some(program),
        Err(err) => {
            eprintln!("Error: {err:?}");
            None
        }
    }
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
                assert_eq!(std::str::from_utf8(&ind.name.value).unwrap(), "Bool");
                assert_eq!(ind.parameters.groups.len(), 0);
                assert_eq!(ind.indices.groups.len(), 0);
                assert_eq!(ind.constructors.len(), 2);
                assert_eq!(
                    std::str::from_utf8(&ind.constructors[0].name.value).unwrap(),
                    "true"
                );
                assert_eq!(
                    std::str::from_utf8(&ind.constructors[1].name.value).unwrap(),
                    "false"
                );
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
                assert_eq!(std::str::from_utf8(&ind.name.value).unwrap(), "List");
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
                assert_eq!(std::str::from_utf8(&ind.name.value).unwrap(), "Vec");
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
                assert_eq!(std::str::from_utf8(&ind.name.value).unwrap(), "Eq");
                assert_eq!(ind.parameters.groups.len(), 2); // (A : Type) (a : A)
                assert_eq!(ind.indices.groups.len(), 1); // (b : A)
                assert_eq!(ind.constructors.len(), 1);
                assert_eq!(
                    std::str::from_utf8(&ind.constructors[0].name.value).unwrap(),
                    "refl"
                );
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
                assert_eq!(std::str::from_utf8(&ns.name.value).unwrap(), "Foo");
                let segments: Vec<_> = ns.name.segments().collect();
                assert_eq!(segments.len(), 1);
                assert_eq!(segments[0], b"Foo");
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
                assert_eq!(std::str::from_utf8(&ns.name.value).unwrap(), "Foo.Bar.Baz");
                let segments: Vec<_> = ns.name.segments().collect();
                assert_eq!(segments.len(), 3);
                assert_eq!(segments[0], b"Foo");
                assert_eq!(segments[1], b"Bar");
                assert_eq!(segments[2], b"Baz");
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
                assert_eq!(std::str::from_utf8(&outer.name.value).unwrap(), "Outer");
                let segments: Vec<_> = outer.name.segments().collect();
                assert_eq!(segments.len(), 1);
                assert_eq!(segments[0], b"Outer");
                assert_eq!(outer.statements.len(), 1);

                match &outer.statements[0] {
                    Statement::Namespace(inner) => {
                        assert_eq!(std::str::from_utf8(&inner.name.value).unwrap(), "Inner");
                        let segments: Vec<_> = inner.name.segments().collect();
                        assert_eq!(segments.len(), 1);
                        assert_eq!(segments[0], b"Inner");
                        assert_eq!(inner.statements.len(), 1);
                    }
                    _ => panic!("Expected nested Namespace statement"),
                }
            }
            _ => panic!("Expected Namespace statement"),
        }
    }
}
