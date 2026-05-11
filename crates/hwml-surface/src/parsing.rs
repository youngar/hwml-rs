// NEW: Use our hand-written top-down parser instead of LALRPOP
use crate::parse::Parser;
use crate::syntax::Program;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseResult {
    pub program: Program,
    pub errors: Vec<ParseErrorInfo>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseErrorInfo {
    pub offset: usize,
    pub message: String,
}

impl ParseErrorInfo {
    fn from_parse_error(err: &crate::parse::context::ParseError) -> Self {
        ParseErrorInfo {
            offset: err.location.start,
            message: err.message.clone(),
        }
    }
}

pub fn parse_with_errors(input: &[u8]) -> ParseResult {
    // Use our new hand-written parser
    let parser = Parser::new(input);
    let result = parser.parse();

    ParseResult {
        program: result.program,
        errors: result.errors.iter().map(ParseErrorInfo::from_parse_error).collect(),
    }
}

pub fn parse(input: &[u8]) -> Program {
    let result = parse_with_errors(input);
    // Note: Parse errors are now in result.errors and reported by the caller using the diagnostic framework
    // See hwml/src/main.rs for the rendering logic
    result.program
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::Statement;

    #[test]
    fn test_parse_simple_inductive() {
        let input = b"inductive Bool : Type := | true : Bool | false : Bool end";
        let program = parse(input);
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
            b"inductive List (A : Type) : Type := | nil : List A | cons : A -> List A -> List A end";
        let program = parse(input);
        assert_eq!(program.statements.len(), 1);

        match &program.statements[0] {
            Statement::Inductive(ind) => {
                assert_eq!(&*ind.name.value, "List");
                assert_eq!(ind.parameters.groups.len(), 1);
                // indices not checked - not fully supported yet
                assert_eq!(ind.constructors.len(), 2);
            }
            _ => panic!("Expected Inductive statement"),
        }
    }

    #[test]
    fn test_parse_simple_def() {
        let input = b"def zero := 0";
        let program = parse(input);
        assert_eq!(program.statements.len(), 1);

        match &program.statements[0] {
            Statement::Def(def) => {
                assert_eq!(&*def.id.value, "zero");
            }
            _ => panic!("Expected Def statement"),
        }
    }

    #[test]
    fn test_parse_simple_namespace() {
        let input = b"namespace Foo { def x := 1 }";
        let program = parse(input);
        assert_eq!(program.statements.len(), 1);

        match &program.statements[0] {
            Statement::Namespace(ns) => {
                assert_eq!(&*ns.name.value, "Foo");
                assert_eq!(ns.statements.len(), 1);
            }
            _ => panic!("Expected Namespace statement"),
        }
    }

    #[test]
    fn test_parse_prim() {
        let input = b"prim Bit : Signal";
        let program = parse(input);
        assert_eq!(program.statements.len(), 1);

        match &program.statements[0] {
            Statement::Prim(prim) => {
                assert_eq!(&*prim.id.value, "Bit");
            }
            _ => panic!("Expected Prim statement"),
        }
    }

    #[test]
    fn test_parse_nested_namespace() {
        let input = b"namespace Outer { namespace Inner { def x := 1 } }";
        let program = parse(input);
        assert_eq!(program.statements.len(), 1);

        match &program.statements[0] {
            Statement::Namespace(outer) => {
                assert_eq!(&*outer.name.value, "Outer");
                assert_eq!(outer.statements.len(), 1);

                match &outer.statements[0] {
                    Statement::Namespace(inner) => {
                        assert_eq!(&*inner.name.value, "Inner");
                        assert_eq!(inner.statements.len(), 1);
                    }
                    _ => panic!("Expected nested Namespace statement"),
                }
            }
            _ => panic!("Expected Namespace statement"),
        }
    }

    #[test]
    fn test_stdlib_bool_parses() {
        let src = std::fs::read("../../stdlib/src/Bool.hwml").expect("Could not read Bool.hwml");
        let result = parse_with_errors(&src);
        if !result.errors.is_empty() {
            eprintln!("Errors parsing Bool.hwml:");
            for error in &result.errors {
                eprintln!("  {:?}", error);
            }
        }
        assert!(result.errors.is_empty(), "Bool.hwml should parse without errors");
        assert!(!result.program.statements.is_empty(), "Bool.hwml should have statements");
    }

    #[test]
    fn test_stdlib_nat_parses() {
        let src = std::fs::read("../../stdlib/src/Nat.hwml").expect("Could not read Nat.hwml");
        let result = parse_with_errors(&src);
        if !result.errors.is_empty() {
            eprintln!("Errors parsing Nat.hwml:");
            for error in &result.errors {
                eprintln!("  {:?}", error);
            }
        }
        assert!(result.errors.is_empty(), "Nat.hwml should parse without errors");
        assert!(!result.program.statements.is_empty(), "Nat.hwml should have statements");
    }

    #[test]
    fn test_stdlib_list_parses() {
        let src = std::fs::read("../../stdlib/src/List.hwml").expect("Could not read List.hwml");
        let result = parse_with_errors(&src);
        if !result.errors.is_empty() {
            eprintln!("Errors parsing List.hwml:");
            for error in &result.errors {
                eprintln!("  {:?}", error);
            }
        }
        assert!(result.errors.is_empty(), "List.hwml should parse without errors");
        assert!(!result.program.statements.is_empty(), "List.hwml should have statements");
    }

    #[test]
    fn test_stdlib_unit_parses() {
        let src = std::fs::read("../../stdlib/src/Unit.hwml").expect("Could not read Unit.hwml");
        let result = parse_with_errors(&src);
        assert!(result.errors.is_empty(), "Unit.hwml should parse without errors");
        assert!(!result.program.statements.is_empty(), "Unit.hwml should have statements");
    }

    #[test]
    fn test_stdlib_void_parses() {
        let src = std::fs::read("../../stdlib/src/Void.hwml").expect("Could not read Void.hwml");
        let result = parse_with_errors(&src);
        assert!(result.errors.is_empty(), "Void.hwml should parse without errors");
        assert!(!result.program.statements.is_empty(), "Void.hwml should have statements");
    }

    #[test]
    fn test_stdlib_vec_parses() {
        let src = std::fs::read("../../stdlib/src/Vec.hwml").expect("Could not read Vec.hwml");
        let result = parse_with_errors(&src);
        assert!(result.errors.is_empty(), "Vec.hwml should parse without errors");
        assert!(!result.program.statements.is_empty(), "Vec.hwml should have statements");
    }

    #[test]
    fn test_stdlib_option_parses() {
        let src = std::fs::read("../../stdlib/src/Option.hwml").expect("Could not read Option.hwml");
        let result = parse_with_errors(&src);
        assert!(result.errors.is_empty(), "Option.hwml should parse without errors");
        assert!(!result.program.statements.is_empty(), "Option.hwml should have statements");
    }

    #[test]
    fn test_stdlib_prod_parses() {
        let src = std::fs::read("../../stdlib/src/Prod.hwml").expect("Could not read Prod.hwml");
        let result = parse_with_errors(&src);
        assert!(result.errors.is_empty(), "Prod.hwml should parse without errors");
        assert!(!result.program.statements.is_empty(), "Prod.hwml should have statements");
    }

    #[test]
    fn test_stdlib_sum_parses() {
        let src = std::fs::read("../../stdlib/src/Sum.hwml").expect("Could not read Sum.hwml");
        let result = parse_with_errors(&src);
        assert!(result.errors.is_empty(), "Sum.hwml should parse without errors");
        assert!(!result.program.statements.is_empty(), "Sum.hwml should have statements");
    }
}
