//! Common test utilities for hwml tests.
//!
//! This module provides shared helper functions for parsing, evaluating,
//! and setting up test environments.

use std::rc::Rc;

use crate::check_module::check_module;
use crate::eval;
use crate::syn::parse::{parse_module, parse_syntax};
use crate::syn::RcSyntax;
use crate::val::{Environment, GlobalEnv, Value};
use crate::Database;

// ========== Prelude String Constants ==========
// Note: Type constructor references use #[@Name args...], data constructor references use [@Name args...]

/// Bool type: True and False constructors
pub const BOOL_PRELUDE: &str =
    "tcon @Bool : -> U0 where dcon @True : #[@Bool] dcon @False : #[@Bool];";

/// Nat type: Zero and Succ constructors
pub const NAT_PRELUDE: &str =
    "tcon @Nat : -> U0 where dcon @Zero : #[@Nat] dcon @Succ (%n : #[@Nat]) : #[@Nat];";

/// Option type (parametric): None and Some constructors
pub const OPTION_PRELUDE: &str = "\
tcon @Option (%a : U0) : -> U0 where \
    dcon @None : #[@Option %a] \
    dcon @Some (%x : %a) : #[@Option %a];";

/// Vec type (parametric + indexed): VNil and VCons constructors
/// Note: Nat must be defined first
pub const VEC_PRELUDE: &str = "\
tcon @Nat : -> U0 where dcon @Zero : #[@Nat] dcon @Succ (%n : #[@Nat]) : #[@Nat]; \
tcon @Vec (%a : U0) : (%n : #[@Nat]) -> U0 where \
    dcon @VNil : #[@Vec %a [@Zero]] \
    dcon @VCons (%n : #[@Nat]) (%x : %a) (%xs : #[@Vec %a %n]) : #[@Vec %a [@Succ %n]];";

/// Parse a syntax string, panicking with a helpful message on failure.
pub fn parse<'db>(db: &'db Database, input: &'db str) -> RcSyntax<'db> {
    parse_syntax(db, input).unwrap_or_else(|e| panic!("Failed to parse '{}': {:?}", input, e))
}

/// Parse a prelude and build a GlobalEnv from it.
///
/// The prelude can contain primitives, constants, type constructors,
/// data constructors, and metavariable declarations.
///
/// # Example
/// ```ignore
/// let global = make_global_from_prelude(&db, r#"
///     prim @id : (%%A : U0) -> %A -> %A;
///     meta ?[0] : U0;
/// "#);
/// ```
pub fn load_prelude<'db>(db: &'db Database, prelude: &'db str) -> GlobalEnv<'db> {
    let module =
        parse_module(db, prelude).unwrap_or_else(|e| panic!("Failed to parse prelude: {:?}", e));
    let checked = check_module(db, &module, GlobalEnv::new())
        .unwrap_or_else(|e| panic!("Failed to check prelude: {:?}", e));
    checked.global_env
}

/// Evaluate a syntax term to a value.
pub fn eval_term<'db>(global: &GlobalEnv<'db>, stx: &RcSyntax<'db>) -> Rc<Value<'db>> {
    let mut env = Environment::new(global);
    eval::eval(&mut env, stx).unwrap_or_else(|e| panic!("Failed to eval '{:?}': {:?}", stx, e))
}

/// Parse and evaluate a string to a value.
pub fn eval_str<'db>(
    db: &'db Database,
    global: &GlobalEnv<'db>,
    input: &'db str,
) -> Rc<Value<'db>> {
    let stx = parse(db, input);
    eval_term(global, &stx)
}

/// Parse and evaluate a string to a value with a specific depth context.
/// This allows referencing variables by index (e.g., %0, %1, etc.).
/// The `depth` parameter specifies how many variables are in scope.
/// Variables are given dummy types (U0) for testing purposes.
///
/// # Example
/// ```ignore
/// // Create a context with 2 variables in scope
/// // %0 will be at level 1, %1 will be at level 0
/// let val = eval_str_at_depth(&db, &global, "[@Succ %0]", 2);
/// ```
pub fn eval_str_at_depth<'db>(
    db: &'db Database,
    global: &GlobalEnv<'db>,
    input: &'db str,
    depth: usize,
) -> Rc<Value<'db>> {
    use crate::common::{Level, UniverseLevel};
    use crate::syn::parse::parse_syntax_at_depth;

    let stx = parse_syntax_at_depth(db, input, depth)
        .unwrap_or_else(|e| panic!("Failed to parse '{}': {:?}", input, e));
    let mut env = Environment::new(global);

    // Add dummy variables to the environment
    // Variables are added as rigid variables with type U0 for simplicity
    let dummy_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
    let dummy_vars: Vec<_> = (0..depth)
        .map(|i| Rc::new(Value::variable(Level::new(i), dummy_ty.clone())))
        .collect();
    env.extend(dummy_vars);

    eval::eval(&mut env, &stx).unwrap_or_else(|e| panic!("Failed to eval '{:?}': {:?}", stx, e))
}

#[cfg(test)]
mod tests {
    use super::*;
    use hwml_support::IntoWithDb;

    #[test]
    fn test_nat_prelude_parses() {
        let db = Database::default();
        let global = load_prelude(&db, NAT_PRELUDE);
        // Verify Nat type constructor is defined
        assert!(global.type_constructor("Nat".into_with_db(&db)).is_ok());
    }

    #[test]
    fn test_bool_prelude_parses() {
        let db = Database::default();
        let global = load_prelude(&db, BOOL_PRELUDE);
        // Verify Bool type constructor is defined
        assert!(global.type_constructor("Bool".into_with_db(&db)).is_ok());
    }

    #[test]
    fn test_vec_prelude_parses() {
        let db = Database::default();
        let global = load_prelude(&db, VEC_PRELUDE);
        // Verify Vec type constructor is defined
        assert!(global.type_constructor("Vec".into_with_db(&db)).is_ok());
        // Verify Nat is also defined (included in VEC_PRELUDE)
        assert!(global.type_constructor("Nat".into_with_db(&db)).is_ok());
    }

    #[test]
    fn test_eval_str_at_depth() {
        use crate::common::Level;

        let db = Database::default();
        let global = load_prelude(&db, NAT_PRELUDE);

        // Parse "[@Succ %0]" with depth 1 (one variable in scope)
        // %0 should reference the variable at level 0
        let val = eval_str_at_depth(&db, &global, "[@Succ %0]", 1);

        // Should be a data constructor application
        match val.as_ref() {
            Value::DataConstructor(dcon) => {
                assert_eq!(dcon.constructor.name(&db), "Succ");
                assert_eq!(dcon.arguments.len(), 1);
                // The argument should be a rigid variable at level 0
                match dcon.arguments[0].as_ref() {
                    Value::Rigid(rigid) => {
                        assert_eq!(rigid.head.level, Level::new(0));
                    }
                    other => panic!("Expected rigid variable, got {:?}", other),
                }
            }
            other => panic!("Expected data constructor, got {:?}", other),
        }
    }

    #[test]
    fn test_eval_str_at_depth_multiple_vars() {
        use crate::common::Level;

        let db = Database::default();
        let global = GlobalEnv::new();

        // Parse "%1" with depth 2 (two variables in scope)
        // %0 is at index 0 (level 1), %1 is at index 1 (level 0)
        // But we're parsing %1 which refers to the name "1" at index 1
        // which corresponds to level 1 (since we pushed "0" first, then "1")
        let val = eval_str_at_depth(&db, &global, "%1", 2);

        // Should be a rigid variable at level 1
        match val.as_ref() {
            Value::Rigid(rigid) => {
                assert_eq!(rigid.head.level, Level::new(1));
            }
            other => panic!("Expected rigid variable, got {:?}", other),
        }
    }
}
