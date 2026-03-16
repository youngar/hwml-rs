//! Common test utilities for hwml tests.
//!
//! This module provides shared helper functions for parsing, evaluating,
//! and setting up test environments.

use crate::check_module::check_module;
use crate::common::{Level, UniverseLevel};
use crate::eval;
use crate::quote::{quote, type_quote};
use crate::syn::parse::{parse_module, parse_syntax, parse_syntax_at_depth};
use crate::syn::print::print_syntax_to_string;
use crate::syn::RcSyntax;
use crate::val::{Environment, GlobalEnv, RcValue, Value};
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
pub fn eval_term<'db>(global: &GlobalEnv<'db>, stx: &RcSyntax<'db>) -> RcValue<'db> {
    let mut env = Environment::new(global);
    eval::eval(&mut env, stx).unwrap_or_else(|e| panic!("Failed to eval '{:?}': {:?}", stx, e))
}

/// Parse and evaluate a string to a value.
pub fn eval_str<'db>(db: &'db Database, global: &GlobalEnv<'db>, input: &'db str) -> RcValue<'db> {
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
) -> RcValue<'db> {
    let stx = parse_syntax_at_depth(db, input, depth)
        .unwrap_or_else(|e| panic!("Failed to parse '{}': {:?}", input, e));
    let mut env = Environment::new(global);

    // Add dummy variables to the environment
    // Variables are added as rigid variables with type U0 for simplicity
    let dummy_ty = Value::universe_rc(UniverseLevel::new(0));
    let dummy_vars: Vec<_> = (0..depth)
        .map(|i| Value::variable_rc(Level::new(i), dummy_ty.clone()))
        .collect();
    env.extend(dummy_vars);

    eval::eval(&mut env, &stx).unwrap_or_else(|e| panic!("Failed to eval '{:?}': {:?}", stx, e))
}

// ========== Enhanced Test Utilities ==========

/// Quote a value at a type and print it to a string.
/// This is useful for test assertions.
///
/// # Example
/// ```ignore
/// let val = eval_str(&db, &global, "[@Succ [@Zero]]");
/// let ty = eval_str(&db, &global, "#[@Nat]");
/// assert_eq!(print_value_to_string(&db, &global, &val, &ty), "[@Succ [@Zero]]");
/// ```
pub fn print_value_to_string<'db>(
    db: &'db Database,
    global: &GlobalEnv<'db>,
    value: &Value<'db>,
    ty: &Value<'db>,
) -> String {
    let syntax = quote(global, 0, value, ty).expect("quote failed");
    print_syntax_to_string(db, &syntax)
}

/// Quote a type and print it to a string.
/// This is useful for test assertions on types.
///
/// # Example
/// ```ignore
/// let ty = eval_str(&db, &global, "#[@Nat]");
/// assert_eq!(print_type_to_string(&db, &global, &ty), "#[@Nat]");
/// ```
pub fn print_type_to_string<'db>(
    db: &'db Database,
    global: &GlobalEnv<'db>,
    ty: &Value<'db>,
) -> String {
    let syntax = type_quote(global, 0, ty).expect("type_quote failed");
    print_syntax_to_string(db, &syntax)
}

/// Parse a context declaration of the form "%name : type".
/// Returns the variable name and the parsed type syntax.
fn parse_context_binding<'db>(
    db: &'db Database,
    binding: &'db str,
) -> Result<(String, RcSyntax<'db>), String> {
    let binding = binding.trim();
    if binding.is_empty() {
        return Err("Empty context binding".to_string());
    }

    // Split on ':'
    let parts: Vec<&str> = binding.splitn(2, ':').collect();
    if parts.len() != 2 {
        return Err(format!(
            "Invalid context binding '{}': expected '%name : type'",
            binding
        ));
    }

    let var_part = parts[0].trim();
    let ty_part = parts[1].trim();

    // Variable name should start with %
    if !var_part.starts_with('%') {
        return Err(format!(
            "Invalid variable name '{}': must start with %",
            var_part
        ));
    }

    let var_name = var_part[1..].to_string(); // Remove the %

    // Parse the type
    let ty_syntax = parse_syntax(db, ty_part)
        .map_err(|e| format!("Failed to parse type '{}': {:?}", ty_part, e))?;

    Ok((var_name, ty_syntax))
}

/// Evaluate a string with a typed variable context.
/// The input format is: "context |- expression"
/// where context is a semicolon-separated list of "%name : type" bindings.
///
/// Variables in the context are referenced by their position (0-indexed) in the expression.
/// The first variable in the context is %0, the second is %1, etc.
///
/// # Example
/// ```ignore
/// let db = Database::default();
/// let global = load_prelude(&db, NAT_PRELUDE);
/// // Context: n at level 0, m at level 1
/// // %0 (index 0) refers to m (most recent variable)
/// // %1 (index 1) refers to n (second most recent variable)
/// let val = eval_with_context(&db, &global, "%n : #[@Nat]; %m : #[@Nat] |- [@Succ %0]");
/// ```
pub fn eval_with_context<'db>(
    db: &'db Database,
    global: &GlobalEnv<'db>,
    input: &'db str,
) -> RcValue<'db> {
    // Split on '|-'
    let parts: Vec<&str> = input.splitn(2, "|-").collect();
    if parts.len() != 2 {
        panic!(
            "Invalid context syntax '{}': expected 'context |- expression'",
            input
        );
    }

    let context_str = parts[0].trim();
    let expr_str = parts[1].trim();

    // Parse context bindings
    let bindings: Vec<(String, RcSyntax<'db>)> = if context_str.is_empty() {
        Vec::new()
    } else {
        context_str
            .split(';')
            .map(|binding| {
                parse_context_binding(db, binding)
                    .unwrap_or_else(|e| panic!("Failed to parse context: {}", e))
            })
            .collect()
    };

    // Create an environment and evaluate types, adding variables
    let mut env = Environment::new(global);

    for (_var_name, ty_syntax) in &bindings {
        // Evaluate the type in the current environment
        let ty_val = eval::eval(&mut env, ty_syntax)
            .unwrap_or_else(|e| panic!("Failed to eval type '{:?}': {:?}", ty_syntax, e));

        // Add variable to environment
        let level = Level::new(env.depth());
        let var_val = Value::variable_rc(level, ty_val);
        env.push(var_val);
        env.transparent.push_rigid();
    }

    // Parse the expression with the depth set to the number of variables
    let depth = bindings.len();
    let expr_syntax = parse_syntax_at_depth(db, expr_str, depth)
        .unwrap_or_else(|e| panic!("Failed to parse expression '{}': {:?}", expr_str, e));

    // Evaluate the expression
    eval::eval(&mut env, &expr_syntax)
        .unwrap_or_else(|e| panic!("Failed to eval expression '{:?}': {:?}", expr_syntax, e))
}

/// Convenience wrapper: evaluate with context and prelude, auto-managing Database.
/// Returns the value for further inspection or use with print_value_to_string.
///
/// # Example
/// ```ignore
/// let val = eval_with_prelude_and_context(
///     NAT_PRELUDE,
///     "%n : #[@Nat] |- [@Succ %0]"
/// );
/// ```
pub fn eval_with_prelude_and_context<'db>(
    db: &'db Database,
    prelude: &'db str,
    context_and_expr: &'db str,
) -> RcValue<'db> {
    let global = load_prelude(db, prelude);
    eval_with_context(db, &global, context_and_expr)
}

/// Convenience wrapper: evaluate a simple expression with prelude, no context.
/// Auto-manages Database creation.
///
/// # Example
/// ```ignore
/// let val = eval_with_prelude(&db, NAT_PRELUDE, "[@Zero]");
/// ```
pub fn eval_with_prelude<'db>(
    db: &'db Database,
    prelude: &'db str,
    expr: &'db str,
) -> RcValue<'db> {
    let global = load_prelude(db, prelude);
    eval_str(db, &global, expr)
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
                assert_eq!(dcon.constructor.name(&db).to_string(&db), "Succ");
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
        let db = Database::default();
        let global = GlobalEnv::new();

        // Parse "%1" with depth 2 (two variables in scope)
        // With standard de Bruijn indexing:
        // - Variable at level 0 is referenced by index 1 (%1)
        // - Variable at level 1 is referenced by index 0 (%0)
        // So %1 refers to the variable at level 0
        let val = eval_str_at_depth(&db, &global, "%1", 2);

        // Should be a rigid variable at level 0
        match val.as_ref() {
            Value::Rigid(rigid) => {
                assert_eq!(rigid.head.level, Level::new(0));
            }
            other => panic!("Expected rigid variable, got {:?}", other),
        }
    }

    // =========================================================================
    // Enhanced Test Utilities Tests
    // =========================================================================

    #[test]
    fn test_print_value_to_string_nat() {
        let db = Database::default();
        let global = load_prelude(&db, NAT_PRELUDE);

        // Evaluate [@Zero]
        let val = eval_str(&db, &global, "[@Zero]");
        let ty = eval_str(&db, &global, "#[@Nat]");

        // Print it back
        assert_eq!(print_value_to_string(&db, &global, &val, &ty), "[@Zero]");
    }

    #[test]
    fn test_print_value_to_string_succ() {
        let db = Database::default();
        let global = load_prelude(&db, NAT_PRELUDE);

        // Evaluate [@Succ [@Zero]]
        let val = eval_str(&db, &global, "[@Succ [@Zero]]");
        let ty = eval_str(&db, &global, "#[@Nat]");

        // Print it back
        assert_eq!(
            print_value_to_string(&db, &global, &val, &ty),
            "[@Succ ([@Zero])]"
        );
    }

    #[test]
    fn test_print_type_to_string() {
        let db = Database::default();
        let global = load_prelude(&db, NAT_PRELUDE);

        // Evaluate #[@Nat]
        let ty = eval_str(&db, &global, "#[@Nat]");

        // Print it back
        assert_eq!(print_type_to_string(&db, &global, &ty), "#[@Nat]");
    }

    #[test]
    fn test_eval_with_context_single_var() {
        let db = Database::default();
        let global = load_prelude(&db, NAT_PRELUDE);

        // Evaluate with one variable in context
        let val = eval_with_context(&db, &global, "%n : #[@Nat] |- [@Succ %0]");

        // Should be [@Succ %0] where %0 is a rigid variable
        match val.as_ref() {
            Value::DataConstructor(dcon) => {
                assert_eq!(dcon.constructor.name(&db).to_string(&db), "Succ");
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
    fn test_eval_with_context_multiple_vars() {
        let db = Database::default();
        let global = load_prelude(&db, NAT_PRELUDE);

        // Evaluate with two variables in context
        // Context: n at level 0, m at level 1
        // %0 (index 0) refers to m (most recent, level 1)
        // %1 (index 1) refers to n (second most recent, level 0)
        let val = eval_with_context(&db, &global, "%n : #[@Nat]; %m : #[@Nat] |- [@Succ %0]");

        // Should be [@Succ %0] where %0 is a rigid variable at level 1 (m)
        match val.as_ref() {
            Value::DataConstructor(dcon) => {
                assert_eq!(dcon.constructor.name(&db).to_string(&db), "Succ");
                assert_eq!(dcon.arguments.len(), 1);
                match dcon.arguments[0].as_ref() {
                    Value::Rigid(rigid) => {
                        assert_eq!(rigid.head.level, Level::new(1));
                    }
                    other => panic!("Expected rigid variable, got {:?}", other),
                }
            }
            other => panic!("Expected data constructor, got {:?}", other),
        }
    }

    #[test]
    fn test_eval_with_context_second_var() {
        let db = Database::default();
        let global = load_prelude(&db, NAT_PRELUDE);

        // Evaluate with two variables, using the second one
        // Context: n at level 0, m at level 1
        // %0 (index 0) refers to m (most recent, level 1)
        // %1 (index 1) refers to n (second most recent, level 0)
        let val = eval_with_context(&db, &global, "%n : #[@Nat]; %m : #[@Nat] |- [@Succ %1]");

        // Should be [@Succ %1] where %1 is a rigid variable at level 0 (n)
        match val.as_ref() {
            Value::DataConstructor(dcon) => {
                assert_eq!(dcon.constructor.name(&db).to_string(&db), "Succ");
                assert_eq!(dcon.arguments.len(), 1);
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
    fn test_eval_with_context_bool() {
        let db = Database::default();
        let global = load_prelude(&db, BOOL_PRELUDE);

        // Evaluate with Bool variable
        let val = eval_with_context(&db, &global, "%b : #[@Bool] |- %0");

        // Should be a rigid variable at level 0
        match val.as_ref() {
            Value::Rigid(rigid) => {
                assert_eq!(rigid.head.level, Level::new(0));
            }
            other => panic!("Expected rigid variable, got {:?}", other),
        }
    }

    #[test]
    fn test_eval_with_prelude_and_context() {
        let db = Database::default();

        // Use the convenience wrapper
        let val = eval_with_prelude_and_context(&db, NAT_PRELUDE, "%n : #[@Nat] |- [@Succ %0]");

        // Should be [@Succ %0]
        match val.as_ref() {
            Value::DataConstructor(dcon) => {
                assert_eq!(dcon.constructor.name(&db).to_string(&db), "Succ");
            }
            other => panic!("Expected data constructor, got {:?}", other),
        }
    }

    #[test]
    fn test_eval_with_prelude() {
        let db = Database::default();

        // Use the convenience wrapper
        let val = eval_with_prelude(&db, NAT_PRELUDE, "[@Zero]");

        // Should be [@Zero]
        match val.as_ref() {
            Value::DataConstructor(dcon) => {
                assert_eq!(dcon.constructor.name(&db).to_string(&db), "Zero");
            }
            other => panic!("Expected data constructor, got {:?}", other),
        }
    }

    #[test]
    fn test_eval_with_context_empty_context() {
        let db = Database::default();
        let global = load_prelude(&db, NAT_PRELUDE);

        // Empty context should work
        let val = eval_with_context(&db, &global, " |- [@Zero]");

        match val.as_ref() {
            Value::DataConstructor(dcon) => {
                assert_eq!(dcon.constructor.name(&db).to_string(&db), "Zero");
            }
            other => panic!("Expected data constructor, got {:?}", other),
        }
    }

    #[test]
    fn test_eval_with_context_dependent_types() {
        let db = Database::default();
        let global = load_prelude(&db, VEC_PRELUDE);

        // Test with dependent types: Vec depends on Nat
        // %0 is the Nat, %1 is the element type
        let val = eval_with_context(&db, &global, "%n : #[@Nat]; %a : U0 |- #[@Vec %1 %0]");

        // Should be a type constructor application
        match val.as_ref() {
            Value::TypeConstructor(tcon) => {
                assert_eq!(tcon.constructor.name(&db).to_string(&db), "Vec");
                assert_eq!(tcon.arguments.len(), 2);
            }
            other => panic!("Expected type constructor, got {:?}", other),
        }
    }

    #[test]
    fn test_print_value_with_context() {
        let db = Database::default();
        let global = load_prelude(&db, NAT_PRELUDE);

        // Evaluate with context and print the result
        let val = eval_with_context(&db, &global, "%n : #[@Nat] |- [@Succ %0]");
        let ty = eval_str(&db, &global, "#[@Nat]");

        // The printed form should show the variable as !0 (unbound at depth 0)
        let printed = print_value_to_string(&db, &global, &val, &ty);
        assert_eq!(printed, "[@Succ !0]");
    }
}
