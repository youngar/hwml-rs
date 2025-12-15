//! Binary executable to run hwml-core examples.
//!
//! This executable runs all the examples from the hwml-core examples module.
//!
//! Run with:
//! ```
//! cargo run --manifest-path crates/hwml-core/fuzz/Cargo.toml --bin run_examples
//! ```

use hwml_core::common::UniverseLevel;
use hwml_core::eval;
use hwml_core::quote;
use hwml_core::syn::parse::parse_syntax;
use hwml_core::syn::print::print_syntax_to_string;
use hwml_core::syn::{RcSyntax, Syntax};
use hwml_core::val::{Closure, Environment, GlobalEnv, LocalEnv, Value};
use hwml_core::Database;
use std::rc::Rc;

// ============================================================================
// Helper Functions
// ============================================================================

/// Parse an input string and print the parsed syntax.
fn parse_and_print<'db>(db: &'db Database, input: &'db str) -> Result<RcSyntax<'db>, String> {
    println!("Input string: {}", input);
    let syntax = parse_syntax(db, input).map_err(|e| format!("Parse error: {:?}", e))?;
    println!("Parsed syntax: {:?}", syntax);
    Ok(syntax)
}

/// Create an empty environment (no global definitions, no local variables).
fn empty_env<'db>() -> GlobalEnv<'db> {
    GlobalEnv::new()
}

/// Evaluate a syntax term and print the result.
fn eval_and_print<'g, 'db>(
    env: &mut Environment<'g, 'db>,
    syntax: &RcSyntax<'db>,
) -> Result<Rc<Value<'db>>, String> {
    let value = eval::eval(env, syntax).map_err(|e| format!("Eval error: {:?}", e))?;
    println!("Evaluated value: {:?}", value);
    Ok(value)
}

/// Print a type.
fn print_type<'db>(
    db: &'db Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    ty: &Rc<Value<'db>>,
) -> Result<(), String> {
    let ty_syntax =
        quote::quote(db, global, depth, ty, ty).map_err(|e| format!("Quote error: {:?}", e))?;
    let ty_str = print_syntax_to_string(db, &ty_syntax);
    println!("Type: {}", ty_str);
    Ok(())
}

/// Quote a value back to syntax and print it.
fn quote_and_print<'db>(
    db: &'db Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    ty: &Rc<Value<'db>>,
    value: &Rc<Value<'db>>,
) -> Result<(), String> {
    let quoted =
        quote::quote(db, global, depth, ty, value).map_err(|e| format!("Quote error: {:?}", e))?;
    let quoted_str = print_syntax_to_string(db, &quoted);
    println!("Quoted syntax: {}", quoted_str);
    Ok(())
}

/// Quote a type and print it.
fn quote_type_and_print<'db>(
    db: &'db Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Rc<Value<'db>>,
) -> Result<(), String> {
    let ty = Rc::new(Value::universe(UniverseLevel::new(1)));
    quote_and_print(db, global, depth, &ty, value)
}

// ============================================================================
// Examples
// ============================================================================

/// Example 1: Evaluating and quoting a simple universe
pub fn example_universe<'db>(db: &'db Database) -> Result<(), String> {
    println!("\n=== Example 1: Universe ===");

    let syntax = parse_and_print(db, "𝒰0")?;
    let global = empty_env();
    let mut env = Environment {
        global: &global,
        local: LocalEnv::new(),
    };

    // Type of 𝒰0 is 𝒰1
    let ty = Rc::new(Value::universe(UniverseLevel::new(1)));
    print_type(db, &global, 0, &ty)?;

    let value = eval_and_print(&mut env, &syntax)?;
    quote_type_and_print(db, &global, 0, &value)?;

    Ok(())
}

/// Example 2: Evaluating and quoting a lambda expression
pub fn example_lambda<'db>(db: &'db Database) -> Result<(), String> {
    println!("\n=== Example 2: Lambda (Identity Function) ===");

    let syntax = parse_and_print(db, "λ %x → %x")?;
    let global = empty_env();
    let mut env = Environment {
        global: &global,
        local: LocalEnv::new(),
    };
    let value = eval_and_print(&mut env, &syntax)?;

    // To quote a lambda, we need its type (a Pi type: Type₀ → Type₀)
    let universe = Rc::new(Value::universe(UniverseLevel::new(0)));
    let pi_target_closure =
        Closure::new(LocalEnv::new(), Syntax::universe_rc(UniverseLevel::new(0)));
    let pi_type = Rc::new(Value::pi(universe, pi_target_closure));

    print_type(db, &global, 0, &pi_type)?;
    quote_and_print(db, &global, 0, &pi_type, &value)?;

    Ok(())
}

/// Run all examples
pub fn run_all_examples() {
    let db = Database::new();

    println!("Running eval and quote examples...\n");

    let _ = example_universe(&db);
    let _ = example_lambda(&db);

    println!("\n=== All examples completed ===");
}

fn main() {
    println!("╔═══════════════════════════════════════════════════════════════╗");
    println!("║  HWML-Core: Running Examples                                 ║");
    println!("╚═══════════════════════════════════════════════════════════════╝");
    println!();

    run_all_examples();

    println!();
    println!("✓ All examples completed successfully!");
}
