//! Test utilities for the elaborator.
//!
//! This module provides helper functions for writing elaboration tests,
//! including snapshot testing support similar to LLVM's FileCheck/lit tests.

use hwml_core::{
    check::TCEnvironment,
    quote::type_quote,
    syn::{print::print_syntax_to_string, RcSyntax},
    val::{Environment, GlobalEnv, RcValue},
};

use crate::{
    elaborator::ElaborationContext,
    engine::{SingleThreadedExecutor, SolverEnvironment},
};

// ========== Prelude String Constants ==========
// These match the core test_utils preludes but are duplicated here for convenience

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

// ========== Parsing Helpers ==========

/// Parse a surface expression from a string.
/// Panics with a helpful message on failure.
///
/// This wraps the expression in a minimal def statement to use the ProgramParser,
/// then extracts the expression from the parsed definition.
pub fn parse_surface(input: &str) -> hwml_surface::syntax::Expression {
    // Wrap the expression in a def statement so we can parse it
    let wrapped = format!("def __test := {}", input);
    let program = hwml_surface::parsing::parse(wrapped.as_bytes())
        .unwrap_or_else(|| panic!("Failed to parse surface expression '{}'", input));

    // Extract the expression from the first (and only) statement
    match program.statements.first() {
        Some(hwml_surface::syntax::Statement::Def(def)) => (*def.value).clone(),
        _ => panic!("Expected a def statement when parsing '{}'", input),
    }
}

// ========== Elaboration Helpers ==========

/// Create a test elaboration context with the given global environment.
/// The caller must create and own the GlobalEnv to ensure proper lifetimes.
pub fn make_test_context<'db, 'g>(
    db: &'db dyn salsa::Database,
    global: &'g GlobalEnv<'db>,
) -> ElaborationContext<'db, 'g> {
    let executor = SingleThreadedExecutor::new();
    let tc_env = TCEnvironment {
        db,
        values: Environment::new(global),
        types: Vec::new(),
    };
    let solver = SolverEnvironment::new(tc_env, executor.spawner());
    ElaborationContext::new(db, None, solver)
}

/// Elaborate a surface expression to core syntax, synthesizing its type.
/// Returns (term, type) as core syntax.
pub fn elaborate_synth<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    expr: &hwml_surface::syntax::Expression,
) -> (RcSyntax<'db>, RcSyntax<'db>) {
    let (term, ty_value) =
        futures::executor::block_on(async { crate::elaborator::synth(ctx, expr).await });

    // Quote the type back to syntax for easier inspection
    let ty_syntax = type_quote(ctx.solver.tc_env.values.global, ctx.depth(), &ty_value)
        .unwrap_or_else(|_| {
            hwml_core::syn::Syntax::universe_rc(hwml_core::common::UniverseLevel::new(0))
        });

    (term.into_inner(), ty_syntax)
}

/// Elaborate a surface expression against an expected type.
/// Returns the elaborated core syntax term.
pub fn elaborate_check<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    expr: &hwml_surface::syntax::Expression,
    expected_ty: RcValue<'db>,
) -> RcSyntax<'db> {
    futures::executor::block_on(async { crate::elaborator::check(ctx, expr, expected_ty).await })
        .into_inner()
}

// ========== Pretty Printing Helpers ==========

/// Print a core syntax term to a string.
pub fn print_term(_db: &dyn salsa::Database, term: &RcSyntax) -> String {
    // We need the concrete Database type for printing
    let db_impl = hwml_core::Database::default();
    print_syntax_to_string(&db_impl, term)
}

/// Print a core syntax type to a string.
pub fn print_type(_db: &dyn salsa::Database, ty: &RcSyntax) -> String {
    // We need the concrete Database type for printing
    let db_impl = hwml_core::Database::default();
    print_syntax_to_string(&db_impl, ty)
}

// ========== Snapshot Testing Helpers ==========

/// Format an elaboration result for snapshot testing.
/// Returns a string in the format:
/// ```
/// INPUT:
/// <surface expression>
///
/// TERM:
/// <elaborated core term>
///
/// TYPE:
/// <synthesized type>
/// ```
pub fn format_elab_snapshot(
    db: &dyn salsa::Database,
    input: &str,
    term: &RcSyntax,
    ty: &RcSyntax,
) -> String {
    format!(
        "INPUT:\n{}\n\nTERM:\n{}\n\nTYPE:\n{}",
        input,
        print_term(db, term),
        print_type(db, ty)
    )
}

/// Format a check elaboration result for snapshot testing.
/// Returns a string in the format:
/// ```
/// INPUT:
/// <surface expression>
///
/// EXPECTED TYPE:
/// <expected type>
///
/// TERM:
/// <elaborated core term>
/// ```
pub fn format_check_snapshot(
    db: &dyn salsa::Database,
    input: &str,
    expected_ty_str: &str,
    term: &RcSyntax,
) -> String {
    format!(
        "INPUT:\n{}\n\nEXPECTED TYPE:\n{}\n\nTERM:\n{}",
        input,
        expected_ty_str,
        print_term(db, term)
    )
}
