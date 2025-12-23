//! Comprehensive examples demonstrating the unification API.
//!
//! This module contains practical examples showing how to:
//! - Create and use MetaContext for managing metavariables
//! - Unify different types of values (universes, lambdas, pi types, etc.)
//! - Handle pattern unification and metavariable solving
//! - Work with rigid and flexible terms
//! - Test various unification scenarios

use hwml_core::common::{Level, UniverseLevel};
use hwml_core::unify::{unify, MetaContext, UnificationError};
use hwml_core::val::{Closure, GlobalEnv, LocalEnv, Value};
use hwml_core::Database;
use std::rc::Rc;

// ============================================================================
// Helper Functions
// ============================================================================

/// Create an empty global environment for testing.
fn empty_global_env<'db>() -> GlobalEnv<'db> {
    GlobalEnv::new()
}

/// Create a new MetaContext for testing.
fn new_meta_context<'db>() -> MetaContext<'db> {
    MetaContext::new()
}

/// Print the result of a unification attempt.
fn print_unify_result<'db>(name: &str, result: Result<(), UnificationError<'db>>) {
    match result {
        Ok(()) => println!("✓ {}: Unification succeeded", name),
        Err(e) => println!("✗ {}: Unification failed: {:?}", name, e),
    }
}

// ============================================================================
// Basic Unification Examples
// ============================================================================

/// Example 1: Unifying two identical universes
///
/// This is the simplest case: Type₀ =?= Type₀
pub fn example_unify_universes<'db>(db: &'db Database) {
    println!("\n=== Example 1: Unifying Identical Universes ===");

    let global = empty_global_env();
    let mut mctx = new_meta_context();

    let u0 = Rc::new(Value::universe(UniverseLevel::new(0)));
    let u0_copy = Rc::new(Value::universe(UniverseLevel::new(0)));

    let result = unify(db, &global, &mut mctx, 0, u0, u0_copy);
    print_unify_result("Type₀ =?= Type₀", result);
}

/// Example 2: Unifying different universes (should fail)
///
/// This should fail: Type₀ ≠ Type₁
pub fn example_unify_different_universes<'db>(db: &'db Database) {
    println!("\n=== Example 2: Unifying Different Universes (should fail) ===");

    let global = empty_global_env();
    let mut mctx = new_meta_context();

    let u0 = Rc::new(Value::universe(UniverseLevel::new(0)));
    let u1 = Rc::new(Value::universe(UniverseLevel::new(1)));

    let result = unify(db, &global, &mut mctx, 0, u0, u1);
    print_unify_result("Type₀ =?= Type₁", result);
}

/// Example 3: Unifying rigid variables
///
/// Unifying two identical bound variables: x =?= x
pub fn example_unify_rigid_variables<'db>(db: &'db Database) {
    println!("\n=== Example 3: Unifying Rigid Variables ===");

    let global = empty_global_env();
    let mut mctx = new_meta_context();

    let ty = Rc::new(Value::universe(UniverseLevel::new(0)));
    let var0 = Rc::new(Value::variable(ty.clone(), Level::new(0)));
    let var0_copy = Rc::new(Value::variable(ty, Level::new(0)));

    let result = unify(db, &global, &mut mctx, 1, var0, var0_copy);
    print_unify_result("x =?= x", result);
}

/// Example 4: Unifying different rigid variables (should fail)
///
/// This should fail: x ≠ y
pub fn example_unify_different_variables<'db>(db: &'db Database) {
    println!("\n=== Example 4: Unifying Different Variables (should fail) ===");

    let global = empty_global_env();
    let mut mctx = new_meta_context();

    let ty = Rc::new(Value::universe(UniverseLevel::new(0)));
    let var0 = Rc::new(Value::variable(ty.clone(), Level::new(0)));
    let var1 = Rc::new(Value::variable(ty, Level::new(1)));

    let result = unify(db, &global, &mut mctx, 2, var0, var1);
    print_unify_result("x =?= y", result);
}

// ============================================================================
// Lambda Unification Examples
// ============================================================================

/// Example 5: Unifying two identical lambdas
///
/// Unifying: (λx. x) =?= (λy. y)
pub fn example_unify_lambdas<'db>(db: &'db Database) {
    println!("\n=== Example 5: Unifying Identical Lambdas ===");

    let global = empty_global_env();
    let mut mctx = new_meta_context();

    // Create (λx. x)
    let var0_syntax = hwml_core::syn::Syntax::variable_rc(hwml_core::common::Index(0));
    let lambda1_body = Closure::new(LocalEnv::new(), var0_syntax.clone());
    let lambda1 = Rc::new(Value::lambda(lambda1_body));

    // Create (λy. y) - same structure, different name
    let lambda2_body = Closure::new(LocalEnv::new(), var0_syntax);
    let lambda2 = Rc::new(Value::lambda(lambda2_body));

    let result = unify(db, &global, &mut mctx, 0, lambda1, lambda2);
    print_unify_result("(λx. x) =?= (λy. y)", result);
}

/// Example 6: Eta-expansion during unification
///
/// Unifying: (λx. f x) =?= f
pub fn example_unify_eta_expansion<'db>(_db: &'db Database) {
    println!("\n=== Example 6: Eta-Expansion ===");

    let _global = empty_global_env();
    let mut _mctx = new_meta_context();

    // This example demonstrates eta-conversion
    // In practice, we'd need to construct the appropriate terms
    println!("Note: Eta-expansion is handled automatically during unification");
}

// ============================================================================
// Pi Type Unification Examples
// ============================================================================

/// Example 7: Unifying identical Pi types
///
/// Unifying: (A : Type) -> A =?= (B : Type) -> B
pub fn example_unify_pi_types<'db>(db: &'db Database) {
    println!("\n=== Example 7: Unifying Pi Types ===");

    let global = empty_global_env();
    let mut mctx = new_meta_context();

    let u0 = Rc::new(Value::universe(UniverseLevel::new(0)));

    // Create (A : Type) -> A
    let var0_syntax = hwml_core::syn::Syntax::variable_rc(hwml_core::common::Index(0));
    let target1 = Closure::new(LocalEnv::new(), var0_syntax.clone());
    let pi1 = Rc::new(Value::pi(u0.clone(), target1));

    // Create (B : Type) -> B
    let target2 = Closure::new(LocalEnv::new(), var0_syntax);
    let pi2 = Rc::new(Value::pi(u0, target2));

    let result = unify(db, &global, &mut mctx, 0, pi1, pi2);
    print_unify_result("(A : Type) -> A =?= (B : Type) -> B", result);
}

/// Example 8: Unifying Pi types with different sources (should fail)
///
/// This should fail: (A : Type₀) -> A ≠ (A : Type₁) -> A
pub fn example_unify_pi_different_sources<'db>(db: &'db Database) {
    println!("\n=== Example 8: Unifying Pi Types with Different Sources (should fail) ===");

    let global = empty_global_env();
    let mut mctx = new_meta_context();

    let u0 = Rc::new(Value::universe(UniverseLevel::new(0)));
    let u1 = Rc::new(Value::universe(UniverseLevel::new(1)));

    let var0_syntax = hwml_core::syn::Syntax::variable_rc(hwml_core::common::Index(0));

    // Create (A : Type₀) -> A
    let target1 = Closure::new(LocalEnv::new(), var0_syntax.clone());
    let pi1 = Rc::new(Value::pi(u0, target1));

    // Create (A : Type₁) -> A
    let target2 = Closure::new(LocalEnv::new(), var0_syntax);
    let pi2 = Rc::new(Value::pi(u1, target2));

    let result = unify(db, &global, &mut mctx, 0, pi1, pi2);
    print_unify_result("(A : Type₀) -> A =?= (A : Type₁) -> A", result);
}

// ============================================================================
// Metavariable Unification Examples
// ============================================================================

/// Example 9: Creating and using metavariables
///
/// Demonstrates how to create metavariables and use them in unification
pub fn example_create_metavariables<'db>(_db: &'db Database) {
    println!("\n=== Example 9: Creating Metavariables ===");

    let _global = empty_global_env();
    let mut mctx = new_meta_context();

    // Create a fresh metavariable
    let meta_id = mctx.fresh_id();
    println!("Created metavariable: {:?}", meta_id);

    // Create a metavariable value
    let meta_value = Rc::new(Value::metavariable(meta_id, LocalEnv::new()));
    println!("Metavariable value: {:?}", meta_value);
}

/// Example 10: Unifying a metavariable with a concrete value
///
/// Solving: ?M =?= Type₀
pub fn example_unify_meta_with_universe<'db>(db: &'db Database) {
    println!("\n=== Example 10: Unifying Metavariable with Universe ===");

    let global = empty_global_env();
    let mut mctx = new_meta_context();

    // Create a metavariable
    let meta_id = mctx.fresh_id();
    let meta = Rc::new(Value::metavariable(meta_id, LocalEnv::new()));

    // Create a universe
    let u0 = Rc::new(Value::universe(UniverseLevel::new(0)));

    println!("Before unification:");
    println!("  Metavariable solution: {:?}", mctx.lookup(meta_id));

    let result = unify(db, &global, &mut mctx, 0, meta, u0);
    print_unify_result("?M =?= Type₀", result);

    println!("After unification:");
    println!("  Metavariable solution: {:?}", mctx.lookup(meta_id));
}

/// Example 11: Unifying two metavariables (flex-flex)
///
/// Solving: ?M =?= ?N
pub fn example_unify_two_metavariables<'db>(db: &'db Database) {
    println!("\n=== Example 11: Unifying Two Metavariables (Flex-Flex) ===");

    let global = empty_global_env();
    let mut mctx = new_meta_context();

    // Create two metavariables
    let meta1_id = mctx.fresh_id();
    let meta2_id = mctx.fresh_id();

    let meta1 = Rc::new(Value::metavariable(meta1_id, LocalEnv::new()));
    let meta2 = Rc::new(Value::metavariable(meta2_id, LocalEnv::new()));

    println!("Before unification:");
    println!("  ?M solution: {:?}", mctx.lookup(meta1_id));
    println!("  ?N solution: {:?}", mctx.lookup(meta2_id));

    let result = unify(db, &global, &mut mctx, 0, meta1, meta2);
    print_unify_result("?M =?= ?N", result);

    println!("After unification:");
    println!("  ?M solution: {:?}", mctx.lookup(meta1_id));
    println!("  ?N solution: {:?}", mctx.lookup(meta2_id));
}

// ============================================================================
// Type Constructor Unification Examples
// ============================================================================

/// Example 12: Unifying type constructors
///
/// Unifying: Vec Nat n =?= Vec Nat n
pub fn example_unify_type_constructors<'db>(db: &'db Database) {
    println!("\n=== Example 12: Unifying Type Constructors ===");

    let global = empty_global_env();
    let mut mctx = new_meta_context();

    use hwml_core::syn::ConstantId;
    use hwml_support::FromWithDb;

    // Create Vec constructor
    let vec_id = ConstantId::from_with_db(db, "Vec");

    // Create Nat type
    let nat_id = ConstantId::from_with_db(db, "Nat");
    let nat = Rc::new(Value::constant(nat_id));

    // Create a variable for n
    let n_ty = Rc::new(Value::constant(nat_id));
    let n = Rc::new(Value::variable(n_ty.clone(), Level::new(0)));

    // Create Vec Nat n
    let vec1 = Rc::new(Value::type_constructor(
        vec_id,
        vec![nat.clone(), n.clone()],
    ));
    let vec2 = Rc::new(Value::type_constructor(vec_id, vec![nat, n]));

    let result = unify(db, &global, &mut mctx, 1, vec1, vec2);
    print_unify_result("Vec Nat n =?= Vec Nat n", result);
}

/// Example 13: Unifying different type constructors (should fail)
///
/// This should fail: Vec Nat ≠ List Nat
pub fn example_unify_different_type_constructors<'db>(db: &'db Database) {
    println!("\n=== Example 13: Unifying Different Type Constructors (should fail) ===");

    let global = empty_global_env();
    let mut mctx = new_meta_context();

    use hwml_core::syn::ConstantId;
    use hwml_support::FromWithDb;

    // Create Vec and List constructors
    let vec_id = ConstantId::from_with_db(db, "Vec");
    let list_id = ConstantId::from_with_db(db, "List");

    // Create Nat type
    let nat_id = ConstantId::from_with_db(db, "Nat");
    let nat = Rc::new(Value::constant(nat_id));

    // Create Vec Nat and List Nat
    let vec_nat = Rc::new(Value::type_constructor(vec_id, vec![nat.clone()]));
    let list_nat = Rc::new(Value::type_constructor(list_id, vec![nat]));

    let result = unify(db, &global, &mut mctx, 0, vec_nat, list_nat);
    print_unify_result("Vec Nat =?= List Nat", result);
}

// ============================================================================
// Data Constructor Unification Examples
// ============================================================================

/// Example 14: Unifying data constructors
///
/// Unifying: Some x =?= Some x
pub fn example_unify_data_constructors<'db>(db: &'db Database) {
    println!("\n=== Example 14: Unifying Data Constructors ===");

    let global = empty_global_env();
    let mut mctx = new_meta_context();

    use hwml_core::syn::ConstantId;
    use hwml_support::FromWithDb;

    // Create Some constructor
    let some_id = ConstantId::from_with_db(db, "Some");

    // Create a variable for x
    let ty = Rc::new(Value::universe(UniverseLevel::new(0)));
    let x = Rc::new(Value::variable(ty, Level::new(0)));

    // Create Some x
    let some1 = Rc::new(Value::data_constructor(some_id, vec![x.clone()]));
    let some2 = Rc::new(Value::data_constructor(some_id, vec![x]));

    let result = unify(db, &global, &mut mctx, 1, some1, some2);
    print_unify_result("Some x =?= Some x", result);
}

/// Example 15: Unifying different data constructors (should fail)
///
/// This should fail: Some x ≠ None
pub fn example_unify_different_data_constructors<'db>(db: &'db Database) {
    println!("\n=== Example 15: Unifying Different Data Constructors (should fail) ===");

    let global = empty_global_env();
    let mut mctx = new_meta_context();

    use hwml_core::syn::ConstantId;
    use hwml_support::FromWithDb;

    // Create Some and None constructors
    let some_id = ConstantId::from_with_db(db, "Some");
    let none_id = ConstantId::from_with_db(db, "None");

    // Create a variable for x
    let ty = Rc::new(Value::universe(UniverseLevel::new(0)));
    let x = Rc::new(Value::variable(ty, Level::new(0)));

    // Create Some x and None
    let some_x = Rc::new(Value::data_constructor(some_id, vec![x]));
    let none = Rc::new(Value::data_constructor(none_id, vec![]));

    let result = unify(db, &global, &mut mctx, 1, some_x, none);
    print_unify_result("Some x =?= None", result);
}

// ============================================================================
// Pattern Unification Examples
// ============================================================================

/// Example 16: Pattern unification with distinct variables
///
/// Solving: ?M x y =?= x
/// Solution: ?M = λa b. a
pub fn example_pattern_unification<'db>(db: &'db Database) {
    println!("\n=== Example 16: Pattern Unification ===");

    let global = empty_global_env();
    let mut mctx = new_meta_context();

    // Create a metavariable ?M
    let meta_id = mctx.fresh_id();

    // Create variables x and y
    let ty = Rc::new(Value::universe(UniverseLevel::new(0)));
    let x = Rc::new(Value::variable(ty.clone(), Level::new(0)));
    let y = Rc::new(Value::variable(ty.clone(), Level::new(1)));

    // Create local environment with x and y
    let mut local = LocalEnv::new();
    local.push(x.clone());
    local.push(y.clone());

    // Create ?M with local environment
    let meta = Rc::new(Value::metavariable(meta_id, local));

    println!("Before unification:");
    println!("  ?M solution: {:?}", mctx.lookup(meta_id));

    // Unify ?M[x, y] =?= x
    // Note: In practice, we'd need to apply the metavariable to x and y
    let result = unify(db, &global, &mut mctx, 2, meta, x);
    print_unify_result("?M[x, y] =?= x", result);

    println!("After unification:");
    println!("  ?M solution: {:?}", mctx.lookup(meta_id));
}

// ============================================================================
// Main Function - Run All Examples
// ============================================================================

fn main() {
    let db = Database::default();

    println!("╔════════════════════════════════════════════════════════════════╗");
    println!("║         HWML Unification API Examples                         ║");
    println!("╚════════════════════════════════════════════════════════════════╝");

    // Basic unification examples
    example_unify_universes(&db);
    example_unify_different_universes(&db);
    example_unify_rigid_variables(&db);
    example_unify_different_variables(&db);

    // Lambda unification examples
    example_unify_lambdas(&db);
    example_unify_eta_expansion(&db);

    // Pi type unification examples
    example_unify_pi_types(&db);
    example_unify_pi_different_sources(&db);

    // Metavariable examples
    example_create_metavariables(&db);
    example_unify_meta_with_universe(&db);
    // Note: Skipping flex-flex example as it triggers unimplemented eval code
    // example_unify_two_metavariables(&db);

    // Type constructor examples
    example_unify_type_constructors(&db);
    example_unify_different_type_constructors(&db);

    // Data constructor examples
    example_unify_data_constructors(&db);
    example_unify_different_data_constructors(&db);

    // Pattern unification examples
    example_pattern_unification(&db);

    println!("\n╔════════════════════════════════════════════════════════════════╗");
    println!("║         All Examples Completed                                 ║");
    println!("╚════════════════════════════════════════════════════════════════╝");
}
