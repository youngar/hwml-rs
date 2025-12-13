//! Examples demonstrating the use of `eval` and `quote` functions.
//!
//! This module contains practical examples showing how to:
//! - Evaluate syntax terms to semantic values
//! - Quote semantic values back to syntax
//! - Work with different term types (lambdas, applications, universes, etc.)

use hwml_core::common::{Level, UniverseLevel};
use hwml_core::eval;
use hwml_core::quote;
use hwml_core::syn::parse::parse_syntax;
use hwml_core::syn::print::dump_syntax;
use hwml_core::syn::{ConstantId, RcSyntax, Syntax};
use hwml_core::val::{
    Closure, DataConstructorInfo, Environment, GlobalEnv, LocalEnv, TypeConstructor,
    TypeConstructorInfo, Value,
};
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
fn empty_env<'db>() -> (GlobalEnv<'db>, Environment<'db>) {
    let global = GlobalEnv::new();
    let local = LocalEnv::new();
    let env = Environment {
        global: global.clone(),
        local,
    };
    (global, env)
}

/// Create an environment with Bool type and True/False data constructors.
fn bool_env<'db>(db: &'db Database) -> (GlobalEnv<'db>, Environment<'db>) {
    let mut global = GlobalEnv::new();

    // Register Bool type constructor with type Type₀
    let bool_id = ConstantId::from_str(db, "Bool");
    let bool_type_info = TypeConstructorInfo::new(
        vec![].into(),         // no arguments (0 parameters, 0 indices)
        0,                     // num_parameters
        UniverseLevel::new(0), // lives in Type₀
    );
    println!("Bool type_info: {:?}", bool_type_info);
    global.add_type_constructor(bool_id, bool_type_info);

    // Register True data constructor with type Bool
    let true_id = ConstantId::from_str(db, "True");
    let bool_type_syn = Syntax::type_constructor_rc(bool_id, vec![]);
    let true_data_info = DataConstructorInfo::new(
        vec![].into(), // no arguments
        bool_type_syn.clone(),
    );
    println!("True data_info: {:?}", true_data_info);
    global.add_data_constructor(true_id, true_data_info);

    // Register False data constructor with type Bool
    let false_id = ConstantId::from_str(db, "False");
    let false_data_info = DataConstructorInfo::new(
        vec![].into(), // no arguments
        bool_type_syn.clone(),
    );
    println!("False data_info: {:?}", false_data_info);
    global.add_data_constructor(false_id, false_data_info);

    let env = Environment {
        global: global.clone(),
        local: LocalEnv::new(),
    };
    (global, env)
}

/// Create an environment with Nat type and zero/succ data constructors.
fn nat_env<'db>(db: &'db Database) -> (GlobalEnv<'db>, Environment<'db>) {
    let mut global = GlobalEnv::new();

    // Register Nat type constructor: #[@Nat] : 𝒰0
    let nat_id = ConstantId::from_str(db, "Nat");
    let nat_type_info = TypeConstructorInfo::new(
        vec![].into(),         // no arguments (0 parameters, 0 indices)
        0,                     // num_parameters
        UniverseLevel::new(0), // lives in Type₀
    );
    println!("Nat type_info: {:?}", nat_type_info);
    global.add_type_constructor(nat_id, nat_type_info);

    // The Nat type constructor syntax (for use in data constructor types)
    let nat_type_syn = Syntax::type_constructor_rc(nat_id, vec![]);

    // Register zero data constructor: [@zero] : #[@Nat]
    let zero_id = ConstantId::from_str(db, "zero");
    let zero_data_info = DataConstructorInfo::new(
        vec![].into(), // no arguments
        nat_type_syn.clone(),
    );
    println!("zero data_info: {:?}", zero_data_info);
    global.add_data_constructor(zero_id, zero_data_info);

    // Register succ data constructor: [@succ %0] : Nat → Nat
    // Succ has one argument (the predecessor of type Nat)
    let succ_id = ConstantId::from_str(db, "succ");
    let succ_data_info = DataConstructorInfo::new(
        vec![Syntax::type_constructor_rc(nat_id, vec![])].into(), // one argument of type Nat
        nat_type_syn.clone(),
    );
    println!("succ data_info: {:?}", succ_data_info);
    global.add_data_constructor(succ_id, succ_data_info);

    let env = Environment {
        global: global.clone(),
        local: LocalEnv::new(),
    };
    (global, env)
}

/// Create an environment with Option type and Some/None data constructors.
/// Option is parameterized by a type: Option : 𝒰0 → 𝒰0
/// None : ∀ (t : 𝒰0) → Option t
/// Some : ∀ (t : 𝒰0) → t → Option t
fn option_env<'db>(db: &'db Database) -> (GlobalEnv<'db>, Environment<'db>) {
    let mut global = GlobalEnv::new();

    // Register Option type constructor: #[@Option] : 𝒰0 → 𝒰0
    // Option has one parameter (the element type)
    let option_id = ConstantId::from_str(db, "Option");

    // Option type: ∀ (%0 : 𝒰0) → 𝒰0
    let option_type_info = TypeConstructorInfo::new(
        vec![Syntax::universe_rc(UniverseLevel::new(0))].into(), // one argument: parameter (Type₀)
        1,                     // num_parameters (1 parameter, 0 indices)
        UniverseLevel::new(0), // lives in Type₀
    );
    println!("Option type_info: {:?}", option_type_info);
    global.add_type_constructor(option_id, option_type_info);

    // Register None data constructor: [@None] : Option %0
    // None has no arguments (the type parameter is implicit from the type constructor)
    let none_id = ConstantId::from_str(db, "None");
    // The result type is Option applied to the parameter (variable 0)
    let none_result_type_syn = Syntax::type_constructor_rc(
        option_id,
        vec![Syntax::variable_rc(hwml_core::common::Index(0))],
    );
    let none_data_info = DataConstructorInfo::new(
        vec![].into(), // no arguments
        none_result_type_syn,
    );
    println!("None data_info: {:?}", none_data_info);
    global.add_data_constructor(none_id, none_data_info);

    // Register Some data constructor: [@Some] : t → Option t
    // Some has one argument (the value of type t, where t is the type parameter)
    let some_id = ConstantId::from_str(db, "Some");
    // The argument type is the type parameter (variable 0)
    // The result type is Option applied to the parameter (variable 0, but now at index 1 after binding the argument)
    let some_result_type_syn = Syntax::type_constructor_rc(
        option_id,
        vec![Syntax::variable_rc(hwml_core::common::Index(1))],
    );
    let some_data_info = DataConstructorInfo::new(
        vec![Syntax::variable_rc(hwml_core::common::Index(0))].into(), // one argument of type %0 (the type parameter)
        some_result_type_syn,
    );
    println!("Some data_info: {:?}", some_data_info);
    global.add_data_constructor(some_id, some_data_info);

    let env = Environment {
        global: global.clone(),
        local: LocalEnv::new(),
    };
    (global, env)
}

/// Create an environment with Vec type (indexed by length) and nil/cons data constructors.
/// Vec : ∀ (A : 𝒰0) (n : Nat) → 𝒰0
/// nil : ∀ (A : 𝒰0) → Vec A zero
/// cons : ∀ (A : 𝒰0) (n : Nat) (x : A) (xs : Vec A n) → Vec A (succ n)
fn vec_env<'db>(db: &'db Database) -> (GlobalEnv<'db>, Environment<'db>) {
    let mut global = GlobalEnv::new();

    // First, register Bool type (for vector elements)
    let bool_id = ConstantId::from_str(db, "Bool");
    let bool_type_info = TypeConstructorInfo::new(
        vec![].into(),         // no arguments (0 parameters, 0 indices)
        0,                     // num_parameters
        UniverseLevel::new(0), // lives in Type₀
    );
    println!("Bool type_info: {:?}", bool_type_info);
    global.add_type_constructor(bool_id, bool_type_info);

    // Register True data constructor
    let true_id = ConstantId::from_str(db, "True");
    let bool_type_syn = Syntax::type_constructor_rc(bool_id, vec![]);
    let true_data_info = DataConstructorInfo::new(
        vec![].into(), // no arguments
        bool_type_syn.clone(),
    );
    println!("True data_info: {:?}", true_data_info);
    global.add_data_constructor(true_id, true_data_info);

    // Register False data constructor
    let false_id = ConstantId::from_str(db, "False");
    let false_data_info = DataConstructorInfo::new(
        vec![].into(), // no arguments
        bool_type_syn.clone(),
    );
    println!("False data_info: {:?}", false_data_info);
    global.add_data_constructor(false_id, false_data_info);

    // Register Nat type (needed for the index)
    let nat_id = ConstantId::from_str(db, "Nat");
    let nat_type_info = TypeConstructorInfo::new(
        vec![].into(),         // no arguments (0 parameters, 0 indices)
        0,                     // num_parameters
        UniverseLevel::new(0), // lives in Type₀
    );
    println!("Nat type_info: {:?}", nat_type_info);
    global.add_type_constructor(nat_id, nat_type_info);

    let nat_type_syn = Syntax::type_constructor_rc(nat_id, vec![]);

    // Register zero data constructor
    let zero_id = ConstantId::from_str(db, "zero");
    let zero_data_info = DataConstructorInfo::new(
        vec![].into(), // no arguments
        nat_type_syn.clone(),
    );
    println!("zero data_info: {:?}", zero_data_info);
    global.add_data_constructor(zero_id, zero_data_info);

    // Register succ data constructor
    let succ_id = ConstantId::from_str(db, "succ");
    let succ_data_info = DataConstructorInfo::new(
        vec![Syntax::type_constructor_rc(nat_id, vec![])].into(), // one argument of type Nat
        nat_type_syn.clone(),
    );
    println!("succ data_info: {:?}", succ_data_info);
    global.add_data_constructor(succ_id, succ_data_info);

    // Register Vec type constructor: Vec : 𝒰0 → Nat → 𝒰0
    // Vec has one parameter (element type A) and one index (length n)
    let vec_id = ConstantId::from_str(db, "Vec");
    let vec_type_info = TypeConstructorInfo::new(
        vec![
            Syntax::universe_rc(UniverseLevel::new(0)), // parameter: Type₀ (element type)
            Syntax::type_constructor_rc(nat_id, vec![]), // index: Nat (length)
        ]
        .into(),
        1,                     // num_parameters (1 parameter, 1 index)
        UniverseLevel::new(0), // lives in Type₀
    );
    println!("Vec type_info: {:?}", vec_type_info);
    global.add_type_constructor(vec_id, vec_type_info);

    // Register nil data constructor: nil : ∀ (A : 𝒰0) → Vec A zero
    // nil has no arguments (the type parameter A is implicit)
    // The result type is Vec A zero
    let nil_id = ConstantId::from_str(db, "nil");
    let nil_result_type_syn = Syntax::type_constructor_rc(
        vec_id,
        vec![
            // Parameter: A (variable at index 0)
            Syntax::variable_rc(hwml_core::common::Index(0)),
            // Index: zero
            Syntax::data_constructor_rc(zero_id, vec![]),
        ],
    );
    let nil_data_info = DataConstructorInfo::new(
        vec![].into(), // no arguments
        nil_result_type_syn,
    );
    println!("nil data_info: {:?}", nil_data_info);
    global.add_data_constructor(nil_id, nil_data_info);

    // Register cons data constructor: cons : ∀ (A : 𝒰0) {n : Nat} (x : A) (xs : Vec A n) → Vec A (succ n)
    // cons has three arguments under the parameters:
    //   - n : Nat (implicit, the length of the tail)
    //   - x : A (the head element)
    //   - xs : Vec A n (the tail vector)
    // The result type is Vec A (succ n)
    // Note: n is an implicit argument that must be provided explicitly in the syntax
    let cons_id = ConstantId::from_str(db, "cons");

    // Build the result type: Vec A (succ n)
    // where A is at index 3 (the parameter) and n is at index 2 (first argument)
    let cons_result_type_syn = Syntax::type_constructor_rc(
        vec_id,
        vec![
            // Parameter: A (variable at index 3)
            Syntax::variable_rc(hwml_core::common::Index(3)),
            // Index: succ n (where n is at index 2)
            Syntax::data_constructor_rc(
                succ_id,
                vec![Syntax::variable_rc(hwml_core::common::Index(2))],
            ),
        ],
    );

    let cons_data_info = DataConstructorInfo::new(
        vec![
            Syntax::type_constructor_rc(nat_id, vec![]), // n : Nat (implicit)
            Syntax::variable_rc(hwml_core::common::Index(1)), // x : A (A is at index 1, the parameter)
            // xs : Vec A n (where A is at index 2 and n is at index 0)
            Syntax::type_constructor_rc(
                vec_id,
                vec![
                    Syntax::variable_rc(hwml_core::common::Index(2)), // A (parameter)
                    Syntax::variable_rc(hwml_core::common::Index(0)), // n (index)
                ],
            ),
        ]
        .into(),
        cons_result_type_syn,
    );
    println!("cons data_info: {:?}", cons_data_info);
    global.add_data_constructor(cons_id, cons_data_info);

    let env = Environment {
        global: global.clone(),
        local: LocalEnv::new(),
    };
    (global, env)
}

/// Evaluate syntax and print the result.
fn eval_and_print<'db>(
    env: &mut Environment<'db>,
    syntax: &RcSyntax<'db>,
) -> Result<Rc<Value<'db>>, String> {
    let value = eval::eval(env, syntax).map_err(|e| format!("Eval error: {:?}", e))?;
    println!("Evaluated to: {:?}", value);
    Ok(value)
}

/// Print a type value.
fn print_type<'db>(
    db: &'db Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    ty: &Rc<Value<'db>>,
) -> Result<(), String> {
    let quoted_type = quote::quote_type(db, global, depth, ty)
        .map_err(|e| format!("Quote type error: {:?}", e))?;
    print!("Type: ");
    dump_syntax(db, &quoted_type);
    Ok(())
}

/// Quote a type value and print the result.
fn quote_type_and_print<'db>(
    db: &'db Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Rc<Value<'db>>,
) -> Result<RcSyntax<'db>, String> {
    let quoted =
        quote::quote_type(db, global, depth, value).map_err(|e| format!("Quote error: {:?}", e))?;
    println!("Quoted back: {:?}", quoted);
    print!("Quoted (printed): ");
    dump_syntax(db, &quoted);
    Ok(quoted)
}

/// Quote a value with a given type and print the result.
fn quote_and_print<'db>(
    db: &'db Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    ty: &Rc<Value<'db>>,
    value: &Rc<Value<'db>>,
) -> Result<RcSyntax<'db>, String> {
    // Print the type
    let quoted_type = quote::quote_type(db, global, depth, ty)
        .map_err(|e| format!("Quote type error: {:?}", e))?;
    print!("Type: ");
    dump_syntax(db, &quoted_type);

    let quoted =
        quote::quote(db, global, depth, ty, value).map_err(|e| format!("Quote error: {:?}", e))?;
    println!("Quoted back: {:?}", quoted);
    print!("Quoted (printed): ");
    dump_syntax(db, &quoted);
    Ok(quoted)
}

// ============================================================================
// Examples
// ============================================================================

/// Example 1: Evaluating and quoting a simple universe
///
/// This example shows how to evaluate `Type₀` and quote it back.
pub fn example_universe<'db>(db: &'db Database) -> Result<(), String> {
    println!("\n=== Example 1: Universe ===");

    let syntax = parse_and_print(db, "𝒰0")?;
    let (global, mut env) = empty_env();

    // Type of 𝒰0 is 𝒰1
    let ty = Rc::new(Value::universe(UniverseLevel::new(1)));
    print_type(db, &global, 0, &ty)?;

    let value = eval_and_print(&mut env, &syntax)?;
    quote_type_and_print(db, &global, 0, &value)?;

    Ok(())
}

/// Example 2: Evaluating and quoting a lambda expression
///
/// This example shows how to evaluate `λx. x` (identity function) and quote it back.
pub fn example_lambda<'db>(db: &'db Database) -> Result<(), String> {
    println!("\n=== Example 2: Lambda (Identity Function) ===");

    let syntax = parse_and_print(db, "λ %x → %x")?;
    let (global, mut env) = empty_env();
    let value = eval_and_print(&mut env, &syntax)?;

    // To quote a lambda, we need its type (a Pi type: Type₀ → Type₀)
    let universe = Rc::new(Value::universe(UniverseLevel::new(0)));
    let pi_target_closure =
        Closure::new(LocalEnv::new(), Syntax::universe_rc(UniverseLevel::new(0)));
    let pi_type = Rc::new(Value::pi(universe, pi_target_closure));

    quote_and_print(db, &global, 0, &pi_type, &value)?;

    Ok(())
}

/// Example 3: Evaluating an application
///
/// This example shows how to evaluate `(λx. x) y` where y is a free variable.
pub fn example_application<'db>(db: &'db Database) -> Result<(), String> {
    println!("\n=== Example 3: Application ===");

    let syntax = parse_and_print(db, "(λ %x → %x) !0")?;

    // Create environment with one variable
    let global = GlobalEnv::new();
    let universe = Rc::new(Value::universe(UniverseLevel::new(0)));
    let var_value = Rc::new(Value::variable(universe.clone(), Level::new(0)));
    let mut local = LocalEnv::new();
    local.push(var_value);
    let mut env = Environment {
        global: global.clone(),
        local,
    };

    // Type of the application is 𝒰0 (the type of the free variable)
    print_type(db, &global, 1, &universe)?;

    let value = eval_and_print(&mut env, &syntax)?;
    quote_type_and_print(db, &global, 1, &value)?;

    Ok(())
}

/// Example 4: Evaluating a constant
///
/// This example shows how to evaluate a named constant.
/// Note: Without a definition, we can't determine the type, so we skip type printing.
pub fn example_constant<'db>(db: &'db Database) -> Result<(), String> {
    println!("\n=== Example 4: Constant ===");

    let syntax = parse_and_print(db, "@myConst")?;
    println!("Type: (unknown - constant not defined in environment)");
    let (_global, mut env) = empty_env();
    eval_and_print(&mut env, &syntax)?;

    Ok(())
}

/// Example 5: Evaluating a Pi type
///
/// This example shows how to evaluate and quote a dependent function type.
pub fn example_pi_type<'db>(db: &'db Database) -> Result<(), String> {
    println!("\n=== Example 5: Pi Type ===");

    let syntax = parse_and_print(db, "∀ (%0 : 𝒰0) → 𝒰0")?;
    let (global, mut env) = empty_env();

    // Type of a Pi type is a universe (𝒰1 since it contains 𝒰0)
    let ty = Rc::new(Value::universe(UniverseLevel::new(1)));
    print_type(db, &global, 0, &ty)?;

    let value = eval_and_print(&mut env, &syntax)?;
    quote_type_and_print(db, &global, 0, &value)?;

    Ok(())
}

/// Example 6: Working with data constructors
///
/// This example shows how to evaluate a data constructor with arguments.
pub fn example_data_constructor<'db>(db: &'db Database) -> Result<(), String> {
    println!("\n=== Example 6: Data Constructor ===");

    let syntax = parse_and_print(db, "[@Pair [@True] [@False]]")?;

    // Create environment with Bool and Pair data constructors
    let (mut global, mut env) = bool_env(db);

    let pair_id = ConstantId::from_str(db, "Pair");
    let pair_type_id = ConstantId::from_str(db, "PairType");
    let bool_id = ConstantId::from_str(db, "Bool");

    // Register PairType type constructor with type Type₀
    let pair_type_info = TypeConstructorInfo::new(
        vec![].into(),         // no arguments (0 parameters, 0 indices)
        0,                     // num_parameters
        UniverseLevel::new(0), // lives in Type₀
    );
    println!("PairType type_info: {:?}", pair_type_info);
    global.add_type_constructor(pair_type_id, pair_type_info);

    // Pair has two arguments (both of type Bool)
    let pair_result_type_syn = Syntax::type_constructor_rc(pair_type_id, vec![]);
    let pair_data_info = DataConstructorInfo::new(
        vec![
            Syntax::type_constructor_rc(bool_id, vec![]), // first argument of type Bool
            Syntax::type_constructor_rc(bool_id, vec![]), // second argument of type Bool
        ]
        .into(),
        pair_result_type_syn.clone(),
    );
    println!("Pair data_info: {:?}", pair_data_info);
    global.add_data_constructor(pair_id, pair_data_info);

    // Update env with the new global
    env.global = global.clone();

    let value = eval_and_print(&mut env, &syntax)?;

    // To quote the data constructor, we need its result type (PairType)
    let pair_result_type = Rc::new(Value::type_constructor(pair_type_id, vec![]));
    quote_and_print(db, &global, 0, &pair_result_type, &value)?;

    Ok(())
}

/// Example 7: Application inside lambda (reduces)
///
/// This example shows a lambda containing an application that beta-reduces.
/// λx. (λy. y) x  should normalize to  λx. x
pub fn example_lambda_app_reduces<'db>(db: &'db Database) -> Result<(), String> {
    println!("\n=== Example 7: Application inside Lambda (Reduces) ===");

    let syntax = parse_and_print(db, "λ %x → (λ %y → %y) %x")?;
    let (global, mut env) = empty_env();
    let value = eval_and_print(&mut env, &syntax)?;

    // To quote a lambda, we need its type (Type₀ → Type₀)
    let universe = Rc::new(Value::universe(UniverseLevel::new(0)));
    let pi_target_closure =
        Closure::new(LocalEnv::new(), Syntax::universe_rc(UniverseLevel::new(0)));
    let pi_type = Rc::new(Value::pi(universe, pi_target_closure));

    quote_and_print(db, &global, 0, &pi_type, &value)?;
    println!("Expected: λx. x (the application should reduce)");

    Ok(())
}

/// Example 8: Application inside lambda (doesn't reduce)
///
/// This example shows a lambda containing an application that cannot reduce.
/// λx. λy. x y  should stay as  λx. λy. x y
pub fn example_lambda_app_no_reduce<'db>(db: &'db Database) -> Result<(), String> {
    println!("\n=== Example 8: Application inside Lambda (No Reduction) ===");

    let syntax = parse_and_print(db, "λ %x %y → %x %y")?;

    // Type: (A → B) → A → B for some types A and B
    // We'll use (𝒰0 → 𝒰0) → 𝒰0 → 𝒰0 as a concrete example
    let (global, mut env) = empty_env();
    let universe = Rc::new(Value::universe(UniverseLevel::new(0)));
    let inner_pi = Rc::new(Value::pi(
        universe.clone(),
        Closure::new(LocalEnv::new(), Syntax::universe_rc(UniverseLevel::new(0))),
    ));
    let outer_pi = Rc::new(Value::pi(
        inner_pi.clone(),
        Closure::new(
            LocalEnv::new(),
            Syntax::pi_rc(
                Syntax::universe_rc(UniverseLevel::new(0)),
                Syntax::universe_rc(UniverseLevel::new(0)),
            ),
        ),
    ));
    print_type(db, &global, 0, &outer_pi)?;

    let value = eval_and_print(&mut env, &syntax)?;
    quote_and_print(db, &global, 0, &outer_pi, &value)?;
    println!("Expected: λx. λy. x y (no reduction possible - it's already in normal form)");

    Ok(())
}

/// Example 9: Eta expansion during quotation
///
/// This example shows how quotation performs eta expansion to match the expected type.
/// λx. x  with type (𝒰0 → 𝒰0) → 𝒰0 → 𝒰0  becomes  λx. λy. x y
pub fn example_eta_expansion<'db>(db: &'db Database) -> Result<(), String> {
    println!("\n=== Example 9: Eta Expansion ===");

    let syntax = parse_and_print(db, "λ %x → %x")?;

    // Type: (𝒰0 → 𝒰0) → 𝒰0 → 𝒰0
    // The identity function, but at a higher-order type
    let (global, mut env) = empty_env();
    let universe = Rc::new(Value::universe(UniverseLevel::new(0)));

    // Inner Pi: 𝒰0 → 𝒰0
    let inner_pi = Rc::new(Value::pi(
        universe.clone(),
        Closure::new(LocalEnv::new(), Syntax::universe_rc(UniverseLevel::new(0))),
    ));

    // Outer Pi: (𝒰0 → 𝒰0) → 𝒰0 → 𝒰0
    let outer_pi = Rc::new(Value::pi(
        inner_pi.clone(),
        Closure::new(
            LocalEnv::new(),
            Syntax::pi_rc(
                Syntax::universe_rc(UniverseLevel::new(0)),
                Syntax::universe_rc(UniverseLevel::new(0)),
            ),
        ),
    ));
    print_type(db, &global, 0, &outer_pi)?;

    let value = eval_and_print(&mut env, &syntax)?;
    quote_and_print(db, &global, 0, &outer_pi, &value)?;
    println!("Expected: λx. λy. x y (eta-expanded to match the Pi type)");

    Ok(())
}

/// Example 10: Normalizing a term (eval + quote)
///
/// This example shows the complete normalization process: syntax → value → syntax.
pub fn example_normalization<'db>(db: &'db Database) -> Result<(), String> {
    println!("\n=== Example 10: Normalization ===");

    let syntax = parse_and_print(db, "(λ %x %y → %x) !0 !1")?;

    // Create environment with two variables
    let global = GlobalEnv::new();
    let universe = Rc::new(Value::universe(UniverseLevel::new(0)));
    let var0 = Rc::new(Value::variable(universe.clone(), Level::new(0)));
    let var1 = Rc::new(Value::variable(universe.clone(), Level::new(1)));
    let mut local = LocalEnv::new();
    local.push(var0);
    local.push(var1);
    let mut env = Environment {
        global: global.clone(),
        local,
    };

    // Type of the result is 𝒰0 (the type of the first variable)
    print_type(db, &global, 2, &universe)?;

    let value = eval_and_print(&mut env, &syntax)?;

    // Quote back (normalize)
    let normalized =
        quote::quote_type(db, &global, 2, &value).map_err(|e| format!("Quote error: {:?}", e))?;
    println!("Normalized to: {:?}", normalized);
    print!("Normalized (printed): ");
    dump_syntax(db, &normalized);
    println!("Expected: Variable at index 0 (the first argument)");

    Ok(())
}

/// Example 11: Case expression with neutral scrutinee (doesn't reduce)
///
/// This example shows a case expression inside a lambda where the scrutinee is a variable,
/// so the case expression remains neutral and doesn't reduce.
pub fn example_case_neutral<'db>(db: &'db Database) -> Result<(), String> {
    println!("\n=== Example 11: Case Expression (Neutral - No Reduction) ===");

    let syntax = parse_and_print(db, "λ %x → %x case %0 → 𝒰0 { @True => 𝒰0 | @False => 𝒰0 }")?;

    // Set up environment with Bool type constructor and True/False data constructors
    let (global, mut env) = bool_env(db);
    let bool_id = ConstantId::from_str(db, "Bool");
    let bool_type = Rc::new(Value::type_constructor(bool_id, vec![]));

    let value = eval_and_print(&mut env, &syntax)?;

    // Quote back - should produce a lambda with a case expression inside
    let pi_type = Rc::new(Value::pi(
        bool_type.clone(),
        Closure::new(LocalEnv::new(), Syntax::universe_rc(UniverseLevel::new(0))),
    ));
    quote_and_print(db, &global, 0, &pi_type, &value)?;

    Ok(())
}

/// Example 12: Case expression that reduces
///
/// This example shows a case expression where the scrutinee is a data constructor,
/// so the case expression reduces by selecting the matching branch.
pub fn example_case_reduces<'db>(db: &'db Database) -> Result<(), String> {
    println!("\n=== Example 12: Case Expression (Reduces) ===");

    let syntax = parse_and_print(
        db,
        "[@Pair [@True] [@False]] case %0 → #[@Bool] { @Pair %x %y => %y }",
    )?;

    // Set up environment with Bool and Pair data constructors
    let (mut global, mut env) = bool_env(db);

    let pair_type_id = ConstantId::from_str(db, "PairType");
    let bool_id = ConstantId::from_str(db, "Bool");
    let bool_type = Rc::new(Value::type_constructor(bool_id, vec![]));

    let pair_type_info = TypeConstructorInfo::new(
        vec![].into(),         // no arguments (0 parameters, 0 indices)
        0,                     // num_parameters
        UniverseLevel::new(0), // lives in Type₀
    );
    println!("PairType type_info: {:?}", pair_type_info);
    global.add_type_constructor(pair_type_id, pair_type_info);

    let pair_id = ConstantId::from_str(db, "Pair");
    let pair_result_type_syn = Syntax::type_constructor_rc(pair_type_id, vec![]);
    let pair_data_info = DataConstructorInfo::new(
        vec![
            Syntax::type_constructor_rc(bool_id, vec![]), // first argument of type Bool
            Syntax::type_constructor_rc(bool_id, vec![]), // second argument of type Bool
        ]
        .into(),
        pair_result_type_syn.clone(),
    );
    println!("Pair data_info: {:?}", pair_data_info);
    global.add_data_constructor(pair_id, pair_data_info);

    // Update env with the new global
    env.global = global.clone();

    let value = eval_and_print(&mut env, &syntax)?;

    // The result is a Bool value (False), so we need to quote it with Bool type
    quote_and_print(db, &global, 0, &bool_type, &value)?;

    Ok(())
}

/// Example 13: Natural numbers with pattern matching
/// Demonstrates:
/// - Nat type with zero and succ constructors
/// - Pattern matching on natural numbers
/// - Case expression that reduces to a value
pub fn example_nat_pattern_match<'db>(db: &'db Database) -> Result<(), String> {
    println!("\n=== Example 13: Natural Numbers with Pattern Matching ===");

    // Create environment with Nat type
    let (global, mut env) = nat_env(db);

    // Create a natural number: [@succ [@succ [@zero]]] (represents 2)
    let two = parse_and_print(db, "[@succ [@succ [@zero]]]")?;

    // Evaluate it
    let two_value = eval_and_print(&mut env, &two)?;

    // Get the Nat type for quoting
    let nat_type = Rc::new(Value::TypeConstructor(TypeConstructor {
        constructor: ConstantId::from_str(db, "Nat"),
        arguments: vec![],
    }));

    // Print the type
    print_type(db, &global, 0, &nat_type)?;

    // Quote it back
    quote_and_print(db, &global, 0, &nat_type, &two_value)?;

    // Now create a case expression that pattern matches on a Nat
    // [@succ [@zero]] case %0 → #[@Nat] { @zero => [@zero] | @succ %x => %x }
    // This should reduce to [@zero] (the predecessor of 1)
    println!("\n--- Pattern matching to get predecessor ---");
    let pred_expr = parse_and_print(
        db,
        "[@succ [@zero]] case %0 → #[@Nat] { @zero => [@zero] | @succ %x => %x }",
    )?;

    // Evaluate the case expression
    let pred_value = eval_and_print(&mut env, &pred_expr)?;

    // Print type and quote
    print_type(db, &global, 0, &nat_type)?;
    quote_and_print(db, &global, 0, &nat_type, &pred_value)?;

    Ok(())
}

/// Example 14: Option type with dependent pattern matching
/// Demonstrates:
/// - Option/Maybe type with Some and None constructors
/// - Dependent pattern matching where return type depends on the scrutinee
/// - A function that returns Bool for None, or the contained value for Some
pub fn example_option_unwrap<'db>(db: &'db Database) -> Result<(), String> {
    println!("\n=== Example 14: Option Type with Dependent Pattern Matching ===");

    // We need Option, Nat, and Bool types
    let (mut global, mut env) = option_env(db);

    // Add Nat type to the environment
    let nat_id = ConstantId::from_str(db, "Nat");
    global.add_type_constructor(
        nat_id,
        TypeConstructorInfo::new(
            vec![].into(),         // no arguments (0 parameters, 0 indices)
            0,                     // num_parameters
            UniverseLevel::new(0), // lives in Type₀
        ),
    );

    // The Nat type constructor syntax (for use in data constructor types)
    let nat_type_syn = Syntax::type_constructor_rc(nat_id, vec![]);

    let zero_id = ConstantId::from_str(db, "zero");
    global.add_data_constructor(
        zero_id,
        DataConstructorInfo::new(
            vec![].into(), // no arguments
            nat_type_syn.clone(),
        ),
    );

    let succ_id = ConstantId::from_str(db, "succ");
    global.add_data_constructor(
        succ_id,
        DataConstructorInfo::new(
            vec![Syntax::type_constructor_rc(nat_id, vec![])].into(), // one argument of type Nat
            nat_type_syn.clone(),
        ),
    );

    // Add Bool type to the environment
    let bool_id = ConstantId::from_str(db, "Bool");
    global.add_type_constructor(
        bool_id,
        TypeConstructorInfo::new(
            vec![].into(),         // no arguments (0 parameters, 0 indices)
            0,                     // num_parameters
            UniverseLevel::new(0), // lives in Type₀
        ),
    );

    let bool_type_syn = Syntax::type_constructor_rc(bool_id, vec![]);
    let bool_type = Rc::new(Value::type_constructor(bool_id, vec![]));
    let nat_type = Rc::new(Value::type_constructor(nat_id, vec![]));

    let false_id = ConstantId::from_str(db, "False");
    global.add_data_constructor(
        false_id,
        DataConstructorInfo::new(
            vec![].into(), // no arguments
            bool_type_syn.clone(),
        ),
    );

    env.global = global.clone();

    // Dependent pattern matching with motive:
    // λ %t %x → %x case %0 → (%0 case %1 → 𝒰0 { @None %t => #[@Bool] | @Some %t %y => %t })
    //                      { @None %t => [@False] | @Some %t %y => %y }
    //
    // The motive computes the return type by matching on the scrutinee:
    // - If None, return type is Bool
    // - If Some, return type is the type parameter t

    println!("\n--- Dependent pattern matching: returns Bool for None, value for Some ---");
    let dependent_match = parse_and_print(
        db,
        "λ %t %x → %x case %0 → (%0 case %1 → 𝒰0 { @None %t => #[@Bool] | @Some %t %y => %t }) { @None %t => [@False] | @Some %t %y => %y }",
    )?;

    let dependent_fn = eval_and_print(&mut env, &dependent_match)?;

    // Apply to Some Nat 1
    println!("\n--- Applying to Some(1) ---");
    let some_one = parse_and_print(db, "[@Some #[@Nat] [@succ [@zero]]]")?;
    let some_one_value = eval_and_print(&mut env, &some_one)?;

    // Apply the function to Nat and Some(1)
    // First apply to Nat type
    let partial_app = eval::run_application(&global, &dependent_fn, nat_type.clone())
        .map_err(|e| format!("Apply error: {:?}", e))?;
    // Then apply to Some(1)
    let result_some = eval::run_application(&global, &partial_app, some_one_value)
        .map_err(|e| format!("Apply error: {:?}", e))?;

    println!("Result: {:?}", result_some);
    print_type(db, &global, 0, &nat_type)?;
    quote_and_print(db, &global, 0, &nat_type, &result_some)?;

    // Apply to None Nat
    println!("\n--- Applying to None ---");
    let none_nat = parse_and_print(db, "[@None #[@Nat]]")?;
    let none_value = eval_and_print(&mut env, &none_nat)?;

    // First apply to Nat type
    let partial_app = eval::run_application(&global, &dependent_fn, nat_type.clone())
        .map_err(|e| format!("Apply error: {:?}", e))?;
    // Then apply to None
    let result_none = eval::run_application(&global, &partial_app, none_value)
        .map_err(|e| format!("Apply error: {:?}", e))?;

    println!("Result: {:?}", result_none);
    print_type(db, &global, 0, &bool_type)?;
    quote_and_print(db, &global, 0, &bool_type, &result_none)?;

    Ok(())
}

/// Example 15: Vec - an indexed data type
///
/// This example demonstrates an indexed data type where the type is indexed by a natural number
/// representing the length of the vector.
/// Vec : ∀ (A : 𝒰0) (n : Nat) → 𝒰0
/// nil : ∀ (A : 𝒰0) → Vec A zero
/// cons : ∀ (A : 𝒰0) (n : Nat) (x : A) (xs : Vec A n) → Vec A (succ n)
pub fn example_vec<'db>(db: &'db Database) -> Result<(), String> {
    println!("\n=== Example 15: Vec - Indexed Data Type ===");

    let (global, mut env) = vec_env(db);

    // Get the IDs we need
    let vec_id = ConstantId::from_str(db, "Vec");
    let bool_id = ConstantId::from_str(db, "Bool");
    let nat_id = ConstantId::from_str(db, "Nat");
    let zero_id = ConstantId::from_str(db, "zero");
    let succ_id = ConstantId::from_str(db, "succ");

    let bool_type = Rc::new(Value::type_constructor(bool_id, vec![]));
    let nat_type = Rc::new(Value::type_constructor(nat_id, vec![]));

    // Create an empty vector of Bool: [@nil]
    // Note: The type parameter is implicit and inferred from the type
    println!("\n--- Creating empty vector of Bool ---");
    let nil_bool = parse_and_print(db, "[@nil]")?;
    let nil_value = eval_and_print(&mut env, &nil_bool)?;

    // The type is Vec Bool zero
    let vec_bool_zero_type = Rc::new(Value::type_constructor(
        vec_id,
        vec![
            bool_type.clone(),
            Rc::new(Value::data_constructor(zero_id, vec![])),
        ],
    ));
    print_type(db, &global, 0, &vec_bool_zero_type)?;
    quote_and_print(db, &global, 0, &vec_bool_zero_type, &nil_value)?;

    // Create a vector with one element: [@cons [@zero] [@True] [@nil]]
    // Note: The type parameter Bool is implicit and inferred from the type
    // This is cons 0 True nil, which has type Vec Bool (succ zero) = Vec Bool 1
    println!("\n--- Creating vector [True] of type Vec Bool 1 ---");
    let vec_one = parse_and_print(db, "[@cons [@zero] [@True] [@nil]]")?;
    let vec_one_value = eval_and_print(&mut env, &vec_one)?;

    // The type is Vec Bool (succ zero)
    let vec_bool_one_type = Rc::new(Value::type_constructor(
        vec_id,
        vec![
            bool_type.clone(),
            Rc::new(Value::data_constructor(
                succ_id,
                vec![Rc::new(Value::data_constructor(zero_id, vec![]))],
            )),
        ],
    ));
    print_type(db, &global, 0, &vec_bool_one_type)?;
    quote_and_print(db, &global, 0, &vec_bool_one_type, &vec_one_value)?;

    // Create a vector with two elements: [@cons [@succ [@zero]] [@False] [@cons [@zero] [@True] [@nil]]]
    // Note: The type parameter Bool is implicit and inferred from the type
    // This is cons 1 False (cons 0 True nil), which has type Vec Bool (succ (succ zero)) = Vec Bool 2
    println!("\n--- Creating vector [True, False] of type Vec Bool 2 ---");
    let vec_two = parse_and_print(
        db,
        "[@cons [@succ [@zero]] [@False] [@cons [@zero] [@True] [@nil]]]",
    )?;
    let vec_two_value = eval_and_print(&mut env, &vec_two)?;

    // The type is Vec Bool (succ (succ zero))
    let vec_bool_two_type = Rc::new(Value::type_constructor(
        vec_id,
        vec![
            bool_type.clone(),
            Rc::new(Value::data_constructor(
                succ_id,
                vec![Rc::new(Value::data_constructor(
                    succ_id,
                    vec![Rc::new(Value::data_constructor(zero_id, vec![]))],
                ))],
            )),
        ],
    ));
    print_type(db, &global, 0, &vec_bool_two_type)?;
    quote_and_print(db, &global, 0, &vec_bool_two_type, &vec_two_value)?;

    // Pattern match on a vector to get its head element
    // We'll match on the vector [True] to extract the head
    // [@cons [@zero] [@True] [@nil]] case %0 → #[@Bool] { @nil => [@False] | @cons %n %x %xs => %x }
    // This should reduce to [@True] (the head element)
    println!("\n--- Pattern matching to extract head element ---");
    let head_expr = parse_and_print(
        db,
        "[@cons [@zero] [@True] [@nil]] case %0 → #[@Bool] { @nil => [@False] | @cons %n %x %xs => %x }",
    )?;

    let head_value = eval_and_print(&mut env, &head_expr)?;

    // The result should be True (the head element)
    print_type(db, &global, 0, &bool_type)?;
    quote_and_print(db, &global, 0, &bool_type, &head_value)?;

    // Pattern match on a vector to get its tail
    // [@cons [@succ [@zero]] [@False] [@cons [@zero] [@True] [@nil]]]
    //   case %0 → %0 case %1 → 𝒰0 { @nil => #[@Vec #[@Bool] [@zero]] | @cons %n %x %xs => #[@Vec #[@Bool] %n] }
    //        { @nil => [@nil] | @cons %n %x %xs => %xs }
    // The motive pattern matches on the scrutinee to compute the result type:
    //   - For nil: Vec Bool 0 (impossible case, but we need a type)
    //   - For cons n x xs: Vec Bool n (the tail has length n)
    // This extracts the tail of the vector [True, False], which should be [True]
    println!("\n--- Pattern matching to extract tail ---");
    let tail_expr = parse_and_print(
        db,
        "[@cons [@succ [@zero]] [@False] [@cons [@zero] [@True] [@nil]]] case %0 → %0 case %1 → 𝒰0 { @nil => #[@Vec #[@Bool] [@zero]] | @cons %n %x %xs => #[@Vec #[@Bool] %n] } { @nil => [@nil] | @cons %n %x %xs => %xs }",
    )?;

    let tail_value = eval_and_print(&mut env, &tail_expr)?;

    // The result should be a vector [True] of type Vec Bool 1
    // But we need to compute the type from the motive
    // The motive is: case %1 → #[@Nat] { @nil => [@zero] | @cons %n %x %xs => %n }
    // When applied to the scrutinee (the vector [True, False]), this should give us the length of the tail
    // The scrutinee has type Vec Bool 2, so the tail has length 1
    print_type(db, &global, 0, &vec_bool_one_type)?;
    quote_and_print(db, &global, 0, &vec_bool_one_type, &tail_value)?;

    // Demonstrate a length function using pattern matching
    // length : ∀ (A : Type) (n : Nat) → Vec A n → Nat
    // length v = v case _ → Nat { nil => zero | cons n x xs => succ n }
    // Note: We can extract the length from the cons pattern since n is the length of the tail
    println!("\n--- Computing length via pattern matching ---");

    // Apply length to the vector [True, False]
    // (λ %v → %v case %0 → #[@Nat] { @nil => [@zero] | @cons %n %x %xs => [@succ %n] }) [@cons [@succ [@zero]] [@False] [@cons [@zero] [@True] [@nil]]]
    let length_expr = parse_and_print(
        db,
        "(λ %v → %v case %0 → #[@Nat] { @nil => [@zero] | @cons %n %x %xs => [@succ %n] }) [@cons [@succ [@zero]] [@False] [@cons [@zero] [@True] [@nil]]]",
    )?;

    let length_value = eval_and_print(&mut env, &length_expr)?;

    // The result should be succ (succ zero) = 2
    print_type(db, &global, 0, &nat_type)?;
    quote_and_print(db, &global, 0, &nat_type, &length_value)?;

    // Create a polymorphic tail function: λ %t %n %v → %v case ...
    // Type: ∀(t : 𝒰0) (n : Nat) (v : Vec t (succ n)) → Vec t n
    // The function takes:
    //   - t: the element type (will be !2 inside the lambda body)
    //   - n: the length of the tail (will be !1 inside the lambda body)
    //   - v: the vector to extract the tail from (will be !0 inside the lambda body)
    // The motive computes the result type based on the scrutinee:
    //   - For cons m x xs: Vec t m (the tail has length m)
    //   - For nil: Vec t 0 (absurd case, but we need a type)
    // Using !N notation for unbound variables to refer to outer lambda parameters
    println!("\n--- Polymorphic tail function ---");
    let tail_fn = parse_and_print(
        db,
        "λ %t %n %v → %v case %0 → %0 case %1 → 𝒰0 { @nil => #[@Vec !5 [@zero]] | @cons %m %x %xs => #[@Vec !8 %m] } { @nil => [@nil] | @cons %m %x %xs => %xs }",
    )?;
    let _tail_fn_value = eval_and_print(&mut env, &tail_fn)?;

    // The type of the tail function is:
    // ∀(t : 𝒰0) (n : Nat) (v : Vec t (succ n)) → Vec t n
    // For now, let's just print that we created it
    println!("Created polymorphic tail function");

    // Apply the tail function to Bool, 1, and the vector [True, False]
    // This should give us [True]
    println!("\n--- Applying tail function to [True, False] ---");
    let tail_app = parse_and_print(
        db,
        "(λ %t %n %v → %v case %0 → %0 case %1 → 𝒰0 { @nil => #[@Vec !5 [@zero]] | @cons %m %x %xs => #[@Vec !8 %m] } { @nil => [@nil] | @cons %m %x %xs => %xs }) #[@Bool] [@succ [@zero]] [@cons [@succ [@zero]] [@False] [@cons [@zero] [@True] [@nil]]]",
    )?;
    let tail_app_value = eval_and_print(&mut env, &tail_app)?;
    print_type(db, &global, 0, &vec_bool_one_type)?;
    quote_and_print(db, &global, 0, &vec_bool_one_type, &tail_app_value)?;

    println!("\n--- TYPEEEEEEEEEEEEEEEEEEEEEEEEEEEEEE   --");
    env.local = LocalEnv::new();
    let ty = parse_and_print(db, "∀ (%0 : #[@Nat]) → ∀ (%1 : #[@Nat]) → #[@Nat]")?;
    let ety = eval_and_print(&mut env, &ty)?;
    println!("\n--- PARSEEEE--");
    let syntax = parse_and_print(
        db,
        "(λ %x → (λ %y %z → %y) (%x case %0 → #[@Nat] { @zero => [@zero] | @succ %n => %n }))",
    )?;
    println!("\n--- EBALLLLLLLLLL         --");
    let eval = eval_and_print(&mut env, &syntax)?;
    println!("\n--- BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB--");
    quote_and_print(db, &global, 0, &ety, &eval)?;

    Ok(())
}

/// Run all examples
pub fn run_all_examples() {
    let db = Database::new();

    println!("Running eval and quote examples...\n");

    let _ = example_universe(&db);
    let _ = example_lambda(&db);
    let _ = example_application(&db);
    let _ = example_constant(&db);
    let _ = example_pi_type(&db);
    let _ = example_data_constructor(&db);
    let _ = example_lambda_app_reduces(&db);
    let _ = example_lambda_app_no_reduce(&db);
    let _ = example_eta_expansion(&db);
    let _ = example_normalization(&db);
    let _ = example_case_neutral(&db);
    let _ = example_case_reduces(&db);
    let _ = example_nat_pattern_match(&db);
    let _ = example_option_unwrap(&db);
    let _ = example_vec(&db);

    println!("\n=== All examples completed ===");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper function to run an example and assert it succeeds.
    /// Prints any error messages before asserting.
    fn run_example_test<F>(example_fn: F)
    where
        F: FnOnce(&Database) -> Result<(), String>,
    {
        let db = Database::new();
        let result = example_fn(&db);
        if let Err(e) = &result {
            eprintln!("Error: {}", e);
        }
        assert!(result.is_ok());
    }

    #[test]
    fn test_universe_example() {
        run_example_test(example_universe);
    }

    #[test]
    fn test_lambda_example() {
        run_example_test(example_lambda);
    }

    #[test]
    fn test_application_example() {
        run_example_test(example_application);
    }

    #[test]
    fn test_constant_example() {
        run_example_test(example_constant);
    }

    #[test]
    fn test_pi_type_example() {
        run_example_test(example_pi_type);
    }

    #[test]
    fn test_data_constructor_example() {
        run_example_test(example_data_constructor);
    }

    #[test]
    fn test_lambda_app_reduces_example() {
        run_example_test(example_lambda_app_reduces);
    }

    #[test]
    fn test_lambda_app_no_reduce_example() {
        run_example_test(example_lambda_app_no_reduce);
    }

    #[test]
    fn test_eta_expansion_example() {
        run_example_test(example_eta_expansion);
    }

    #[test]
    fn test_normalization_example() {
        run_example_test(example_normalization);
    }

    #[test]
    fn test_case_neutral_example() {
        run_example_test(example_case_neutral);
    }

    #[test]
    fn test_case_reduces_example() {
        run_example_test(example_case_reduces);
    }

    #[test]
    fn test_nat_pattern_match_example() {
        run_example_test(example_nat_pattern_match);
    }

    #[test]
    fn test_option_unwrap_example() {
        run_example_test(example_option_unwrap);
    }

    #[test]
    fn test_vec_example() {
        run_example_test(example_vec);
    }

    #[test]
    fn test_run_all() {
        run_all_examples();
    }
}
