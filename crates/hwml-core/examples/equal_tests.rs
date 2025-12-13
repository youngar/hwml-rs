//! Tests for conversion checking (Convertible trait).
//!
//! This module contains comprehensive tests for the `Convertible` trait,
//! primarily using the `Normal` data structure to test all conversion cases.

#[cfg(test)]
mod tests {
    use crate::common::{Level, UniverseLevel};
    use crate::equal::Convertible;
    use crate::syn::{ConstantId, Syntax};
    use crate::val::{
        Closure, DataConstructorInfo, GlobalEnv, LocalEnv, Normal, TypeConstructorInfo, Universe,
        Value,
    };
    use crate::Database;
    use std::rc::Rc;

    // ============================================================================
    // Helper Functions
    // ============================================================================

    /// Create an empty global environment.
    fn empty_global<'db>() -> GlobalEnv<'db> {
        GlobalEnv::new()
    }

    /// Create a simple Bool environment for testing.
    fn bool_env<'db>(db: &'db Database) -> GlobalEnv<'db> {
        let mut global = GlobalEnv::new();

        // Register Bool type constructor
        let bool_id = ConstantId::from_str(db, "Bool");
        let bool_type_info = TypeConstructorInfo::new(
            vec![].into(),         // no arguments
            0,                     // num_parameters
            UniverseLevel::new(0), // lives in Type₀
        );
        global.add_type_constructor(bool_id, bool_type_info);

        let bool_type = Rc::new(Value::type_constructor(bool_id, vec![]));

        // Register True data constructor
        let true_id = ConstantId::from_str(db, "True");
        let true_data_info = DataConstructorInfo::new(vec![].into(), bool_type.clone());
        global.add_data_constructor(true_id, true_data_info);

        // Register False data constructor
        let false_id = ConstantId::from_str(db, "False");
        let false_data_info = DataConstructorInfo::new(vec![].into(), bool_type.clone());
        global.add_data_constructor(false_id, false_data_info);

        global
    }

    /// Create a Nat environment for testing.
    fn nat_env<'db>(db: &'db Database) -> GlobalEnv<'db> {
        let mut global = GlobalEnv::new();

        // Register Nat type constructor
        let nat_id = ConstantId::from_str(db, "Nat");
        let nat_type_info = TypeConstructorInfo::new(
            vec![].into(),         // no arguments
            0,                     // num_parameters
            UniverseLevel::new(0), // lives in Type₀
        );
        global.add_type_constructor(nat_id, nat_type_info);

        let nat_type = Rc::new(Value::type_constructor(nat_id, vec![]));

        // Register zero data constructor
        let zero_id = ConstantId::from_str(db, "zero");
        let zero_data_info = DataConstructorInfo::new(vec![].into(), nat_type.clone());
        global.add_data_constructor(zero_id, zero_data_info);

        // Register succ data constructor
        let succ_id = ConstantId::from_str(db, "succ");
        let succ_data_info = DataConstructorInfo::new(
            vec![Syntax::type_constructor_rc(nat_id, vec![])].into(),
            nat_type.clone(),
        );
        global.add_data_constructor(succ_id, succ_data_info);

        global
    }

    // ============================================================================
    // Tests for Level Convertibility
    // ============================================================================

    #[test]
    fn test_level_convertible_same() {
        let global = empty_global();
        let level1 = Level::new(5);
        let level2 = Level::new(5);

        assert!(level1.is_convertible(&global, 0, &level2).is_ok());
    }

    #[test]
    fn test_level_not_convertible_different() {
        let global = empty_global();
        let level1 = Level::new(5);
        let level2 = Level::new(7);

        assert!(level1.is_convertible(&global, 0, &level2).is_err());
    }

    // ============================================================================
    // Tests for Universe Convertibility
    // ============================================================================

    #[test]
    fn test_universe_convertible_same_level() {
        let global = empty_global();
        let u1 = Universe::new(UniverseLevel::new(0));
        let u2 = Universe::new(UniverseLevel::new(0));

        assert!(u1.is_convertible(&global, 0, &u2).is_ok());
    }

    #[test]
    fn test_universe_not_convertible_different_level() {
        let global = empty_global();
        let u1 = Universe::new(UniverseLevel::new(0));
        let u2 = Universe::new(UniverseLevel::new(1));

        assert!(u1.is_convertible(&global, 0, &u2).is_err());
    }

    // ============================================================================
    // Tests for Normal Convertibility - Universe Case
    // ============================================================================

    #[test]
    fn test_normal_universe_convertible() {
        let global = empty_global();

        // Create two Normal values with Universe types
        let universe_type = Rc::new(Value::universe(UniverseLevel::new(1)));
        let universe_val = Rc::new(Value::universe(UniverseLevel::new(0)));

        let nf1 = Normal::new(universe_type.clone(), universe_val.clone());
        let nf2 = Normal::new(universe_type.clone(), universe_val.clone());

        assert!(nf1.is_convertible(&global, 0, &nf2).is_ok());
    }

    #[test]
    fn test_normal_universe_not_convertible() {
        let global = empty_global();

        // Create two Normal values with Universe types but different values
        let universe_type = Rc::new(Value::universe(UniverseLevel::new(1)));
        let universe_val1 = Rc::new(Value::universe(UniverseLevel::new(0)));
        let universe_val2 = Rc::new(Value::universe(UniverseLevel::new(1)));

        let nf1 = Normal::new(universe_type.clone(), universe_val1);
        let nf2 = Normal::new(universe_type.clone(), universe_val2);

        assert!(nf1.is_convertible(&global, 0, &nf2).is_err());
    }

    // ============================================================================
    // Tests for Normal Convertibility - TypeConstructor Case
    // ============================================================================

    #[test]
    fn test_normal_type_constructor_convertible_same_data_constructor() {
        let db = Database::default();
        let global = bool_env(&db);

        let bool_id = ConstantId::from_str(&db, "Bool");
        let true_id = ConstantId::from_str(&db, "True");

        // Create type: Bool
        let bool_type = Rc::new(Value::type_constructor(bool_id, vec![]));

        // Create value: True
        let true_val = Rc::new(Value::data_constructor(true_id, vec![]));

        let nf1 = Normal::new(bool_type.clone(), true_val.clone());
        let nf2 = Normal::new(bool_type.clone(), true_val.clone());

        assert!(nf1.is_convertible(&global, 0, &nf2).is_ok());
    }

    #[test]
    fn test_normal_type_constructor_not_convertible_different_data_constructors() {
        let db = Database::default();
        let global = bool_env(&db);

        let bool_id = ConstantId::from_str(&db, "Bool");
        let true_id = ConstantId::from_str(&db, "True");
        let false_id = ConstantId::from_str(&db, "False");

        // Create type: Bool
        let bool_type = Rc::new(Value::type_constructor(bool_id, vec![]));

        // Create values: True and False
        let true_val = Rc::new(Value::data_constructor(true_id, vec![]));
        let false_val = Rc::new(Value::data_constructor(false_id, vec![]));

        let nf1 = Normal::new(bool_type.clone(), true_val);
        let nf2 = Normal::new(bool_type.clone(), false_val);

        assert!(nf1.is_convertible(&global, 0, &nf2).is_err());
    }

    #[test]
    fn test_normal_type_constructor_convertible_with_arguments() {
        let db = Database::default();
        let global = nat_env(&db);

        let nat_id = ConstantId::from_str(&db, "Nat");
        let zero_id = ConstantId::from_str(&db, "zero");
        let succ_id = ConstantId::from_str(&db, "succ");

        // Create type: Nat
        let nat_type = Rc::new(Value::type_constructor(nat_id, vec![]));

        // Create value: zero
        let zero_val = Rc::new(Value::data_constructor(zero_id, vec![]));

        // Create value: succ zero (both instances)
        let succ_zero1 = Rc::new(Value::data_constructor(succ_id, vec![zero_val.clone()]));
        let succ_zero2 = Rc::new(Value::data_constructor(succ_id, vec![zero_val.clone()]));

        let nf1 = Normal::new(nat_type.clone(), succ_zero1);
        let nf2 = Normal::new(nat_type.clone(), succ_zero2);

        assert!(nf1.is_convertible(&global, 0, &nf2).is_ok());
    }

    #[test]
    fn test_normal_type_constructor_not_convertible_different_arguments() {
        let db = Database::default();
        let global = nat_env(&db);

        let nat_id = ConstantId::from_str(&db, "Nat");
        let zero_id = ConstantId::from_str(&db, "zero");
        let succ_id = ConstantId::from_str(&db, "succ");

        // Create type: Nat
        let nat_type = Rc::new(Value::type_constructor(nat_id, vec![]));

        // Create values: zero
        let zero_val = Rc::new(Value::data_constructor(zero_id, vec![]));

        // Create value: succ zero
        let succ_zero = Rc::new(Value::data_constructor(succ_id, vec![zero_val.clone()]));

        // Create value: succ (succ zero)
        let succ_succ_zero = Rc::new(Value::data_constructor(succ_id, vec![succ_zero.clone()]));

        let nf1 = Normal::new(nat_type.clone(), succ_zero);
        let nf2 = Normal::new(nat_type.clone(), succ_succ_zero);

        assert!(nf1.is_convertible(&global, 0, &nf2).is_err());
    }

    // ============================================================================
    // Tests for Normal Convertibility - Neutral Case
    // ============================================================================

    #[test]
    fn test_normal_neutral_variable_convertible() {
        let global = empty_global();

        // Create a neutral type (universe)
        let universe_type = Rc::new(Value::universe(UniverseLevel::new(1)));

        // Create neutral values (variables at the same level)
        let var_type = Rc::new(Value::universe(UniverseLevel::new(0)));
        let var1 = Rc::new(Value::variable(var_type.clone(), Level::new(5)));
        let var2 = Rc::new(Value::variable(var_type.clone(), Level::new(5)));

        let nf1 = Normal::new(universe_type.clone(), var1);
        let nf2 = Normal::new(universe_type.clone(), var2);

        assert!(nf1.is_convertible(&global, 0, &nf2).is_ok());
    }

    #[test]
    fn test_normal_neutral_variable_not_convertible() {
        let global = empty_global();

        // Create a neutral type (universe)
        let universe_type = Rc::new(Value::universe(UniverseLevel::new(1)));

        // Create neutral values (variables at different levels)
        let var_type = Rc::new(Value::universe(UniverseLevel::new(0)));
        let var1 = Rc::new(Value::variable(var_type.clone(), Level::new(5)));
        let var2 = Rc::new(Value::variable(var_type.clone(), Level::new(7)));

        let nf1 = Normal::new(universe_type.clone(), var1);
        let nf2 = Normal::new(universe_type.clone(), var2);

        assert!(nf1.is_convertible(&global, 0, &nf2).is_err());
    }

    // ============================================================================
    // Tests for Normal Convertibility - Mismatched Types
    // ============================================================================

    #[test]
    fn test_normal_mismatched_types_not_convertible() {
        let global = empty_global();

        // Create a Normal with Universe type
        let universe_type = Rc::new(Value::universe(UniverseLevel::new(1)));
        let universe_val = Rc::new(Value::universe(UniverseLevel::new(0)));
        let nf1 = Normal::new(universe_type.clone(), universe_val);

        // Create a Normal with Variable (Neutral) type
        let var_type = Rc::new(Value::universe(UniverseLevel::new(0)));
        let var_val = Rc::new(Value::variable(var_type.clone(), Level::new(5)));
        let neutral_type = Rc::new(Value::neutral(
            universe_type.clone(),
            Rc::new(crate::val::Neutral::variable(Level::new(3))),
        ));
        let nf2 = Normal::new(neutral_type, var_val);

        // These should not be convertible because their types don't match
        assert!(nf1.is_convertible(&global, 0, &nf2).is_err());
    }

    // ============================================================================
    // Tests for TypeConstructor Convertibility
    // ============================================================================

    #[test]
    fn test_type_constructor_convertible_same() {
        let db = Database::default();
        let global = bool_env(&db);

        let bool_id = ConstantId::from_str(&db, "Bool");
        let tc1 = crate::val::TypeConstructor::new(bool_id, vec![]);
        let tc2 = crate::val::TypeConstructor::new(bool_id, vec![]);

        assert!(tc1.is_convertible(&global, 0, &tc2).is_ok());
    }

    #[test]
    fn test_type_constructor_not_convertible_different() {
        let db = Database::default();
        let mut global = bool_env(&db);

        // Add Nat type as well
        let nat_id = ConstantId::from_str(&db, "Nat");
        let nat_type_info = TypeConstructorInfo::new(vec![].into(), 0, UniverseLevel::new(0));
        global.add_type_constructor(nat_id, nat_type_info);

        let bool_id = ConstantId::from_str(&db, "Bool");
        let tc1 = crate::val::TypeConstructor::new(bool_id, vec![]);
        let tc2 = crate::val::TypeConstructor::new(nat_id, vec![]);

        assert!(tc1.is_convertible(&global, 0, &tc2).is_err());
    }

    // ============================================================================
    // Tests for Neutral Convertibility - Application
    // ============================================================================

    #[test]
    fn test_neutral_application_convertible() {
        let global = empty_global();

        // Create a function type: Type₀ → Type₀
        let universe0 = Rc::new(Value::universe(UniverseLevel::new(0)));

        // Create a neutral function (variable)
        let func_neutral = Rc::new(crate::val::Neutral::variable(Level::new(0)));

        // Create an argument
        let arg_val = Rc::new(Value::universe(UniverseLevel::new(0)));
        let arg_normal1 = Normal::new(universe0.clone(), arg_val.clone());
        let arg_normal2 = Normal::new(universe0.clone(), arg_val.clone());

        // Create applications
        let app1 = crate::val::Application::new(func_neutral.clone(), arg_normal1);
        let app2 = crate::val::Application::new(func_neutral.clone(), arg_normal2);

        assert!(app1.is_convertible(&global, 0, &app2).is_ok());
    }

    #[test]
    fn test_neutral_application_not_convertible_different_args() {
        let global = empty_global();

        // Create a function type: Type₀ → Type₀
        let universe0 = Rc::new(Value::universe(UniverseLevel::new(0)));

        // Create a neutral function (variable)
        let func_neutral = Rc::new(crate::val::Neutral::variable(Level::new(0)));

        // Create different arguments
        let arg_val1 = Rc::new(Value::universe(UniverseLevel::new(0)));
        let arg_val2 = Rc::new(Value::universe(UniverseLevel::new(1)));
        let arg_normal1 = Normal::new(universe0.clone(), arg_val1);
        let arg_normal2 = Normal::new(universe0.clone(), arg_val2);

        // Create applications
        let app1 = crate::val::Application::new(func_neutral.clone(), arg_normal1);
        let app2 = crate::val::Application::new(func_neutral.clone(), arg_normal2);

        assert!(app1.is_convertible(&global, 0, &app2).is_err());
    }

    #[test]
    fn test_neutral_application_not_convertible_different_functions() {
        let global = empty_global();

        // Create a function type: Type₀ → Type₀
        let universe0 = Rc::new(Value::universe(UniverseLevel::new(0)));

        // Create different neutral functions (variables)
        let func_neutral1 = Rc::new(crate::val::Neutral::variable(Level::new(0)));
        let func_neutral2 = Rc::new(crate::val::Neutral::variable(Level::new(1)));

        // Create an argument
        let arg_val = Rc::new(Value::universe(UniverseLevel::new(0)));
        let arg_normal1 = Normal::new(universe0.clone(), arg_val.clone());
        let arg_normal2 = Normal::new(universe0.clone(), arg_val.clone());

        // Create applications
        let app1 = crate::val::Application::new(func_neutral1, arg_normal1);
        let app2 = crate::val::Application::new(func_neutral2, arg_normal2);

        assert!(app1.is_convertible(&global, 0, &app2).is_err());
    }

    // ============================================================================
    // Tests for Neutral Convertibility - Mixed Types
    // ============================================================================

    #[test]
    fn test_neutral_variable_vs_application_not_convertible() {
        let global = empty_global();

        let var_neutral = crate::val::Neutral::variable(Level::new(0));

        let universe0 = Rc::new(Value::universe(UniverseLevel::new(0)));
        let func_neutral = Rc::new(crate::val::Neutral::variable(Level::new(1)));
        let arg_val = Rc::new(Value::universe(UniverseLevel::new(0)));
        let arg_normal = Normal::new(universe0.clone(), arg_val);
        let app_neutral = crate::val::Neutral::Application(crate::val::Application::new(
            func_neutral,
            arg_normal,
        ));

        assert!(var_neutral
            .is_convertible(&global, 0, &app_neutral)
            .is_err());
    }

    // ============================================================================
    // Tests for Data Constructor Convertibility
    // ============================================================================

    #[test]
    fn test_data_constructor_convertible_no_args() {
        let db = Database::default();
        let global = bool_env(&db);

        let bool_id = ConstantId::from_str(&db, "Bool");
        let true_id = ConstantId::from_str(&db, "True");

        let bool_type = crate::val::TypeConstructor::new(bool_id, vec![]);
        let true_dc1 = crate::val::DataConstructor::new(true_id, vec![]);
        let true_dc2 = crate::val::DataConstructor::new(true_id, vec![]);

        // Use the helper function from equal.rs
        let result = crate::equal::is_type_constructor_instance_convertible(
            &global,
            0,
            bool_type.clone(),
            &Value::DataConstructor(true_dc1),
            &Value::DataConstructor(true_dc2),
        );

        assert!(result.is_ok());
    }

    #[test]
    fn test_data_constructor_not_convertible_different_constructors() {
        let db = Database::default();
        let global = bool_env(&db);

        let bool_id = ConstantId::from_str(&db, "Bool");
        let true_id = ConstantId::from_str(&db, "True");
        let false_id = ConstantId::from_str(&db, "False");

        let bool_type = crate::val::TypeConstructor::new(bool_id, vec![]);
        let true_dc = crate::val::DataConstructor::new(true_id, vec![]);
        let false_dc = crate::val::DataConstructor::new(false_id, vec![]);

        let result = crate::equal::is_type_constructor_instance_convertible(
            &global,
            0,
            bool_type.clone(),
            &Value::DataConstructor(true_dc),
            &Value::DataConstructor(false_dc),
        );

        assert!(result.is_err());
    }

    #[test]
    fn test_data_constructor_convertible_with_args() {
        let db = Database::default();
        let global = nat_env(&db);

        let nat_id = ConstantId::from_str(&db, "Nat");
        let zero_id = ConstantId::from_str(&db, "zero");
        let succ_id = ConstantId::from_str(&db, "succ");

        let nat_type = crate::val::TypeConstructor::new(nat_id, vec![]);
        let zero_val = Rc::new(Value::data_constructor(zero_id, vec![]));

        let succ_dc1 = crate::val::DataConstructor::new(succ_id, vec![zero_val.clone()]);
        let succ_dc2 = crate::val::DataConstructor::new(succ_id, vec![zero_val.clone()]);

        let result = crate::equal::is_type_constructor_instance_convertible(
            &global,
            0,
            nat_type.clone(),
            &Value::DataConstructor(succ_dc1),
            &Value::DataConstructor(succ_dc2),
        );

        assert!(result.is_ok());
    }

    #[test]
    fn test_data_constructor_not_convertible_different_args() {
        let db = Database::default();
        let global = nat_env(&db);

        let nat_id = ConstantId::from_str(&db, "Nat");
        let zero_id = ConstantId::from_str(&db, "zero");
        let succ_id = ConstantId::from_str(&db, "succ");

        let nat_type = crate::val::TypeConstructor::new(nat_id, vec![]);
        let zero_val = Rc::new(Value::data_constructor(zero_id, vec![]));
        let succ_zero = Rc::new(Value::data_constructor(succ_id, vec![zero_val.clone()]));

        let succ_dc1 = crate::val::DataConstructor::new(succ_id, vec![zero_val.clone()]);
        let succ_dc2 = crate::val::DataConstructor::new(succ_id, vec![succ_zero.clone()]);

        let result = crate::equal::is_type_constructor_instance_convertible(
            &global,
            0,
            nat_type.clone(),
            &Value::DataConstructor(succ_dc1),
            &Value::DataConstructor(succ_dc2),
        );

        assert!(result.is_err());
    }

    // ============================================================================
    // Tests for Case Convertibility
    // ============================================================================

    #[test]
    fn test_case_convertible_same_branches() {
        let db = Database::default();
        let global = bool_env(&db);

        let bool_id = ConstantId::from_str(&db, "Bool");
        let true_id = ConstantId::from_str(&db, "True");
        let false_id = ConstantId::from_str(&db, "False");

        // Create a scrutinee (neutral variable of type Bool)
        let scrutinee = Rc::new(crate::val::Neutral::variable(Level::new(0)));

        // Create a motive (return type) - a closure that returns Type₀
        let universe0_syntax = Syntax::universe_rc(UniverseLevel::new(0));
        let motive = Closure::new(LocalEnv::new(), universe0_syntax.clone());

        // Create branch bodies (both return Type₀) - closures with no arguments
        let true_body = Closure::new(LocalEnv::new(), universe0_syntax.clone());
        let false_body = Closure::new(LocalEnv::new(), universe0_syntax.clone());

        // Create branches
        let branches = vec![
            crate::val::CaseBranch {
                constructor: true_id,
                arity: 0,
                body: true_body.clone(),
            },
            crate::val::CaseBranch {
                constructor: false_id,
                arity: 0,
                body: false_body.clone(),
            },
        ];

        let case1 = crate::val::Case::new(
            scrutinee.clone(),
            bool_id,
            vec![], // Bool has no parameters
            motive.clone(),
            branches.clone(),
        );
        let case2 = crate::val::Case::new(
            scrutinee.clone(),
            bool_id,
            vec![], // Bool has no parameters
            motive.clone(),
            branches.clone(),
        );

        assert!(case1.is_convertible(&global, 0, &case2).is_ok());
    }

    #[test]
    fn test_case_not_convertible_different_scrutinee() {
        let db = Database::default();
        let global = bool_env(&db);

        let bool_id = ConstantId::from_str(&db, "Bool");
        let true_id = ConstantId::from_str(&db, "True");
        let false_id = ConstantId::from_str(&db, "False");

        // Create different scrutinees
        let scrutinee1 = Rc::new(crate::val::Neutral::variable(Level::new(0)));
        let scrutinee2 = Rc::new(crate::val::Neutral::variable(Level::new(1)));

        // Create a motive (return type) - a closure that returns Type₀
        let universe0_syntax = Syntax::universe_rc(UniverseLevel::new(0));
        let motive = Closure::new(LocalEnv::new(), universe0_syntax.clone());

        // Create branch bodies (both return Type₀) - closures with no arguments
        let true_body = Closure::new(LocalEnv::new(), universe0_syntax.clone());
        let false_body = Closure::new(LocalEnv::new(), universe0_syntax.clone());

        // Create branches
        let branches = vec![
            crate::val::CaseBranch {
                constructor: true_id,
                arity: 0,
                body: true_body.clone(),
            },
            crate::val::CaseBranch {
                constructor: false_id,
                arity: 0,
                body: false_body.clone(),
            },
        ];

        let case1 = crate::val::Case::new(
            scrutinee1,
            bool_id,
            vec![], // Bool has no parameters
            motive.clone(),
            branches.clone(),
        );
        let case2 = crate::val::Case::new(
            scrutinee2,
            bool_id,
            vec![], // Bool has no parameters
            motive.clone(),
            branches.clone(),
        );

        assert!(case1.is_convertible(&global, 0, &case2).is_err());
    }

    #[test]
    fn test_case_not_convertible_different_branch_count() {
        let db = Database::default();
        let global = bool_env(&db);

        let bool_id = ConstantId::from_str(&db, "Bool");
        let true_id = ConstantId::from_str(&db, "True");
        let false_id = ConstantId::from_str(&db, "False");

        let scrutinee = Rc::new(crate::val::Neutral::variable(Level::new(0)));

        // Create a motive (return type) - a closure that returns Type₀
        let universe0_syntax = Syntax::universe_rc(UniverseLevel::new(0));
        let motive = Closure::new(LocalEnv::new(), universe0_syntax.clone());

        // Create branch bodies (both return Type₀) - closures with no arguments
        let true_body = Closure::new(LocalEnv::new(), universe0_syntax.clone());
        let false_body = Closure::new(LocalEnv::new(), universe0_syntax.clone());

        // Case 1 has both branches
        let branches1 = vec![
            crate::val::CaseBranch {
                constructor: true_id,
                arity: 0,
                body: true_body.clone(),
            },
            crate::val::CaseBranch {
                constructor: false_id,
                arity: 0,
                body: false_body.clone(),
            },
        ];

        // Case 2 has only one branch
        let branches2 = vec![crate::val::CaseBranch {
            constructor: true_id,
            arity: 0,
            body: true_body.clone(),
        }];

        let case1 = crate::val::Case::new(
            scrutinee.clone(),
            bool_id,
            vec![], // Bool has no parameters
            motive.clone(),
            branches1,
        );
        let case2 = crate::val::Case::new(
            scrutinee.clone(),
            bool_id,
            vec![], // Bool has no parameters
            motive.clone(),
            branches2,
        );

        assert!(case1.is_convertible(&global, 0, &case2).is_err());
    }
}

fn main() {
    println!(
        "This is a test file. Run with `cargo test --example equal_tests` to execute the tests."
    );
}
