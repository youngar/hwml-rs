//! Pattern unification for dependent pattern matching.

use crate::{
    common::{Level, MetaVariableId},
    equal, eval,
    val::{DataConstructorInfo, Environment, GlobalEnv, LocalEnv, TypeConstructorInfo},
    ConstantId, Value,
};
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct PatternBinding<'db> {
    pub name: Option<String>,
    pub ty: Rc<Value<'db>>,
}

#[derive(Debug, Clone)]
pub struct PatternUnifyResult<'db> {
    pub new_bindings: Vec<PatternBinding<'db>>,
    pub solutions: Vec<(Level, Rc<Value<'db>>)>,
}

#[derive(Debug, Clone)]
pub enum PatternUnifyOutcome<'db> {
    Success(PatternUnifyResult<'db>),
    Conflict,
    Stuck(MetaVariableId),
}

#[derive(Debug, Clone)]
pub enum Error<'db> {
    EvalError(eval::Error),
    EqualError(equal::Error<'db>),
    LookupError(crate::val::LookupError<'db>),
    Internal(String),
}

impl<'db> From<eval::Error> for Error<'db> {
    fn from(err: eval::Error) -> Self {
        Error::EvalError(err)
    }
}

impl<'db> From<equal::Error<'db>> for Error<'db> {
    fn from(err: equal::Error<'db>) -> Self {
        Error::EqualError(err)
    }
}

impl<'db> From<crate::val::LookupError<'db>> for Error<'db> {
    fn from(err: crate::val::LookupError<'db>) -> Self {
        Error::LookupError(err)
    }
}

impl<'db> std::fmt::Display for Error<'db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::EvalError(e) => write!(f, "evaluation error during pattern unification: {e:?}"),
            Error::EqualError(_) => write!(f, "equality check failed during pattern unification"),
            Error::LookupError(e) => write!(f, "lookup error during pattern unification: {e:?}"),
            Error::Internal(msg) => write!(f, "internal error in pattern unification: {msg}"),
        }
    }
}

impl<'db> std::error::Error for Error<'db> {}

/// Unify a pattern against a scrutinee type.
///
/// # Arguments
/// * `global` - The global environment for lookups
/// * `tcon_info` - The type constructor info (e.g., Vec)
/// * `tcon_args` - The type constructor arguments (e.g., [A, n] for Vec A n)
/// * `dcon_name` - The data constructor name (e.g., "cons")
/// * `dcon_info` - The data constructor info
/// * `base_depth` - The current context depth before adding new bindings
///
/// # Returns
/// * `Ok(PatternUnifyOutcome)` - Success, Conflict, or Stuck
/// * `Err(Error)` - An unexpected error occurred
pub fn unify_pattern<'db>(
    global: &GlobalEnv<'db>,
    tcon_info: &TypeConstructorInfo<'db>,
    tcon_args: &[Rc<Value<'db>>],
    _dcon_name: ConstantId<'db>,
    dcon_info: &DataConstructorInfo<'db>,
    base_depth: usize,
) -> Result<PatternUnifyOutcome<'db>, Error<'db>> {
    // Phase 1: Rigid Telescopic Walk
    // For each argument in the constructor's telescope, create a fresh rigid variable.
    let num_parameters = tcon_info.num_parameters();
    let parameters: Vec<_> = tcon_args.iter().take(num_parameters).cloned().collect();

    // Create environment starting with parameters
    let mut local = LocalEnv::new();
    local.extend(parameters.iter().cloned());

    let mut new_bindings = Vec::new();
    let mut current_depth = base_depth;

    for ty_syntax in dcon_info.arguments.iter() {
        let mut env = Environment {
            global,
            local: local.clone(),
        };
        let ty = eval::eval(&mut env, ty_syntax)?;
        let rigid_var = Rc::new(Value::variable(Level::new(current_depth), ty.clone()));
        new_bindings.push(PatternBinding { name: None, ty });
        local.push(rigid_var);
        current_depth += 1;
    }

    let mut env = Environment { global, local };
    let constructor_return_ty = eval::eval(&mut env, &dcon_info.ty)?;

    let scrutinee_indices: Vec<_> = tcon_args.iter().skip(num_parameters).cloned().collect();

    let constructor_indices = match constructor_return_ty.as_ref() {
        Value::TypeConstructor(tcon) => tcon
            .arguments
            .iter()
            .skip(num_parameters)
            .cloned()
            .collect::<Vec<_>>(),
        _ => {
            return Err(Error::Internal(
                "Constructor return type is not a TypeConstructor".into(),
            ));
        }
    };

    let mut param_env = Environment {
        global,
        local: LocalEnv::new(),
    };
    param_env.extend(parameters.iter().cloned());

    let index_types: Result<Vec<_>, _> = tcon_info
        .indices()
        .iter()
        .map(|ty_syntax| eval::eval(&mut param_env, ty_syntax))
        .collect();
    let index_types = index_types?;

    let equations: Vec<(Rc<Value<'db>>, Rc<Value<'db>>, Rc<Value<'db>>)> = scrutinee_indices
        .into_iter()
        .zip(constructor_indices.into_iter())
        .zip(index_types.into_iter())
        .map(|((lhs, rhs), ty)| (lhs, rhs, ty))
        .collect();

    let unify_depth = base_depth + new_bindings.len();
    match unify_equations(global, unify_depth, &equations)? {
        EquationOutcome::Success(solutions) => {
            Ok(PatternUnifyOutcome::Success(PatternUnifyResult {
                new_bindings,
                solutions,
            }))
        }
        EquationOutcome::Conflict => Ok(PatternUnifyOutcome::Conflict),
        EquationOutcome::Stuck(meta) => Ok(PatternUnifyOutcome::Stuck(meta)),
    }
}

#[derive(Debug)]
enum EquationOutcome<'db> {
    Success(Vec<(Level, Rc<Value<'db>>)>),
    Conflict,
    Stuck(MetaVariableId),
}

fn occurs_check(level: Level, value: &Value<'_>) -> bool {
    match value {
        Value::Rigid(rigid) => {
            if rigid.head.level == level {
                return true;
            }
            rigid.spine.iter().any(|elim| match elim {
                crate::val::Eliminator::Application(app) => {
                    occurs_check(level, &app.argument.value)
                }
                crate::val::Eliminator::Case(_) => false,
            })
        }
        Value::Flex(flex) => flex.spine.iter().any(|elim| match elim {
            crate::val::Eliminator::Application(app) => occurs_check(level, &app.argument.value),
            crate::val::Eliminator::Case(_) => false,
        }),
        Value::DataConstructor(dcon) => dcon.arguments.iter().any(|arg| occurs_check(level, arg)),
        Value::TypeConstructor(tcon) => tcon.arguments.iter().any(|arg| occurs_check(level, arg)),
        Value::Pi(pi) => occurs_check(level, &pi.source),
        Value::Lambda(_) => false,
        Value::EqType(eq) => {
            occurs_check(level, &eq.ty)
                || occurs_check(level, &eq.lhs)
                || occurs_check(level, &eq.rhs)
        }
        Value::Transport(transport) => {
            occurs_check(level, &transport.proof) || occurs_check(level, &transport.value)
        }
        Value::Universe(_)
        | Value::Lift(_)
        | Value::Bit(_)
        | Value::Zero(_)
        | Value::One(_)
        | Value::Refl(_)
        | Value::HardwareUniverse(_)
        | Value::SignalUniverse(_)
        | Value::HArrow(_)
        | Value::Module(_)
        | Value::HApplication(_)
        | Value::SLift(_)
        | Value::MLift(_)
        | Value::ModuleUniverse(_)
        | Value::Prim(_)
        | Value::Constant(_) => false,
    }
}

fn unify_equations<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    equations: &[(Rc<Value<'db>>, Rc<Value<'db>>, Rc<Value<'db>>)],
) -> Result<EquationOutcome<'db>, Error<'db>> {
    let mut solutions: Vec<(Level, Rc<Value<'db>>)> = Vec::new();
    let mut work_list: Vec<(Rc<Value<'db>>, Rc<Value<'db>>, Rc<Value<'db>>)> = equations.to_vec();

    while let Some((lhs, rhs, ty)) = work_list.pop() {
        if equal::equate(global, depth, &lhs, &rhs, &ty).is_ok() {
            continue;
        }

        match (lhs.as_ref(), rhs.as_ref(), ty.as_ref()) {
            (Value::Flex(flex), _, _) | (_, Value::Flex(flex), _) => {
                return Ok(EquationOutcome::Stuck(flex.head.id));
            }

            (Value::Rigid(rigid), _, _) if rigid.spine.is_empty() => {
                let level = rigid.head.level;
                if occurs_check(level, rhs.as_ref()) {
                    return Ok(EquationOutcome::Conflict);
                }
                solutions.push((level, rhs.clone()));
            }

            (_, Value::Rigid(rigid), _) if rigid.spine.is_empty() => {
                let level = rigid.head.level;
                if occurs_check(level, lhs.as_ref()) {
                    return Ok(EquationOutcome::Conflict);
                }
                solutions.push((level, lhs.clone()));
            }

            (Value::Lambda(l1), Value::Lambda(l2), Value::Pi(pi)) => {
                let var = Rc::new(Value::variable(Level::new(depth), pi.source.clone()));
                let l1_body = eval::run_closure(global, &l1.body, [var.clone()])?;
                let l2_body = eval::run_closure(global, &l2.body, [var.clone()])?;
                let result_ty = eval::run_closure(global, &pi.target, [var])?;
                work_list.push((l1_body, l2_body, result_ty));
            }

            (Value::Lambda(l1), _, Value::Pi(pi)) => {
                let var = Rc::new(Value::variable(Level::new(depth), pi.source.clone()));
                let l1_body = eval::run_closure(global, &l1.body, [var.clone()])?;
                let rhs_applied = eval::run_application(global, &rhs, var.clone())?;
                let result_ty = eval::run_closure(global, &pi.target, [var])?;
                work_list.push((l1_body, rhs_applied, result_ty));
            }

            (_, Value::Lambda(l2), Value::Pi(pi)) => {
                let var = Rc::new(Value::variable(Level::new(depth), pi.source.clone()));
                let lhs_applied = eval::run_application(global, &lhs, var.clone())?;
                let l2_body = eval::run_closure(global, &l2.body, [var.clone()])?;
                let result_ty = eval::run_closure(global, &pi.target, [var])?;
                work_list.push((lhs_applied, l2_body, result_ty));
            }

            // Rule: Injectivity - same data constructor on both sides at TypeConstructor type
            (
                Value::DataConstructor(lhs_dcon),
                Value::DataConstructor(rhs_dcon),
                Value::TypeConstructor(tcon),
            ) => {
                if lhs_dcon.constructor == rhs_dcon.constructor {
                    // Same constructor - unify arguments pairwise
                    // We need to get the types of the arguments from the data constructor info
                    let data_info = global
                        .data_constructor(lhs_dcon.constructor)
                        .map_err(|e| Error::LookupError(e))?
                        .clone();

                    let type_info = global
                        .type_constructor(tcon.constructor)
                        .map_err(|e| Error::LookupError(e))?
                        .clone();

                    let num_parameters = type_info.num_parameters();
                    let parameters = tcon.iter().take(num_parameters).cloned();

                    // Create an environment for evaluating argument types
                    let mut env = Environment {
                        global,
                        local: LocalEnv::new(),
                    };
                    env.extend(parameters);

                    // Evaluate the type of each argument and add equations
                    for (l, r, ty_syntax) in itertools::izip!(
                        lhs_dcon.arguments.iter(),
                        rhs_dcon.arguments.iter(),
                        data_info.arguments.iter()
                    ) {
                        let arg_ty = eval::eval(&mut env, ty_syntax)?;
                        work_list.push((l.clone(), r.clone(), arg_ty.clone()));
                        // Extend environment with the left argument for dependent types
                        env.push(l.clone());
                    }
                } else {
                    // Different constructors - conflict!
                    return Ok(EquationOutcome::Conflict);
                }
            }

            // Rule: Injectivity - equality types at Universe
            (Value::EqType(eq1), Value::EqType(eq2), Value::Universe(_)) => {
                // Eq A x y ~ Eq B u v  becomes  A ~ B, x ~ u, y ~ v
                // We need to get the type of A (which should be a universe)
                // For simplicity, use U0 as the type for the type argument
                let type_ty = Rc::new(Value::universe(crate::common::UniverseLevel::new(0)));
                work_list.push((eq1.ty.clone(), eq2.ty.clone(), type_ty.clone()));
                // x and y have type A (use eq1.ty as the type)
                work_list.push((eq1.lhs.clone(), eq2.lhs.clone(), eq1.ty.clone()));
                work_list.push((eq1.rhs.clone(), eq2.rhs.clone(), eq1.ty.clone()));
            }

            // Rule: Axiom K - all Refl proofs are equal at EqType
            (Value::Refl(_), Value::Refl(_), Value::EqType(_)) => {
                // refl ~ refl  is always true (Axiom K)
                // Delete this equation
                continue;
            }

            // Rule: Injectivity - Transport at EqType
            (Value::Transport(t1), Value::Transport(t2), _) => {
                // transport P1 h1 v1 ~ transport P2 h2 v2
                // We need to unify the motives, proofs, and values
                // For motives, we need to eta-expand them
                let var = Rc::new(Value::variable(
                    Level::new(depth),
                    Rc::new(Value::universe(crate::common::UniverseLevel::new(0))),
                ));
                let m1_body = eval::run_closure(global, &t1.motive, [var.clone()])?;
                let m2_body = eval::run_closure(global, &t2.motive, [var.clone()])?;
                // The result type of the motive is a universe
                let motive_result_ty =
                    Rc::new(Value::universe(crate::common::UniverseLevel::new(0)));
                work_list.push((m1_body, m2_body, motive_result_ty));

                // Unify proofs - we need to infer their type (should be EqType)
                // For simplicity, use a placeholder type
                let proof_ty = Rc::new(Value::universe(crate::common::UniverseLevel::new(0)));
                work_list.push((t1.proof.clone(), t2.proof.clone(), proof_ty));

                // Unify values - they should have the same type (P x for some x)
                // For simplicity, use a placeholder type
                let value_ty = Rc::new(Value::universe(crate::common::UniverseLevel::new(0)));
                work_list.push((t1.value.clone(), t2.value.clone(), value_ty));
            }

            // No rule applies - this is a conflict
            _ => {
                return Ok(EquationOutcome::Conflict);
            }
        }
    }

    Ok(EquationOutcome::Success(solutions))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::val::GlobalEnv;
    use crate::Database;
    use hwml_support::IntoWithDb;

    use crate::test_utils::{load_prelude, VEC_PRELUDE};

    /// Test helper to create a test database and global environment with Nat and Vec.
    fn setup_nat_vec<'db>(db: &'db Database) -> GlobalEnv<'db> {
        load_prelude(db, VEC_PRELUDE)
    }

    #[test]
    fn test_unify_pattern_vnil_at_zero() {
        // Test: matching @VNil against Vec A @Zero should succeed with no index solutions
        // @VNil : (A : Type) -> Vec A @Zero
        use crate::test_utils::eval_str;

        let db = Database::default();
        let global = setup_nat_vec(&db);

        match unify_pattern(
            &global,
            global.type_constructor("Vec".into_with_db(&db)).unwrap(),
            &vec![
                eval_str(&db, &global, "$Bit"),
                eval_str(&db, &global, "[@Zero]"),
            ],
            "VNil".into_with_db(&db),
            global.data_constructor("VNil".into_with_db(&db)).unwrap(),
            0,
        ) {
            Ok(PatternUnifyOutcome::Success(res)) => {
                assert_eq!(res.new_bindings.len(), 0); // @VNil has no arguments for Vec
                assert_eq!(res.solutions.len(), 0); // Index @Zero ~ @Zero deleted by Axiom K
            }
            Ok(PatternUnifyOutcome::Conflict) => panic!("Unexpected conflict"),
            Ok(PatternUnifyOutcome::Stuck(meta)) => panic!("Unexpected stuck on {:?}", meta),
            Err(e) => panic!("Unexpected error: {:?}", e),
        }
    }

    #[test]
    fn test_unify_pattern_vnil_at_succ_n_conflicts() {
        // Test: matching @VNil against Vec A (@Succ n) should CONFLICT
        // @VNil produces Vec A @Zero, but scrutinee is Vec A (@Succ n)
        use crate::test_utils::eval_str;

        let db = Database::default();
        let global = setup_nat_vec(&db);

        match unify_pattern(
            &global,
            global.type_constructor("Vec".into_with_db(&db)).unwrap(),
            &vec![
                eval_str(&db, &global, "$Bit"),
                eval_str(&db, &global, "[@Succ [@Zero]]"),
            ],
            "VNil".into_with_db(&db),
            global.data_constructor("VNil".into_with_db(&db)).unwrap(),
            0,
        ) {
            Ok(PatternUnifyOutcome::Conflict) => {} // Expected: @Zero ~ @Succ @Zero
            Ok(PatternUnifyOutcome::Success(_)) => panic!("Expected conflict, got success"),
            Ok(PatternUnifyOutcome::Stuck(meta)) => panic!("Unexpected stuck on {:?}", meta),
            Err(e) => panic!("Unexpected error: {:?}", e),
        }
    }

    #[test]
    fn test_unify_pattern_vcons_at_variable() {
        // Test: matching @VCons against Vec A n where n is a variable
        // @VCons : (m : Nat) -> A -> Vec A m -> Vec A (@Succ m)
        // Expected: n ~ @Succ m, with new bindings for (m, x, xs)
        use crate::test_utils::eval_str_at_depth;

        let db = Database::default();
        let global = setup_nat_vec(&db);

        match unify_pattern(
            &global,
            global.type_constructor("Vec".into_with_db(&db)).unwrap(),
            &vec![
                Rc::new(Value::bit()),
                eval_str_at_depth(&db, &global, "%0", 1),
            ],
            "VCons".into_with_db(&db),
            global.data_constructor("VCons".into_with_db(&db)).unwrap(),
            1,
        ) {
            Ok(PatternUnifyOutcome::Success(res)) => {
                assert_eq!(res.new_bindings.len(), 3); // (m : Nat), (x : A), (xs : Vec A m)
                assert_eq!(res.solutions.len(), 1); // n ~ @Succ m
                assert_eq!(res.solutions[0].0, Level::new(0)); // n is at level 0
                match res.solutions[0].1.as_ref() {
                    Value::DataConstructor(dcon) => {
                        assert_eq!(dcon.constructor.name(&db), "Succ");
                        assert_eq!(dcon.arguments.len(), 1);
                    }
                    other => panic!("Expected @Succ, got {:?}", other),
                }
            }
            Ok(PatternUnifyOutcome::Conflict) => panic!("Unexpected conflict"),
            Ok(PatternUnifyOutcome::Stuck(meta)) => panic!("Unexpected stuck on {:?}", meta),
            Err(e) => panic!("Unexpected error: {:?}", e),
        }
    }

    #[test]
    fn test_occurs_check_cyclic_returns_conflict() {
        // Test: n ~ Succ n should return Conflict (not a valid substitution)
        // This tests the occurs check directly
        use crate::test_utils::{eval_str, eval_str_at_depth};

        let db = Database::default();
        let global = setup_nat_vec(&db);

        match unify_equations(
            &global,
            1,
            &vec![(
                eval_str_at_depth(&db, &global, "%0", 1),
                eval_str_at_depth(&db, &global, "[@Succ %0]", 1),
                eval_str(&db, &global, "#[@Nat]"),
            )],
        ) {
            Ok(EquationOutcome::Conflict) => {} // Expected: occurs check detects n in Succ n
            Ok(EquationOutcome::Success(s)) => panic!("Expected conflict, got success: {:?}", s),
            Ok(EquationOutcome::Stuck(meta)) => panic!("Unexpected stuck on {:?}", meta),
            Err(e) => panic!("Unexpected error: {:?}", e),
        }
    }

    #[test]
    fn test_injectivity_unifies_arguments() {
        // Test: Succ x ~ Succ y should produce x ~ y (which then becomes a solution)
        use crate::test_utils::{eval_str, eval_str_at_depth};

        let db = Database::default();
        let global = setup_nat_vec(&db);

        match unify_equations(
            &global,
            2,
            &vec![(
                eval_str_at_depth(&db, &global, "[@Succ %1]", 2), // x at level 0
                eval_str_at_depth(&db, &global, "[@Succ %0]", 2), // y at level 1
                eval_str(&db, &global, "#[@Nat]"),
            )],
        ) {
            Ok(EquationOutcome::Success(solutions)) => {
                assert_eq!(solutions.len(), 1); // x ~ y or y ~ x
                match solutions[0].1.as_ref() {
                    Value::Rigid(rigid) if rigid.spine.is_empty() => {
                        let (level, other_level) = (solutions[0].0, rigid.head.level);
                        assert!(
                            (level == Level::new(0) && other_level == Level::new(1))
                                || (level == Level::new(1) && other_level == Level::new(0))
                        );
                    }
                    other => panic!("Expected rigid variable, got {:?}", other),
                }
            }
            Ok(EquationOutcome::Conflict) => panic!("Unexpected conflict"),
            Ok(EquationOutcome::Stuck(meta)) => panic!("Unexpected stuck on {:?}", meta),
            Err(e) => panic!("Unexpected error: {:?}", e),
        }
    }

    #[test]
    fn test_metavariable_returns_stuck() {
        // Test: unifying against a metavariable should return Stuck
        use crate::common::MetaVariableId;
        use crate::test_utils::{eval_str, eval_str_at_depth, load_prelude};

        let db = Database::default();
        let global = load_prelude(
            &db,
            "tcon @Nat : -> U0 where dcon @Zero : @Nat dcon @Succ (%n : @Nat) : @Nat; meta ?[42] : U0;",
        );

        match unify_equations(
            &global,
            1,
            &vec![(
                eval_str_at_depth(&db, &global, "%0", 1),
                eval_str_at_depth(&db, &global, "?[42]", 1),
                eval_str(&db, &global, "U0"),
            )],
        ) {
            Ok(EquationOutcome::Stuck(id)) => assert_eq!(id, MetaVariableId::new(42)),
            Ok(EquationOutcome::Success(_)) => panic!("Expected stuck, got success"),
            Ok(EquationOutcome::Conflict) => panic!("Expected stuck, got conflict"),
            Err(e) => panic!("Unexpected error: {:?}", e),
        }
    }

    #[test]
    fn test_lambda_expansion_both_lambdas() {
        // Test: λx.x ~ λy.y should succeed via eta-expansion
        use crate::test_utils::{eval_str, load_prelude};

        let db = Database::default();
        let global = load_prelude(&db, "");

        match unify_equations(
            &global,
            0,
            &vec![(
                eval_str(&db, &global, "λ %x → %x"),
                eval_str(&db, &global, "λ %y → %y"),
                eval_str(&db, &global, "forall (%x : U0) → U0"), // Pi type
            )],
        ) {
            Ok(EquationOutcome::Success(solutions)) => {
                assert_eq!(solutions.len(), 0); // Both are equal
            }
            Ok(EquationOutcome::Conflict) => panic!("Expected success, got conflict"),
            Ok(EquationOutcome::Stuck(meta)) => panic!("Unexpected stuck on {:?}", meta),
            Err(e) => panic!("Unexpected error: {:?}", e),
        }
    }

    #[test]
    fn test_lambda_expansion_lambda_vs_rigid() {
        // Test: λx.x ~ f where f is a rigid variable
        // This should succeed by eta-expanding: x ~ f x
        use crate::test_utils::{eval_str, eval_str_at_depth};

        let db = Database::default();
        let global = GlobalEnv::new();

        match unify_equations(
            &global,
            1,
            &vec![(
                eval_str(&db, &global, "λ %x → %x"),
                eval_str_at_depth(&db, &global, "%0", 1),
                eval_str(&db, &global, "forall (%x : U0) → U0"), // Pi type
            )],
        ) {
            Ok(EquationOutcome::Success(_)) => {} // Success - eta-expansion worked
            Ok(EquationOutcome::Conflict) => panic!("Expected success, got conflict"),
            Ok(EquationOutcome::Stuck(meta)) => panic!("Unexpected stuck on {:?}", meta),
            Err(e) => panic!("Unexpected error: {:?}", e),
        }
    }

    #[test]
    fn test_lambda_expansion_different_bodies() {
        // Test: λx.x ~ λy.0
        // This expands to: x ~ 0 where x is a fresh variable
        // Pattern unification treats this as a solution: x ↦ 0
        // So this SUCCEEDS (not a conflict!)
        use crate::test_utils::eval_str;

        let db = Database::default();
        let global = GlobalEnv::new();

        match unify_equations(
            &global,
            0,
            &vec![(
                eval_str(&db, &global, "λ %x → %x"),
                eval_str(&db, &global, "λ %y → 0"),
                eval_str(&db, &global, "forall (%x : U0) → U0"), // Pi type
            )],
        ) {
            Ok(EquationOutcome::Success(solutions)) => {
                assert_eq!(solutions.len(), 1); // x ↦ 0
                assert_eq!(solutions[0].0, Level::new(0)); // fresh variable at level 0
            }
            Ok(EquationOutcome::Conflict) => panic!("Expected success, got conflict"),
            Ok(EquationOutcome::Stuck(meta)) => panic!("Unexpected stuck on {:?}", meta),
            Err(e) => panic!("Unexpected error: {:?}", e),
        }
    }
}
