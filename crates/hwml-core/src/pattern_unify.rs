//! Pattern unification for dependent pattern matching.

use crate::{
    common::{Level, MetaVariableId},
    equal, eval,
    val::{
        DataConstructorInfo, Environment, GlobalEnv, LocalEnv, RcValue, TransparentEnv,
        TypeConstructorInfo,
    },
    QualifiedName, Value,
};

#[derive(Debug, Clone)]
pub struct PatternBinding<'db> {
    pub name: Option<String>,
    pub ty: RcValue<'db>,
}

#[derive(Debug, Clone)]
pub struct PatternUnifyResult<'db> {
    pub new_bindings: Vec<PatternBinding<'db>>,
    pub solutions: Vec<(Level, RcValue<'db>)>,
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
/// * `transparent` - The transparent environment for δ-reduction during unification
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
    transparent: &TransparentEnv<'db>,
    tcon_info: &TypeConstructorInfo<'db>,
    tcon_args: &[RcValue<'db>],
    _dcon_name: QualifiedName<'db>,
    dcon_info: &DataConstructorInfo<'db>,
    base_depth: usize,
) -> Result<PatternUnifyOutcome<'db>, Error<'db>> {
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
            transparent: TransparentEnv::new(),
        };
        let ty = eval::eval(&mut env, ty_syntax)?;
        let rigid_var = Value::variable_rc(Level::new(current_depth), ty.clone());
        new_bindings.push(PatternBinding { name: None, ty });
        local.push(rigid_var);
        current_depth += 1;
    }

    let mut env = Environment {
        global,
        local,
        transparent: TransparentEnv::new(),
    };
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
        transparent: TransparentEnv::new(),
    };
    param_env.extend(parameters.iter().cloned());

    let index_types: Result<Vec<_>, _> = tcon_info
        .indices()
        .iter()
        .map(|ty_syntax| eval::eval(&mut param_env, ty_syntax))
        .collect();
    let index_types = index_types?;

    let equations: Vec<(RcValue<'db>, RcValue<'db>, RcValue<'db>)> = scrutinee_indices
        .into_iter()
        .zip(constructor_indices.into_iter())
        .zip(index_types.into_iter())
        .map(|((lhs, rhs), ty)| (lhs, rhs, ty))
        .collect();

    let unify_depth = base_depth + new_bindings.len();
    // Use the transparent environment from the typechecker to enable δ-reduction during unification
    match unify_equations(global, transparent, unify_depth, &equations)? {
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
    Success(Vec<(Level, RcValue<'db>)>),
    Conflict,
    Stuck(MetaVariableId),
}

/// Check if a variable at the given level occurs in a value.
/// This is critical for soundness: if we try to solve `?meta =? body` where `?meta` appears
/// in `body`, we would create an infinite cycle in the semantic domain.
///
/// CRITICAL: This function must unfold transparent variables! If we have `let y = ?meta`,
/// and we check whether `?meta` occurs in `y`, we must unfold `y` to detect the cycle.
/// Without this, we would create the substitution `?meta := y`, causing infinite loops.
fn occurs_check(transparent: &TransparentEnv<'_>, level: Level, value: &Value<'_>) -> bool {
    match value {
        Value::Rigid(rigid) => {
            if rigid.head.level == level {
                return true;
            }

            // CRITICAL: If this rigid variable is transparent (let-bound), unfold it!
            // Example: let y = ?meta; occurs(?meta, y) must return true
            if let Some(unfolded) = transparent.lookup(rigid.head.level) {
                if occurs_check(transparent, level, &unfolded) {
                    return true;
                }
            }

            // Also check the spine for occurrences
            rigid.spine.iter().any(|elim| match elim {
                crate::val::Eliminator::Application(app) => {
                    occurs_check(transparent, level, &app.argument.value)
                }
                crate::val::Eliminator::Case(_) => false,
            })
        }
        Value::Flex(flex) => flex.spine.iter().any(|elim| match elim {
            crate::val::Eliminator::Application(app) => {
                occurs_check(transparent, level, &app.argument.value)
            }
            crate::val::Eliminator::Case(_) => false,
        }),
        Value::DataConstructor(dcon) => dcon
            .arguments
            .iter()
            .any(|arg| occurs_check(transparent, level, arg)),
        Value::TypeConstructor(tcon) => tcon
            .arguments
            .iter()
            .any(|arg| occurs_check(transparent, level, arg)),
        Value::Pi(pi) => occurs_check(transparent, level, &pi.source),
        Value::Lambda(_) => false,
        Value::EqType(eq) => {
            occurs_check(transparent, level, &eq.ty)
                || occurs_check(transparent, level, &eq.lhs)
                || occurs_check(transparent, level, &eq.rhs)
        }
        Value::Transport(transport) => {
            occurs_check(transparent, level, &transport.proof)
                || occurs_check(transparent, level, &transport.value)
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
        Value::Let(let_val) => {
            occurs_check(transparent, level, &let_val.ty)
                || occurs_check(transparent, level, &let_val.value)
                || occurs_check(transparent, level, &let_val.body)
        }
    }
}

fn unify_equations<'db>(
    global: &GlobalEnv<'db>,
    transparent: &TransparentEnv<'db>,
    depth: usize,
    equations: &[(RcValue<'db>, RcValue<'db>, RcValue<'db>)],
) -> Result<EquationOutcome<'db>, Error<'db>> {
    let mut solutions: Vec<(Level, RcValue<'db>)> = Vec::new();
    let mut work_list: Vec<(RcValue<'db>, RcValue<'db>, RcValue<'db>)> = equations.to_vec();

    while let Some((lhs, rhs, ty)) = work_list.pop() {
        if equal::equate(global, transparent, depth, &lhs, &rhs, &ty).is_ok() {
            continue;
        }

        match (&*lhs, &*rhs, &*ty) {
            (Value::Flex(flex), _, _) | (_, Value::Flex(flex), _) => {
                return Ok(EquationOutcome::Stuck(flex.head.id));
            }

            (Value::Rigid(rigid), _, _) if rigid.spine.is_empty() => {
                let level = rigid.head.level;

                // CRITICAL: Miller Pattern Validation!
                // If this variable is transparent (let-bound), it's NOT a valid pattern variable.
                // Example: let x = zero; ?meta x =? one
                // This looks like a Miller pattern (?meta applied to variable x), but x is actually
                // zero in disguise! We cannot invert x because it's not a true parameter.
                // We must reject this and return Conflict.
                if transparent.lookup(level).is_some() {
                    // This variable is let-bound, not a pattern variable!
                    // Reject the pattern and return Conflict.
                    return Ok(EquationOutcome::Conflict);
                }

                if occurs_check(transparent, level, &*rhs) {
                    return Ok(EquationOutcome::Conflict);
                }
                solutions.push((level, rhs.clone()));
            }

            (_, Value::Rigid(rigid), _) if rigid.spine.is_empty() => {
                let level = rigid.head.level;

                // CRITICAL: Miller Pattern Validation (symmetric case)
                if transparent.lookup(level).is_some() {
                    // This variable is let-bound, not a pattern variable!
                    return Ok(EquationOutcome::Conflict);
                }

                if occurs_check(transparent, level, &*lhs) {
                    return Ok(EquationOutcome::Conflict);
                }
                solutions.push((level, lhs.clone()));
            }

            (Value::Lambda(l1), Value::Lambda(l2), Value::Pi(pi)) => {
                let var = Value::variable_rc(Level::new(depth), pi.source.clone());
                let l1_body = eval::run_closure(global, &l1.body, [var.clone()])?;
                let l2_body = eval::run_closure(global, &l2.body, [var.clone()])?;
                let result_ty = eval::run_closure(global, &pi.target, [var])?;
                work_list.push((l1_body, l2_body, result_ty));
            }

            (Value::Lambda(l1), _, Value::Pi(pi)) => {
                let var = Value::variable_rc(Level::new(depth), pi.source.clone());
                let l1_body = eval::run_closure(global, &l1.body, [var.clone()])?;
                let rhs_applied = eval::run_application(global, &rhs, var.clone())?;
                let result_ty = eval::run_closure(global, &pi.target, [var])?;
                work_list.push((l1_body, rhs_applied, result_ty));
            }

            (_, Value::Lambda(l2), Value::Pi(pi)) => {
                let var = Value::variable_rc(Level::new(depth), pi.source.clone());
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
                        transparent: TransparentEnv::new(),
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
                let type_ty = Value::universe_rc(crate::common::UniverseLevel::new(0));
                work_list.push((eq1.ty.clone(), eq2.ty.clone(), type_ty.clone()));
                // x and y have type A (use eq1.ty as the type)
                work_list.push((eq1.lhs.clone(), eq2.lhs.clone(), eq1.ty.clone()));
                work_list.push((eq1.rhs.clone(), eq2.rhs.clone(), eq1.ty.clone()));
            }

            // Rule: Axiom K - all Refl proofs are equal at EqType
            (Value::Refl(_), Value::Refl(_), Value::EqType(_)) => {
                // refl ~ refl  is always true (Axiom K)
                // Delete this equation
            }

            // Rule: Injectivity - Transport at EqType
            (Value::Transport(t1), Value::Transport(t2), _) => {
                // transport P1 h1 v1 ~ transport P2 h2 v2
                // We need to unify the motives, proofs, and values
                // For motives, we need to eta-expand them
                let var = Value::variable_rc(
                    Level::new(depth),
                    Value::universe_rc(crate::common::UniverseLevel::new(0)),
                );
                let m1_body = eval::run_closure(global, &t1.motive, [var.clone()])?;
                let m2_body = eval::run_closure(global, &t2.motive, [var.clone()])?;
                let motive_ty = Value::universe_rc(crate::common::UniverseLevel::new(0));
                work_list.push((m1_body, m2_body, motive_ty));

                let proof_ty = Value::universe_rc(crate::common::UniverseLevel::new(0));
                work_list.push((t1.proof.clone(), t2.proof.clone(), proof_ty));

                let value_ty = Value::universe_rc(crate::common::UniverseLevel::new(0));
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
        let transparent = TransparentEnv::new();

        match unify_pattern(
            &global,
            &transparent,
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
        let transparent = TransparentEnv::new();

        match unify_pattern(
            &global,
            &transparent,
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
        let transparent = TransparentEnv::new();

        match unify_pattern(
            &global,
            &transparent,
            global.type_constructor("Vec".into_with_db(&db)).unwrap(),
            &vec![Value::bit_rc(), eval_str_at_depth(&db, &global, "%0", 1)],
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
                        assert_eq!(dcon.constructor.name(&db).to_string(&db), "Succ");
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
        let transparent = TransparentEnv::new();

        match unify_equations(
            &global,
            &transparent,
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
        let transparent = TransparentEnv::new();

        match unify_equations(
            &global,
            &transparent,
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
            "tcon @Nat : -> U0 where dcon @Zero : #[@Nat] dcon @Succ (%n : #[@Nat]) : #[@Nat]; meta ?[42] : U0;",
        );
        let transparent = TransparentEnv::new();

        match unify_equations(
            &global,
            &transparent,
            1,
            &vec![(
                eval_str_at_depth(&db, &global, "%0", 1),
                eval_str_at_depth(&db, &global, "?[42]", 1),
                eval_str(&db, &global, "U0"),
            )],
        ) {
            Ok(EquationOutcome::Stuck(id)) => {
                assert_eq!(id, MetaVariableId::new(42))
            }
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
        let transparent = TransparentEnv::new();

        match unify_equations(
            &global,
            &transparent,
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
        let transparent = TransparentEnv::new();

        match unify_equations(
            &global,
            &transparent,
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
        let transparent = TransparentEnv::new();

        match unify_equations(
            &global,
            &transparent,
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

    #[test]
    fn test_unifier_sees_transparent_bindings() {
        // CRITICAL TEST: Verify that the unifier can see let-bound variables via δ-reduction
        // This test proves that threading TransparentEnv into the unifier actually works!
        //
        // Setup: let y : Nat = @Zero (at level 0)
        // Equation: y =? @Zero
        // Expected: Success (the unifier should unfold y to @Zero and see they're equal)
        // Without the fix: Would return Conflict (treating y as a rigid variable ≠ @Zero)
        use crate::test_utils::{eval_str, load_prelude};

        let db = Database::default();
        let global = load_prelude(
            &db,
            "tcon @Nat : -> U0 where dcon @Zero : #[@Nat] dcon @Succ (%n : #[@Nat]) : #[@Nat];",
        );

        // Create a transparent environment with y = @Zero at level 0
        let mut transparent = TransparentEnv::new();
        let zero_val = eval_str(&db, &global, "[@Zero]");
        transparent.push_transparent(zero_val.clone());

        // Create the equation: Rigid(Level(0)) =? @Zero
        // Rigid(Level(0)) represents the variable y
        let nat_ty = eval_str(&db, &global, "#[@Nat]");
        let y_var = Value::variable_rc(Level::new(0), nat_ty.clone());

        // Try to unify y =? @Zero
        match unify_equations(
            &global,
            &transparent,
            1, // depth = 1 because we have one binding (y)
            &vec![(y_var, zero_val, nat_ty)],
        ) {
            Ok(EquationOutcome::Success(solutions)) => {
                // Should succeed with no new solutions (y is already bound to @Zero)
                assert_eq!(
                    solutions.len(),
                    0,
                    "Expected no solutions (y is transparent, not a pattern variable)"
                );
            }
            Ok(EquationOutcome::Conflict) => {
                panic!("UNIFIER BLINDNESS: The unifier cannot see that y = @Zero!")
            }
            Ok(EquationOutcome::Stuck(meta)) => panic!("Unexpected stuck on {:?}", meta),
            Err(e) => panic!("Unexpected error: {:?}", e),
        }
    }

    #[test]
    fn test_occurs_check_detects_transparent_cycle() {
        // CRITICAL SOUNDNESS TEST: Verify that occurs check unfolds transparent variables
        // This prevents infinite cycles when solving for pattern variables!
        //
        // Setup: let y : Nat = z (at level 1, where z is at level 0)
        // Equation: z =? @Succ y
        // Expected: Conflict (because y = z, so z =? @Succ z would create a cycle if we solve z := @Succ y)
        // Without the fix: Would accept z := @Succ y, but y = z, so z := @Succ z (infinite!)
        use crate::test_utils::{eval_str, load_prelude};

        let db = Database::default();
        let global = load_prelude(
            &db,
            "tcon @Nat : -> U0 where dcon @Zero : #[@Nat] dcon @Succ (%n : #[@Nat]) : #[@Nat];",
        );

        // Create a transparent environment where y (level 1) = z (level 0)
        let nat_ty = eval_str(&db, &global, "#[@Nat]");
        let z_var = Value::variable_rc(Level::new(0), nat_ty.clone());

        let mut transparent = TransparentEnv::new();
        transparent.push_rigid(); // z at level 0
        transparent.push_transparent(z_var.clone()); // y at level 1, bound to z

        // Create the equation: z =? @Succ y
        // This is a pattern unification problem: we're trying to solve for z
        // Build @Succ y manually
        let y_var = Value::variable_rc(Level::new(1), nat_ty.clone());
        let succ_const = eval_str(&db, &global, "[@Succ]");
        let succ_y_applied = match succ_const.as_ref() {
            Value::DataConstructor(dcon) => {
                Value::data_constructor_rc(dcon.constructor, vec![y_var])
            }
            _ => panic!("Expected @Succ to be a data constructor"),
        };

        // Try to unify z =? @Succ y
        // The occurs check should detect that z occurs in @Succ y (because y = z)
        match unify_equations(
            &global,
            &transparent,
            2, // depth = 2 (z and y)
            &vec![(z_var, succ_y_applied, nat_ty)],
        ) {
            Ok(EquationOutcome::Success(_)) => {
                panic!("SOUNDNESS BUG: Occurs check failed to detect cycle! z =? @Succ y where y = z should fail!")
            }
            Ok(EquationOutcome::Conflict) => {
                // This is the correct outcome! The occurs check should detect that
                // z occurs in @Succ y (because y unfolds to z), preventing the cycle.
            }
            Ok(EquationOutcome::Stuck(meta)) => panic!("Unexpected stuck on {:?}", meta),
            Err(e) => panic!("Unexpected error: {:?}", e),
        }
    }

    #[test]
    fn test_miller_pattern_rejects_transparent_variables() {
        // CRITICAL CORRECTNESS TEST: Verify that transparent variables are rejected as Miller patterns
        // This prevents bogus solutions that ignore let-bound constraints!
        //
        // Setup: let x : Nat = @Zero (at level 0)
        // Equation: x =? @Succ @Zero
        // Expected: Conflict (x is not a pattern variable, it's bound to @Zero)
        // Without the fix: Would accept x := @Succ @Zero, completely ignoring that x = @Zero!
        use crate::test_utils::{eval_str, load_prelude};

        let db = Database::default();
        let global = load_prelude(
            &db,
            "tcon @Nat : -> U0 where dcon @Zero : #[@Nat] dcon @Succ (%n : #[@Nat]) : #[@Nat];",
        );

        // Create a transparent environment where x (level 0) = @Zero
        let nat_ty = eval_str(&db, &global, "#[@Nat]");
        let zero_val = eval_str(&db, &global, "[@Zero]");

        let mut transparent = TransparentEnv::new();
        transparent.push_transparent(zero_val.clone()); // x at level 0, bound to @Zero

        // Create the equation: x =? @Succ @Zero
        let x_var = Value::variable_rc(Level::new(0), nat_ty.clone());
        let succ_zero = eval_str(&db, &global, "[@Succ [@Zero]]");

        // Try to unify x =? @Succ @Zero
        // This should REJECT the pattern because x is transparent (let-bound to @Zero)
        match unify_equations(
            &global,
            &transparent,
            1, // depth = 1 (x)
            &vec![(x_var, succ_zero, nat_ty)],
        ) {
            Ok(EquationOutcome::Success(_)) => {
                panic!("CORRECTNESS BUG: Miller pattern accepted transparent variable! x =? @Succ @Zero where x = @Zero should fail!")
            }
            Ok(EquationOutcome::Conflict) => {
                // This is the correct outcome! The pattern validator should reject x
                // because it's transparent (let-bound), not a true pattern variable.
            }
            Ok(EquationOutcome::Stuck(meta)) => panic!("Unexpected stuck on {:?}", meta),
            Err(e) => panic!("Unexpected error: {:?}", e),
        }
    }
}
