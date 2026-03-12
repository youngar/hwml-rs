use crate::*;
use hwml_core::*;
use std::rc::Rc;

/// Substitute a flex term with with a metavariable solution. The meta variable's
/// substitution is used to instantiate the solution for this particular site.
pub fn substitute<'db, 'g>(
    ctx: &SolverEnvironment<'db, 'g>,
    flex: &val::Flex<'db>,
    solution: &Rc<Syntax<'db>>,
) -> Rc<Value<'db>> {
    let global = ctx.tc_env.values.global;
    eval::substitute(global, solution, flex.head.local.clone()).unwrap()
}

/// Force the substitution of a metavariable with its solution, if available.
///
/// This implements the "propagate metas" functionality: when a metavariable has been
/// solved, we substitute its solution into the value. Forcing only computes until
/// it hits the next head constructor which cannot be further unblocked - it does
/// not recurse into values.
///
/// This is essential for the async solver because metavariables may be solved
/// concurrently by other tasks, and we need to pick up those solutions.
pub fn force<'db, 'g>(
    ctx: &SolverEnvironment<'db, 'g>,
    mut value: Rc<Value<'db>>,
) -> Result<Rc<Value<'db>>, eval::Error> {
    let global = ctx.tc_env.values.global;
    while let Value::Flex(flex) = &*value {
        match ctx.solution(flex.head.id) {
            Some(syn_solution) => {
                println!("[Force] Substituting meta {} with solution", flex.head.id);
                let sem_solution =
                    eval::substitute(global, &syn_solution, flex.head.local.clone()).unwrap();
                value = eval::run_spine(global, sem_solution, &flex.spine)?;
            }
            None => break,
        }
    }
    Ok(value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::{SingleThreadedExecutor, SolverEnvironment};
    use hwml_core::check::TCEnvironment;
    use hwml_core::test_utils::{eval_str, load_prelude, parse};
    use hwml_core::val::{Environment, GlobalEnv};
    use hwml_core::Database;

    /// Assert that forcing a term leaves it unchanged (for non-flex values)
    fn assert_force_unchanged(input: &str) {
        let db = Database::new();
        let global = GlobalEnv::new();
        let mut executor = SingleThreadedExecutor::new();
        let tc_env = TCEnvironment {
            db: &db,
            values: Environment::new(&global),
            types: Vec::new(),
        };
        let ctx = SolverEnvironment::new_from_global(tc_env, executor.spawner());

        let val = eval_str(&db, &global, input);
        let result = force(&ctx, val.clone()).expect("force failed");
        assert!(
            Rc::ptr_eq(&val, &result),
            "force should return same Rc for {}",
            input
        );
    }

    /// Create a fresh meta with the given type, solve it, and force it.
    /// Returns the forced result.
    fn solve_and_force<'db>(
        db: &'db Database,
        global: &GlobalEnv<'db>,
        meta_ty: &'db str,
        solution: &'db str,
    ) -> Rc<Value<'db>> {
        let mut executor = SingleThreadedExecutor::new();
        let tc_env = TCEnvironment {
            db,
            values: Environment::new(global),
            types: Vec::new(),
        };
        let ctx = SolverEnvironment::new_from_global(tc_env, executor.spawner());

        let ty = eval_str(db, global, meta_ty);
        let meta_val = ctx.fresh_meta(ty);
        let meta_id = match &*meta_val {
            Value::Flex(flex) => flex.head.id,
            _ => panic!("Expected Flex"),
        };

        ctx.solve(meta_id, parse(db, solution));
        force(&ctx, meta_val).expect("force failed")
    }

    #[test]
    fn test_force_universe() {
        assert_force_unchanged("U0");
    }

    #[test]
    fn test_force_bit() {
        assert_force_unchanged("Bit");
    }

    #[test]
    fn test_force_bit_values() {
        assert_force_unchanged("0");
        assert_force_unchanged("1");
    }

    #[test]
    fn test_force_pi() {
        assert_force_unchanged("∀ (%x : U0) → U0");
    }

    #[test]
    fn test_force_lambda() {
        assert_force_unchanged("λ %x → %x");
    }

    #[test]
    fn test_force_unsolved_meta_returns_same() {
        let db = Database::new();
        let global = GlobalEnv::new();
        let mut executor = SingleThreadedExecutor::new();
        let tc_env = TCEnvironment {
            db: &db,
            values: Environment::new(&global),
            types: Vec::new(),
        };
        let ctx = SolverEnvironment::new_from_global(tc_env, executor.spawner());

        let ty = eval_str(&db, &global, "U0");
        let meta_val = ctx.fresh_meta(ty);
        let result = force(&ctx, meta_val.clone()).expect("force failed");
        assert!(Rc::ptr_eq(&meta_val, &result));
    }

    #[test]
    fn test_force_solved_meta_substitutes() {
        let db = Database::new();
        let global = GlobalEnv::new();
        let result = solve_and_force(&db, &global, "U0", "Bit");
        assert!(matches!(&*result, Value::Bit(_)));
    }

    #[test]
    fn test_force_solved_meta_with_universe() {
        let db = Database::new();
        let global = GlobalEnv::new();
        let result = solve_and_force(&db, &global, "U1", "U0");
        match &*result {
            Value::Universe(u) => assert_eq!(u.level, hwml_core::UniverseLevel::new(0)),
            _ => panic!("Expected Universe, got {:?}", result),
        }
    }

    // ========== Prelude-based Tests ==========

    #[test]
    fn test_force_prelude_meta_unsolved() {
        // A metavariable declared in the prelude but not solved stays as Flex
        let db = Database::new();
        let global = load_prelude(&db, "meta ?[0] : U0;");
        let executor = SingleThreadedExecutor::new();
        let tc_env = TCEnvironment {
            db: &db,
            values: Environment::new(&global),
            types: Vec::new(),
        };
        // Use new_from_global to initialize solver with declared metavariables
        let ctx = SolverEnvironment::new_from_global(tc_env, executor.spawner());

        // Evaluate ?[0] - this gives us a Flex value
        let meta_val = eval_str(&db, &global, "?[0]");
        let result = force(&ctx, meta_val.clone()).expect("force failed");
        // Should stay as Flex since not solved
        assert!(matches!(&*result, Value::Flex(_)));
    }

    #[test]
    fn test_force_prelude_meta_with_args() {
        // Metavariable with arguments declared in prelude
        // The prelude declares: meta ?[0] (%x : U0) : U0;
        // This means ?[0] takes one argument in its substitution
        let db = Database::new();
        let global = load_prelude(&db, "meta ?[0] (%x : U0) : U0;");
        let executor = SingleThreadedExecutor::new();
        let tc_env = TCEnvironment {
            db: &db,
            values: Environment::new(&global),
            types: Vec::new(),
        };
        // Use new_from_global to initialize solver with declared metavariables
        let ctx = SolverEnvironment::new_from_global(tc_env, executor.spawner());

        // When we solve ?[0] with λ%x → Bit, substituting with U0 should give Bit
        // Note: the metavariable's solution is a lambda that will be applied to
        // substitution arguments via substitute(), which builds the local env
        let solution = parse(&db, "λ %x → Bit");
        ctx.solve(hwml_core::common::MetaVariableId::new(0), solution);

        // Evaluate ?[0 U0] - metavariable with U0 in substitution
        // This gives us Flex{ head: Meta(0, local=[U0]), spine: [] }
        let meta_applied = eval_str(&db, &global, "?[0 U0]");
        let result = force(&ctx, meta_applied).expect("force failed");
        // The solution (λ%x → Bit) evaluated with local=[U0] gives Lambda{ body: Bit }
        assert!(
            matches!(&*result, Value::Lambda(_)),
            "Expected Lambda, got {:?}",
            result
        );
    }
}
