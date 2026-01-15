use crate::*;
use hwml_core::*;
use std::{rc::Rc, result::Result};

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
