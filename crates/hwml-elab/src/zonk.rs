//! Zonking: Replace solved metavariables with their solutions.
//!
//! This is a total, non-failable pass that walks a syntax tree and replaces
//! all solved metavariables with their solutions. Unsolved metavariables are
//! left as-is (they will be caught by the typechecker if they're not poisoned).
//!
//! Poisoned metavariables are also left as-is - they represent errors and
//! should not cause the zonking pass to fail.

use hwml_core::common::MetaVariableId;
use hwml_core::{RcSyntax, Syntax};

use std::collections::HashMap;
use std::rc::Rc;

use crate::engine::SolverState;

/// Zonk a syntax term, replacing all solved metavariables with their solutions.
/// This is a total function - it never fails.
///
/// - Solved metavariables are replaced with their solutions (recursively zonked)
/// - Unsolved metavariables are left as-is
/// - Poisoned metavariables are left as-is
///
/// The zonking pass uses a cache to avoid re-zonking the same metavariable multiple times.
pub fn zonk<'db>(state: &SolverState<'db>, term: &Syntax<'db>) -> RcSyntax<'db> {
    let mut cache = HashMap::new();
    zonk_with_cache(state, term, &mut cache)
}

/// Internal zonking function with a cache to avoid redundant work.
fn zonk_with_cache<'db>(
    state: &SolverState<'db>,
    term: &Syntax<'db>,
    cache: &mut HashMap<MetaVariableId, RcSyntax<'db>>,
) -> RcSyntax<'db> {
    match term {
        Syntax::Metavariable(meta) => {
            // Check if we've already zonked this metavariable
            if let Some(cached) = cache.get(&meta.id) {
                return cached.clone();
            }

            // Check if the metavariable is solved
            match state.solution(meta.id) {
                Some(solution) => {
                    // Recursively zonk the solution
                    let zonked = zonk_with_cache(state, &solution, cache);
                    cache.insert(meta.id, zonked.clone());

                    // If there are arguments, we need to apply them to the zonked solution
                    if meta.substitution.is_empty() {
                        zonked
                    } else {
                        // Zonk the arguments
                        let zonked_args: Vec<_> = meta
                            .substitution
                            .iter()
                            .map(|arg| zonk_with_cache(state, arg, cache))
                            .collect();

                        // Apply the arguments to the solution
                        let mut result = zonked;
                        for arg in zonked_args {
                            result = Syntax::application_rc(result, arg);
                        }
                        result
                    }
                }
                None => {
                    // Unsolved or poisoned metavariable - leave it as-is
                    // but zonk the arguments
                    if meta.substitution.is_empty() {
                        Rc::new(term.clone())
                    } else {
                        let zonked_args: Vec<_> = meta
                            .substitution
                            .iter()
                            .map(|arg| zonk_with_cache(state, arg, cache))
                            .collect();
                        Syntax::metavariable_rc(meta.id, zonked_args)
                    }
                }
            }
        }

        // Structural recursion for all other cases
        Syntax::Variable(_) => Rc::new(term.clone()),
        Syntax::Constant(_) => Rc::new(term.clone()),
        Syntax::Universe(_) => Rc::new(term.clone()),
        Syntax::Prim(_) => Rc::new(term.clone()),
        Syntax::HardwareUniverse(_) => Rc::new(term.clone()),
        Syntax::SignalUniverse(_) => Rc::new(term.clone()),
        Syntax::ModuleUniverse(_) => Rc::new(term.clone()),
        Syntax::Bit(_) => Rc::new(term.clone()),
        Syntax::Zero(_) => Rc::new(term.clone()),
        Syntax::One(_) => Rc::new(term.clone()),

        Syntax::Pi(pi) => {
            let source = zonk_with_cache(state, &pi.source, cache);
            let target_body = zonk_with_cache(state, &pi.target.body, cache);
            Syntax::pi_rc(source, hwml_core::binding::Binding::new(target_body))
        }

        Syntax::Lambda(lam) => {
            let body_term = zonk_with_cache(state, &lam.body.body, cache);
            Syntax::lambda_rc(hwml_core::binding::Binding::new(body_term))
        }

        Syntax::Application(app) => {
            let function = zonk_with_cache(state, &app.function, cache);
            let argument = zonk_with_cache(state, &app.argument, cache);
            Syntax::application_rc(function, argument)
        }

        Syntax::Lift(lift) => {
            let zonked = zonk_with_cache(state, &lift.ty, cache);
            Syntax::lift_rc(zonked)
        }

        Syntax::SLift(slift) => {
            let zonked = zonk_with_cache(state, &slift.ty, cache);
            Syntax::slift_rc(zonked)
        }

        Syntax::MLift(mlift) => {
            let zonked = zonk_with_cache(state, &mlift.ty, cache);
            Syntax::mlift_rc(zonked)
        }

        Syntax::TypeConstructor(tc) => {
            let arguments: Vec<_> = tc
                .arguments
                .iter()
                .map(|arg| zonk_with_cache(state, arg, cache))
                .collect();
            Syntax::type_constructor_rc(tc.constructor, arguments)
        }

        Syntax::DataConstructor(dc) => {
            let arguments: Vec<_> = dc
                .arguments
                .iter()
                .map(|arg| zonk_with_cache(state, arg, cache))
                .collect();
            Syntax::data_constructor_rc(dc.constructor, arguments)
        }

        Syntax::Case(case) => {
            // Zonk each branch body
            let branches: Vec<_> = case
                .branches
                .iter()
                .map(|branch| {
                    let body_term = zonk_with_cache(state, &branch.body.body, cache);
                    let arity = branch.body.arity;
                    hwml_core::syn::CaseBranch::new(
                        branch.constructor,
                        hwml_core::binding::DynBinding::new(arity, body_term),
                    )
                })
                .collect();
            Syntax::case_rc(case.scrutinee.index, branches)
        }

        Syntax::Let(let_expr) => {
            let ty = zonk_with_cache(state, &let_expr.ty, cache);
            let value = zonk_with_cache(state, &let_expr.value, cache);
            let body_term = zonk_with_cache(state, &let_expr.body.body, cache);
            Syntax::let_rc(ty, value, hwml_core::binding::Binding::new(body_term))
        }

        Syntax::Eq(eq) => {
            let ty = zonk_with_cache(state, &eq.ty, cache);
            let lhs = zonk_with_cache(state, &eq.lhs, cache);
            let rhs = zonk_with_cache(state, &eq.rhs, cache);
            Syntax::eq_rc(ty, lhs, rhs)
        }

        Syntax::Refl(_) => Rc::new(term.clone()),

        Syntax::Transport(transport) => {
            let motive = zonk_with_cache(state, &transport.motive, cache);
            let proof = zonk_with_cache(state, &transport.proof, cache);
            let value = zonk_with_cache(state, &transport.value, cache);
            Syntax::transport_rc(motive, proof, value)
        }

        Syntax::HArrow(harrow) => {
            let source = zonk_with_cache(state, &harrow.source, cache);
            let target = zonk_with_cache(state, &harrow.target, cache);
            Syntax::harrow_rc(source, target)
        }

        Syntax::Module(module) => {
            let body_term = zonk_with_cache(state, &module.body.body, cache);
            Syntax::module_rc(hwml_core::binding::Binding::new(body_term))
        }

        Syntax::HApplication(happ) => {
            let module = zonk_with_cache(state, &happ.module, cache);
            let module_ty = zonk_with_cache(state, &happ.module_ty, cache);
            let argument = zonk_with_cache(state, &happ.argument, cache);
            Syntax::happlication_rc(module, module_ty, argument)
        }

        Syntax::Check(check) => {
            let ty = zonk_with_cache(state, &check.ty, cache);
            let term_inner = zonk_with_cache(state, &check.term, cache);
            Syntax::check_rc(ty, term_inner)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::SolverState;
    use hwml_core::syn::Syntax;
    use hwml_core::val::Value;

    #[test]
    fn test_zonk_unsolved_meta() {
        // Create a solver state with an unsolved metavariable
        let mut state = SolverState::new();
        let ty = Value::universe_rc(hwml_core::common::UniverseLevel::new(0));
        let meta_id = state.fresh_meta(ty, None);

        // Create a term with the unsolved metavariable
        let term = Syntax::metavariable_rc(meta_id, vec![]);

        // Zonk should leave it unchanged
        let zonked = zonk(&state, &term);
        assert!(
            matches!(zonked.as_ref(), hwml_core::syn::Syntax::Metavariable(m) if m.id == meta_id)
        );
    }

    #[test]
    fn test_zonk_solved_meta() {
        // Create a solver state with a solved metavariable
        let mut state = SolverState::new();
        let ty = Value::universe_rc(hwml_core::common::UniverseLevel::new(0));
        let meta_id = state.fresh_meta(ty, None);

        // Solve the metavariable to a universe
        let solution = Syntax::universe_rc(hwml_core::common::UniverseLevel::new(1));

        // Manually set the solution (bypassing cycle check for this test)
        state.set_solution_unchecked(meta_id, solution.clone());

        // Create a term with the solved metavariable
        let term = Syntax::metavariable_rc(meta_id, vec![]);

        // Zonk should replace it with the solution
        let zonked = zonk(&state, &term);
        assert!(matches!(
            zonked.as_ref(),
            hwml_core::syn::Syntax::Universe(_)
        ));
    }

    #[test]
    fn test_zonk_poisoned_meta() {
        // Create a solver state with a poisoned metavariable
        let mut state = SolverState::new();
        let ty = Value::universe_rc(hwml_core::common::UniverseLevel::new(0));
        let meta_id = state.fresh_poisoned_meta(ty, None);

        // Create a term with the poisoned metavariable
        let term = Syntax::metavariable_rc(meta_id, vec![]);

        // Zonk should leave it unchanged (poisoned metas are unsolved)
        let zonked = zonk(&state, &term);
        assert!(
            matches!(zonked.as_ref(), hwml_core::syn::Syntax::Metavariable(m) if m.id == meta_id)
        );

        // Verify it's actually poisoned
        assert!(state.is_poisoned(meta_id));
    }
}
