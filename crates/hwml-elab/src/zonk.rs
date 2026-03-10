//! Zonking: Replace solved metavariables with their solutions.
//!
//! This is a total, non-failable pass that walks a syntax tree and replaces
//! all solved metavariables with their solutions. Unsolved metavariables are
//! left as-is (they will be caught by the typechecker if they're not poisoned).
//!
//! Poisoned metavariables are also left as-is - they represent errors and
//! should not cause the zonking pass to fail.

use hwml_core::common::MetaVariableId;
use hwml_core::syn::{Syntax, SyntaxData};
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
pub fn zonk<'db>(state: &SolverState<'db>, term: &Syntax<'db>) -> Rc<Syntax<'db>> {
    let mut cache = HashMap::new();
    zonk_with_cache(state, term, &mut cache)
}

/// Internal zonking function with a cache to avoid redundant work.
fn zonk_with_cache<'db>(
    state: &SolverState<'db>,
    term: &Syntax<'db>,
    cache: &mut HashMap<MetaVariableId, Rc<Syntax<'db>>>,
) -> Rc<Syntax<'db>> {
    match &term.data {
        SyntaxData::Metavariable(meta) => {
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
                            result = Syntax::application_rc(term.loc, result, arg);
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
                        Syntax::metavariable_rc(term.loc, meta.id, zonked_args)
                    }
                }
            }
        }

        // Structural recursion for all other cases
        SyntaxData::Variable(_) => Rc::new(term.clone()),
        SyntaxData::Constant(_) => Rc::new(term.clone()),
        SyntaxData::Universe(_) => Rc::new(term.clone()),
        SyntaxData::Prim(_) => Rc::new(term.clone()),
        SyntaxData::HardwareUniverse(_) => Rc::new(term.clone()),
        SyntaxData::SignalUniverse(_) => Rc::new(term.clone()),
        SyntaxData::ModuleUniverse(_) => Rc::new(term.clone()),
        SyntaxData::Bit(_) => Rc::new(term.clone()),
        SyntaxData::Zero(_) => Rc::new(term.clone()),
        SyntaxData::One(_) => Rc::new(term.clone()),

        SyntaxData::Pi(pi) => {
            let source = zonk_with_cache(state, &pi.source, cache);
            let target = zonk_with_cache(state, &pi.target, cache);
            Syntax::pi_rc(term.loc, source, target)
        }

        SyntaxData::Lambda(lam) => {
            let body = zonk_with_cache(state, &lam.body, cache);
            Syntax::lambda_rc(term.loc, body)
        }

        SyntaxData::Application(app) => {
            let function = zonk_with_cache(state, &app.function, cache);
            let argument = zonk_with_cache(state, &app.argument, cache);
            Syntax::application_rc(term.loc, function, argument)
        }

        SyntaxData::Lift(lift) => {
            let zonked = zonk_with_cache(state, &lift.ty, cache);
            Syntax::lift_rc(term.loc, zonked)
        }

        SyntaxData::SLift(slift) => {
            let zonked = zonk_with_cache(state, &slift.ty, cache);
            Syntax::slift_rc(term.loc, zonked)
        }

        SyntaxData::MLift(mlift) => {
            let zonked = zonk_with_cache(state, &mlift.ty, cache);
            Syntax::mlift_rc(term.loc, zonked)
        }

        SyntaxData::TypeConstructor(tc) => {
            let arguments: Vec<_> = tc
                .arguments
                .iter()
                .map(|arg| zonk_with_cache(state, arg, cache))
                .collect();
            Syntax::type_constructor_rc(term.loc, tc.constructor, arguments)
        }

        SyntaxData::DataConstructor(dc) => {
            let arguments: Vec<_> = dc
                .arguments
                .iter()
                .map(|arg| zonk_with_cache(state, arg, cache))
                .collect();
            Syntax::data_constructor_rc(term.loc, dc.constructor, arguments)
        }

        SyntaxData::Case(case) => {
            // Zonk each branch body
            let branches: Vec<_> = case
                .branches
                .iter()
                .map(|branch| {
                    let body = zonk_with_cache(state, &branch.body, cache);
                    hwml_core::syn::CaseBranch::new(branch.constructor, branch.arity, body)
                })
                .collect();
            Syntax::case_rc(term.loc, case.scrutinee.index, branches)
        }

        SyntaxData::Let(let_expr) => {
            let ty = zonk_with_cache(state, &let_expr.ty, cache);
            let value = zonk_with_cache(state, &let_expr.value, cache);
            let body = zonk_with_cache(state, &let_expr.body, cache);
            Syntax::let_rc(term.loc, ty, value, body)
        }

        SyntaxData::Eq(eq) => {
            let ty = zonk_with_cache(state, &eq.ty, cache);
            let lhs = zonk_with_cache(state, &eq.lhs, cache);
            let rhs = zonk_with_cache(state, &eq.rhs, cache);
            Syntax::eq_rc(term.loc, ty, lhs, rhs)
        }

        SyntaxData::Refl(_) => Rc::new(term.clone()),

        SyntaxData::Transport(transport) => {
            let motive_body = zonk_with_cache(state, &transport.motive.body, cache);
            let motive = hwml_core::syn::Closure::new(motive_body);
            let proof = zonk_with_cache(state, &transport.proof, cache);
            let value = zonk_with_cache(state, &transport.value, cache);
            Syntax::transport_rc(term.loc, motive, proof, value)
        }

        SyntaxData::Closure(closure) => {
            let body = zonk_with_cache(state, &closure.body, cache);
            Syntax::closure_rc(term.loc, body)
        }

        SyntaxData::HArrow(harrow) => {
            let source = zonk_with_cache(state, &harrow.source, cache);
            let target = zonk_with_cache(state, &harrow.target, cache);
            Syntax::harrow_rc(term.loc, source, target)
        }

        SyntaxData::Module(module) => {
            let body = zonk_with_cache(state, &module.body, cache);
            Syntax::module_rc(term.loc, body)
        }

        SyntaxData::HApplication(happ) => {
            let module = zonk_with_cache(state, &happ.module, cache);
            let module_ty = zonk_with_cache(state, &happ.module_ty, cache);
            let argument = zonk_with_cache(state, &happ.argument, cache);
            Syntax::happlication_rc(term.loc, module, module_ty, argument)
        }

        SyntaxData::Check(check) => {
            let ty = zonk_with_cache(state, &check.ty, cache);
            let term_inner = zonk_with_cache(state, &check.term, cache);
            Syntax::check_rc(term.loc, ty, term_inner)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::SolverState;
    use hwml_core::common::Location;
    use hwml_core::syn::Syntax;
    use hwml_core::val::Value;
    use std::rc::Rc;

    #[test]
    fn test_zonk_unsolved_meta() {
        // Create a solver state with an unsolved metavariable
        let mut state = SolverState::new();
        let ty = Rc::new(Value::universe(hwml_core::common::UniverseLevel::new(0)));
        let meta_id = state.fresh_meta(Location::UNKNOWN, ty);

        // Create a term with the unsolved metavariable
        let term = Syntax::metavariable_rc(Location::UNKNOWN, meta_id, vec![]);

        // Zonk should leave it unchanged
        let zonked = zonk(&state, &term);
        assert!(
            matches!(&zonked.data, hwml_core::syn::SyntaxData::Metavariable(m) if m.id == meta_id)
        );
    }

    #[test]
    fn test_zonk_solved_meta() {
        // Create a solver state with a solved metavariable
        let mut state = SolverState::new();
        let ty = Rc::new(Value::universe(hwml_core::common::UniverseLevel::new(0)));
        let meta_id = state.fresh_meta(Location::UNKNOWN, ty);

        // Solve the metavariable to a universe
        let solution =
            Syntax::universe_rc(Location::UNKNOWN, hwml_core::common::UniverseLevel::new(1));

        // Manually set the solution (bypassing cycle check for this test)
        state.set_solution_unchecked(meta_id, solution.clone());

        // Create a term with the solved metavariable
        let term = Syntax::metavariable_rc(Location::UNKNOWN, meta_id, vec![]);

        // Zonk should replace it with the solution
        let zonked = zonk(&state, &term);
        assert!(matches!(
            &zonked.data,
            hwml_core::syn::SyntaxData::Universe(_)
        ));
    }

    #[test]
    fn test_zonk_poisoned_meta() {
        // Create a solver state with a poisoned metavariable
        let mut state = SolverState::new();
        let ty = Rc::new(Value::universe(hwml_core::common::UniverseLevel::new(0)));
        let meta_id = state.fresh_poisoned_meta(Location::UNKNOWN, ty);

        // Create a term with the poisoned metavariable
        let term = Syntax::metavariable_rc(Location::UNKNOWN, meta_id, vec![]);

        // Zonk should leave it unchanged (poisoned metas are unsolved)
        let zonked = zonk(&state, &term);
        assert!(
            matches!(&zonked.data, hwml_core::syn::SyntaxData::Metavariable(m) if m.id == meta_id)
        );

        // Verify it's actually poisoned
        assert!(state.is_poisoned(meta_id));
    }
}
