use std::rc::Rc;

use hwml_core::{Binding, Index, RcSyntax, RcValue, Syntax, Value};

use crate::{
    constraint::Constraint,
    error::ElabError,
    meta::{MetaId, MetaKind},
    state::SolverState,
};

/// Universe meta zonking pass.
///
/// After the solver reaches a fixed point:
/// 1. Collect minimum bounds for each UniverseLevel meta from LevelLeq constraints.
/// 2. Solve all unsolved UniverseLevel metas (default to level 0).
/// 3. Report any remaining unsolved Term metas as errors.
pub fn zonk<'db>(state: &mut SolverState<'db>) -> Result<(), ElabError<'db>> {
    let mut min_bounds: std::collections::HashMap<MetaId, usize> = std::collections::HashMap::new();

    let cids: Vec<_> = state.iter_constraints().map(|(id, _)| *id).collect();
    for cid in cids {
        let entry = state.constraint(cid).unwrap().clone();
        if let Constraint::LevelLeq { smaller, larger } = &entry.constraint {
            if let (Value::UniverseCode(n), Value::Flex(flex)) = (smaller.as_ref(), larger.as_ref())
            {
                let id = MetaId(flex.head.id.local_index as u32);
                let bound = min_bounds.entry(id).or_insert(0);
                if *n > *bound {
                    *bound = *n;
                }
            }
        }
    }

    let universe_metas: Vec<MetaId> = state
        .iter_metas()
        .filter_map(|(id, entry)| {
            if matches!(entry.kind, MetaKind::UniverseLevel) && entry.solution.is_none() {
                Some(*id)
            } else {
                None
            }
        })
        .collect();

    for id in universe_metas {
        let level = min_bounds.get(&id).copied().unwrap_or(0);
        let syn: RcSyntax<'db> = Rc::new(Syntax::UniverseCode(level));
        let val: RcValue<'db> = Rc::new(Value::UniverseCode(level));
        state.solve_meta(id, syn, val)?;
    }

    for (id, entry) in state.iter_metas() {
        if entry.solution.is_none() {
            return Err(ElabError::UnsolvedMeta {
                meta: *id,
                span: entry.created_at.clone(), // Use provenance information if available
                elab_backtrace: Vec::new(),
            });
        }
    }

    Ok(())
}

/// Substitute all solved metas in `syn` using their syntax solutions.
///
/// After `zonk` succeeds, every meta in `state` has a `syntax_sol`. This function
/// produces meta-free syntax suitable for the core type checker.
///
/// Convention for `Metavariable(id, [arg0,...,argN-1])` with solution body `sol`:
/// - Substitute `Index(k) → args[N-1-k]` for `k in 0..N` in `sol`.
pub fn substitute_metas_in_syntax<'db>(
    syn: &Syntax<'db>,
    state: &SolverState<'db>,
) -> RcSyntax<'db> {
    subst_metas(syn, state)
}

fn subst_metas<'db>(syn: &Syntax<'db>, state: &SolverState<'db>) -> RcSyntax<'db> {
    match syn {
        Syntax::Metavariable(meta) => {
            let id = MetaId(meta.id.local_index as u32);
            let args: Vec<RcSyntax<'db>> = meta.iter().map(|a| subst_metas(a, state)).collect();
            if let Some(sol_syn) = state.meta_solution_syntax(id) {
                apply_syntax_solution(sol_syn, &args, 0)
            } else {
                Syntax::metavariable_rc(meta.id, args)
            }
        }
        Syntax::Lambda(lam) => {
            let body = subst_metas(&lam.body.body, state);
            Syntax::lambda_rc(lam.icit, Binding::anonymous(body))
        }
        Syntax::PiCode(dom, icit, binding) => {
            let cod = &binding.body;
            let dom2 = subst_metas(dom, state);
            let cod2 = subst_metas(cod, state);
            Rc::new(Syntax::PiCode(dom2, *icit, Binding::anonymous(cod2)))
        }
        Syntax::Application(app) => {
            let fun = subst_metas(&app.function, state);
            let arg = subst_metas(&app.argument, state);
            Syntax::application_rc(fun, arg, app.icit)
        }
        Syntax::LiftCode(n, inner) => {
            let inner2 = subst_metas(inner, state);
            Rc::new(Syntax::LiftCode(*n, inner2))
        }
        _ => Rc::new(syn.clone()),
    }
}

/// Apply a syntax solution body to a list of substitution arguments.
///
/// `sol_body` is the solution in the meta's scope (arity N = args.len()).
/// Convention: `Index(k)` in `sol_body` → `args[N-1-k]`.
/// `extra_depth` tracks how many extra lambda binders we've entered inside `sol_body`.
fn apply_syntax_solution<'db>(
    sol_body: &Syntax<'db>,
    args: &[RcSyntax<'db>],
    extra_depth: usize,
) -> RcSyntax<'db> {
    let n = args.len();
    if n == 0 {
        return Rc::new(sol_body.clone());
    }
    match sol_body {
        Syntax::Variable(var) => {
            let idx = var.index.0;
            if idx < extra_depth {
                // Bound inside sol_body — leave alone.
                Rc::new(sol_body.clone())
            } else {
                let adjusted = idx - extra_depth;
                if adjusted < n {
                    // Substitution target: Index(k) → args[N-1-k].
                    let arg = &args[n - 1 - adjusted];
                    // Shift free vars in arg up by extra_depth.
                    shift_syntax_free(arg, extra_depth, 0)
                } else {
                    // Outer free variable: shift down by N (the args are removed).
                    Syntax::variable_rc(Index(idx - n))
                }
            }
        }
        Syntax::Lambda(lam) => {
            let body = apply_syntax_solution(&lam.body.body, args, extra_depth + 1);
            Syntax::lambda_rc(lam.icit, Binding::anonymous(body))
        }
        Syntax::PiCode(dom, icit, binding) => {
            let cod = &binding.body;
            let dom2 = apply_syntax_solution(dom, args, extra_depth);
            let cod2 = apply_syntax_solution(cod, args, extra_depth + 1);
            Rc::new(Syntax::PiCode(dom2, *icit, Binding::anonymous(cod2)))
        }
        Syntax::Application(app) => {
            let fun = apply_syntax_solution(&app.function, args, extra_depth);
            let arg = apply_syntax_solution(&app.argument, args, extra_depth);
            Syntax::application_rc(fun, arg, app.icit)
        }
        Syntax::Metavariable(meta) => {
            // Nested meta (e.g. from pruning): substitute its args too.
            let new_args: Vec<RcSyntax<'db>> = meta
                .iter()
                .map(|a| apply_syntax_solution(a, args, extra_depth))
                .collect();
            Syntax::metavariable_rc(meta.id, new_args)
        }
        _ => Rc::new(sol_body.clone()),
    }
}

/// Shift all free (unbound) variables in `syn` upward by `shift`.
/// `cutoff` = number of locally-bound variables at the current position.
fn shift_syntax_free<'db>(syn: &Syntax<'db>, shift: usize, cutoff: usize) -> RcSyntax<'db> {
    if shift == 0 {
        return Rc::new(syn.clone());
    }
    match syn {
        Syntax::Variable(var) => {
            if var.index.0 >= cutoff {
                Syntax::variable_rc(Index(var.index.0 + shift))
            } else {
                Rc::new(syn.clone())
            }
        }
        Syntax::Lambda(lam) => {
            let body = shift_syntax_free(&lam.body.body, shift, cutoff + 1);
            Syntax::lambda_rc(lam.icit, Binding::anonymous(body))
        }
        Syntax::PiCode(dom, icit, binding) => {
            let cod = &binding.body;
            let dom2 = shift_syntax_free(dom, shift, cutoff);
            let cod2 = shift_syntax_free(cod, shift, cutoff + 1);
            Rc::new(Syntax::PiCode(dom2, *icit, Binding::anonymous(cod2)))
        }
        Syntax::Application(app) => {
            let fun = shift_syntax_free(&app.function, shift, cutoff);
            let arg = shift_syntax_free(&app.argument, shift, cutoff);
            Syntax::application_rc(fun, arg, app.icit)
        }
        _ => Rc::new(syn.clone()),
    }
}
