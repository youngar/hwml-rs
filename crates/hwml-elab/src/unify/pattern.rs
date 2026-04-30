use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

use hwml_core::{
    Binding, Index, Level, RcSyntax, RcValue, Syntax, Value,
    ty::RcTy,
    val::{Closure, DataConstructor, EqType, Flex, GlobalEnv, LocalEnv, TypeConstructor},
    eval,
};

use crate::{error::ElabError, meta::MetaId, state::SolverState};

/// Miller pattern unification: `Flex { id, local, spine } = rhs`.
///
/// Returns `Ok(true)` on success, `Ok(false)` if not a pattern (non-linear or rhs out-of-scope).
/// Returns `Err` only for hard failures: occurs-check or scope violation with no valid fallback.
pub fn pattern_unify<'db>(
    global: &GlobalEnv<'db>,
    state: &mut SolverState<'db>,
    flex: &Flex<'db>,
    rhs: RcValue<'db>,
    _rhs_ty: RcTy<'db>,
) -> Result<bool, ElabError<'db>> {
    let meta_id = MetaId(flex.head.id.local_index as u32);

    if state.meta_solution(meta_id).is_some() {
        return Ok(false);
    }

    // Only handle empty spine for now.
    if !flex.spine.is_empty() {
        return Ok(false);
    }

    let local = &flex.head.local;
    let arity = local.depth();

    // Build rename (linear vars) and ambiguous (duplicate vars) sets.
    // Non-linear positions are tracked separately: if the RHS doesn't mention an ambiguous
    // variable, the unification still succeeds (Abel-Pientka §3.3).
    let mut rename: HashMap<Level, usize> = HashMap::new();
    let mut ambiguous: HashSet<Level> = HashSet::new();
    for i in 0..arity {
        let val = local.get(Level::new(i));
        match val.as_ref() {
            Value::Rigid(rigid) if rigid.spine.is_empty() => {
                let level = rigid.head.level;
                if ambiguous.contains(&level) {
                    // Already known ambiguous: skip.
                } else if rename.contains_key(&level) {
                    // Second occurrence: mark ambiguous, retract from rename.
                    rename.remove(&level);
                    ambiguous.insert(level);
                } else {
                    rename.insert(level, i);
                }
            }
            _ => return Ok(false), // Non-variable arg: can't invert.
        }
    }

    // Produce the syntax solution (closed term in meta scope, de Bruijn indexed).
    let syntax_sol = match pattern_quote(global, &rhs, &rename, &ambiguous, meta_id, arity, arity) {
        Ok(s) => s,
        Err(RenameError::Hard(e)) => return Err(e),
        Err(RenameError::Soft) => return Ok(false),
    };

    // Produce the value solution (for fast force_flex via subst_value).
    let value_sol = match rename_value(&rhs, &rename, &ambiguous, meta_id) {
        Ok(v) => v,
        Err(RenameError::Hard(e)) => return Err(e),
        Err(RenameError::Soft) => return Ok(false),
    };

    state.solve_meta(meta_id, syntax_sol, value_sol).map(|_| true)
}

// ─── Error type ──────────────────────────────────────────────────────────────

enum RenameError<'db> {
    Hard(ElabError<'db>),
    Soft,
}

// ─── pattern_quote: Value → Syntax in meta scope ─────────────────────────────

/// Traverse `val`, replacing outer-scope variables with their de Bruijn indices
/// in the meta's solution scope.
///
/// - `rename`: maps outer Level → meta-internal position (0 = first/outermost param)
/// - `ambiguous`: levels that appear non-linearly in the meta's args (soft-fail if seen in RHS)
/// - `arity`: number of meta params in the current (possibly extended) scope
/// - `outer_depth`: next fresh level to use when entering closures
///
/// Returns `Syntax` that, when wrapped in `arity` lambdas, is the closed solution term.
fn pattern_quote<'db>(
    global: &GlobalEnv<'db>,
    val: &Value<'db>,
    rename: &HashMap<Level, usize>,
    ambiguous: &HashSet<Level>,
    meta_id: MetaId,
    arity: usize,
    outer_depth: usize,
) -> Result<RcSyntax<'db>, RenameError<'db>> {
    match val {
        Value::Rigid(rigid) if rigid.spine.is_empty() => {
            let level = rigid.head.level;
            if ambiguous.contains(&level) {
                // Ambiguous variable in RHS: can't determine value (non-linear arg). Soft fail.
                return Err(RenameError::Soft);
            }
            match rename.get(&level) {
                Some(&pos) => Ok(Syntax::variable_rc(Index(arity - 1 - pos))),
                None => Err(RenameError::Hard(ElabError::ScopeViolation {
                    meta: meta_id,
                    span: None,
                })),
            }
        }
        Value::Rigid(_) => Err(RenameError::Soft), // non-empty spine not handled

        Value::Flex(flex) => {
            if MetaId(flex.head.id.local_index as u32) == meta_id {
                return Err(RenameError::Hard(ElabError::OccursCheck {
                    meta: meta_id,
                    span: None,
                }));
            }
            // Other unsolved flex: pruning not implemented, soft-fail.
            Err(RenameError::Soft)
        }

        Value::UniverseCode(n) => Ok(Rc::new(Syntax::UniverseCode(*n))),

        Value::Lambda(lam) => {
            let body_syn = pattern_quote_closure(
                global, &lam.body, rename, ambiguous, meta_id, arity, outer_depth,
            )?;
            Ok(Syntax::lambda_rc(Binding(body_syn)))
        }

        Value::PiCode(dom, cod) => {
            let dom_syn =
                pattern_quote(global, dom, rename, ambiguous, meta_id, arity, outer_depth)?;
            let cod_syn = pattern_quote_closure(
                global, cod, rename, ambiguous, meta_id, arity, outer_depth,
            )?;
            Ok(Rc::new(Syntax::PiCode(dom_syn, Binding(cod_syn))))
        }

        Value::LiftCode(n, inner) => {
            let inner_syn =
                pattern_quote(global, inner, rename, ambiguous, meta_id, arity, outer_depth)?;
            Ok(Rc::new(Syntax::LiftCode(*n, inner_syn)))
        }

        // Atomic closed values.
        Value::BitCode => Ok(Rc::new(Syntax::BitCode)),

        // Complex values not yet handled: soft fallback.
        _ => Err(RenameError::Soft),
    }
}

/// Quote a closure body: apply to a fresh variable, extend rename, recurse.
fn pattern_quote_closure<'db>(
    global: &GlobalEnv<'db>,
    clos: &Closure<'db>,
    rename: &HashMap<Level, usize>,
    ambiguous: &HashSet<Level>,
    meta_id: MetaId,
    arity: usize,
    outer_depth: usize,
) -> Result<RcSyntax<'db>, RenameError<'db>> {
    // Create a fresh variable at outer_depth (does not collide with rename keys).
    let fresh_ty: RcValue<'db> = Rc::new(Value::UniverseCode(0));
    let fresh_var: RcValue<'db> = Rc::new(Value::variable(Level::new(outer_depth), fresh_ty));

    // Apply the closure to the fresh variable.
    let mut body_local = clos.local.clone();
    body_local.push(fresh_var);
    let body_val = eval::substitute(global, &clos.term, body_local)
        .map_err(|_| RenameError::Soft)?;

    // Extend rename: the fresh variable's level → new meta param at position `arity`.
    let mut ext_rename = rename.clone();
    ext_rename.insert(Level::new(outer_depth), arity);

    pattern_quote(
        global,
        &body_val,
        &ext_rename,
        ambiguous,
        meta_id,
        arity + 1,
        outer_depth + 1,
    )
}

// ─── rename_value: Value → Value in meta scope (for force_flex caching) ──────

fn rename_value<'db>(
    val: &Value<'db>,
    rename: &HashMap<Level, usize>,
    ambiguous: &HashSet<Level>,
    meta_id: MetaId,
) -> Result<RcValue<'db>, RenameError<'db>> {
    match val {
        Value::Rigid(rigid) => {
            if !rigid.spine.is_empty() {
                return Err(RenameError::Soft);
            }
            let level = rigid.head.level;
            if ambiguous.contains(&level) {
                return Err(RenameError::Soft);
            }
            match rename.get(&level) {
                Some(&pos) => {
                    let new_ty = rename_value(&rigid.ty, rename, ambiguous, meta_id)?;
                    Ok(Rc::new(Value::variable(Level::new(pos), new_ty)))
                }
                None => Err(RenameError::Hard(ElabError::ScopeViolation {
                    meta: meta_id,
                    span: None,
                })),
            }
        }
        Value::Flex(flex) => {
            if MetaId(flex.head.id.local_index as u32) == meta_id {
                return Err(RenameError::Hard(ElabError::OccursCheck {
                    meta: meta_id,
                    span: None,
                }));
            }
            // Other metas: keep as-is (will be solved later).
            Ok(Rc::new(val.clone()))
        }
        Value::Lambda(lam) => {
            let new_clos = rename_closure(&lam.body, rename, ambiguous, meta_id)?;
            Ok(Value::lambda_rc(new_clos))
        }
        Value::PiCode(dom, cod) => {
            let new_dom = rename_value(dom, rename, ambiguous, meta_id)?;
            let new_cod = rename_closure(cod, rename, ambiguous, meta_id)?;
            Ok(Rc::new(Value::PiCode(new_dom, new_cod)))
        }
        Value::LiftCode(n, inner) => {
            let new_inner = rename_value(inner, rename, ambiguous, meta_id)?;
            Ok(Rc::new(Value::LiftCode(*n, new_inner)))
        }
        Value::TypeConstructor(tc) => {
            let new_args: Result<Vec<_>, _> =
                tc.iter().map(|a| rename_value(a, rename, ambiguous, meta_id)).collect();
            Ok(Rc::new(Value::TypeConstructor(TypeConstructor::new(
                tc.constructor,
                new_args?,
            ))))
        }
        Value::DataConstructor(dc) => {
            let new_args: Result<Vec<_>, _> =
                dc.iter().map(|a| rename_value(a, rename, ambiguous, meta_id)).collect();
            Ok(Rc::new(Value::DataConstructor(DataConstructor::new(
                dc.constructor,
                new_args?,
            ))))
        }
        Value::EqType(eq) => {
            let new_ty = rename_value(&eq.ty, rename, ambiguous, meta_id)?;
            let new_lhs = rename_value(&eq.lhs, rename, ambiguous, meta_id)?;
            let new_rhs = rename_value(&eq.rhs, rename, ambiguous, meta_id)?;
            Ok(Rc::new(Value::EqType(EqType::new(new_ty, new_lhs, new_rhs))))
        }
        // Atomic values with no variable occurrences.
        Value::UniverseCode(_)
        | Value::BitCode
        | Value::Refl(_)
        | Value::Constant(_)
        | Value::Prim(_)
        | Value::HardwareUniverse(_)
        | Value::SignalUniverse(_)
        | Value::ModuleUniverse(_)
        | Value::Bit(_)
        | Value::Zero(_)
        | Value::One(_) => Ok(Rc::new(val.clone())),
        // Complex values not yet handled: soft fallback.
        _ => Err(RenameError::Soft),
    }
}

fn rename_closure<'db>(
    clos: &Closure<'db>,
    rename: &HashMap<Level, usize>,
    ambiguous: &HashSet<Level>,
    meta_id: MetaId,
) -> Result<Closure<'db>, RenameError<'db>> {
    let mut new_local = LocalEnv::new();
    for i in 0..clos.local.depth() {
        let v = clos.local.get(Level::new(i));
        new_local.push(rename_value(v, rename, ambiguous, meta_id)?);
    }
    Ok(Closure::new(new_local, clos.term.clone()))
}
