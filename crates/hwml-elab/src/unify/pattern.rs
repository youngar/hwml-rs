use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

use hwml_core::{
    Binding, Index, Level, MetaVariableId, RcSyntax, RcValue, Syntax, Value,
    ty::{RcTy, Ty},
    val::{Closure, DataConstructor, EqType, Eliminator, Flex, GlobalEnv, LocalEnv, Normal, Rigid,
          Spine, TypeConstructor, Variable},
    eval,
};

use crate::{
    error::ElabError,
    meta::{MetaId, MetaKind},
    state::SolverState,
    unify::{intersection_syntax_solution, intersection_value_solution},
};

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
    let syntax_sol = match pattern_quote(global, state, &rhs, &rename, &ambiguous, meta_id, arity, arity) {
        Ok(s) => s,
        Err(RenameError::Hard(e)) => return Err(e),
        Err(RenameError::Soft) => return Ok(false),
    };

    // Produce the value solution (for fast force_flex via subst_value).
    let value_sol = match rename_value(global, state, &rhs, &rename, &ambiguous, meta_id) {
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
fn pattern_quote<'db>(
    global: &GlobalEnv<'db>,
    state: &mut SolverState<'db>,
    val: &Value<'db>,
    rename: &HashMap<Level, usize>,
    ambiguous: &HashSet<Level>,
    meta_id: MetaId,
    arity: usize,
    outer_depth: usize,
) -> Result<RcSyntax<'db>, RenameError<'db>> {
    match val {
        // ── Gap 4: Rigid with empty spine (variable) ──
        Value::Rigid(rigid) if rigid.spine.is_empty() => {
            let level = rigid.head.level;
            if ambiguous.contains(&level) {
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

        // ── Gap 4: Rigid with non-empty spine (lowering) ──
        Value::Rigid(rigid) => {
            let level = rigid.head.level;
            if ambiguous.contains(&level) {
                return Err(RenameError::Soft);
            }
            let &pos = match rename.get(&level) {
                Some(p) => p,
                None => return Err(RenameError::Hard(ElabError::ScopeViolation {
                    meta: meta_id,
                    span: None,
                })),
            };
            let mut result = Syntax::variable_rc(Index(arity - 1 - pos));
            for elim in rigid.spine.iter() {
                match elim {
                    Eliminator::Application(app) => {
                        let arg_syn = pattern_quote(
                            global, state, &app.argument.value,
                            rename, ambiguous, meta_id, arity, outer_depth,
                        )?;
                        result = Syntax::application_rc(result, arg_syn);
                    }
                    _ => return Err(RenameError::Soft),
                }
            }
            Ok(result)
        }

        // ── Gap 3: Flex (pruning) ──
        Value::Flex(flex2) => {
            let flex2_id = MetaId(flex2.head.id.local_index as u32);
            if flex2_id == meta_id {
                return Err(RenameError::Hard(ElabError::OccursCheck {
                    meta: meta_id,
                    span: None,
                }));
            }
            // If solved: force and recurse.
            let forced = state.force_flex(global, flex2);
            if let Some(forced_val) = forced {
                return pattern_quote(
                    global, state, &forced_val,
                    rename, ambiguous, meta_id, arity, outer_depth,
                );
            }
            // Only handle empty spine (can't prune with non-empty spine).
            if !flex2.spine.is_empty() {
                return Err(RenameError::Soft);
            }
            prune_flex_quote(global, state, flex2, flex2_id, rename, ambiguous, meta_id, arity)
        }

        Value::UniverseCode(n) => Ok(Rc::new(Syntax::UniverseCode(*n))),

        Value::Lambda(lam) => {
            let body_syn = pattern_quote_closure(
                global, state, &lam.body, rename, ambiguous, meta_id, arity, outer_depth,
            )?;
            Ok(Syntax::lambda_rc(Binding(body_syn)))
        }

        Value::PiCode(dom, cod) => {
            let dom_syn =
                pattern_quote(global, state, dom, rename, ambiguous, meta_id, arity, outer_depth)?;
            let cod_syn = pattern_quote_closure(
                global, state, cod, rename, ambiguous, meta_id, arity, outer_depth,
            )?;
            Ok(Rc::new(Syntax::PiCode(dom_syn, Binding(cod_syn))))
        }

        Value::LiftCode(n, inner) => {
            let inner_syn =
                pattern_quote(global, state, inner, rename, ambiguous, meta_id, arity, outer_depth)?;
            Ok(Rc::new(Syntax::LiftCode(*n, inner_syn)))
        }

        Value::BitCode => Ok(Rc::new(Syntax::BitCode)),

        _ => Err(RenameError::Soft),
    }
}

/// Quote a closure body: apply to a fresh variable, extend rename, recurse.
fn pattern_quote_closure<'db>(
    global: &GlobalEnv<'db>,
    state: &mut SolverState<'db>,
    clos: &Closure<'db>,
    rename: &HashMap<Level, usize>,
    ambiguous: &HashSet<Level>,
    meta_id: MetaId,
    arity: usize,
    outer_depth: usize,
) -> Result<RcSyntax<'db>, RenameError<'db>> {
    let fresh_ty: RcValue<'db> = Rc::new(Value::UniverseCode(0));
    let fresh_var: RcValue<'db> = Rc::new(Value::variable(Level::new(outer_depth), fresh_ty));

    let mut body_local = clos.local.clone();
    body_local.push(fresh_var);
    let body_val = eval::substitute(global, &clos.term, body_local)
        .map_err(|_| RenameError::Soft)?;

    let mut ext_rename = rename.clone();
    ext_rename.insert(Level::new(outer_depth), arity);

    pattern_quote(
        global,
        state,
        &body_val,
        &ext_rename,
        ambiguous,
        meta_id,
        arity + 1,
        outer_depth + 1,
    )
}

// ─── Gap 3: prune a flex meta encountered in the RHS ─────────────────────────

/// Prune `flex2` so only its args that are in scope of `?meta_id` remain.
/// Creates a fresh `?m'`, solves `flex2 ← λ(n). ?m'[kept]`, and returns the
/// syntax for `?m'[renamed_kept_args]` in meta scope.
fn prune_flex_quote<'db>(
    _global: &GlobalEnv<'db>,
    state: &mut SolverState<'db>,
    flex2: &Flex<'db>,
    flex2_id: MetaId,
    rename: &HashMap<Level, usize>,
    ambiguous: &HashSet<Level>,
    _meta_id: MetaId,
    arity: usize,
) -> Result<RcSyntax<'db>, RenameError<'db>> {
    let flex2_arity = flex2.head.local.depth();

    // Determine which positions of flex2's args are in scope of ?meta_id.
    let mut kept: Vec<usize> = Vec::new();
    for i in 0..flex2_arity {
        let arg = flex2.head.local.get(Level::new(i));
        if let Value::Rigid(rigid) = arg.as_ref() {
            if rigid.spine.is_empty() {
                let level = rigid.head.level;
                if !ambiguous.contains(&level) && rename.contains_key(&level) {
                    kept.push(i);
                    continue;
                }
            }
        }
        // Out of scope or non-variable: prune this position.
    }

    // If all args are in scope, rename them and keep ?flex2 unsolved.
    let meta_vid = MetaVariableId::new(flex2_id.0 as u16);
    let mut renamed_args: Vec<RcSyntax<'db>> = Vec::new();
    for &k in &kept {
        let arg = flex2.head.local.get(Level::new(k));
        if let Value::Rigid(rigid) = arg.as_ref() {
            let &pos = rename.get(&rigid.head.level).unwrap();
            renamed_args.push(Syntax::variable_rc(Index(arity - 1 - pos)));
        }
    }
    if kept.len() == flex2_arity {
        // All args in scope: no pruning needed.
        return Ok(Syntax::metavariable_rc(meta_vid, renamed_args));
    }

    // Some args out of scope: create ?m' and solve ?flex2 ← λ(n). ?m'[kept].
    let dummy_ty: RcTy<'db> = Rc::new(Ty::UniverseType);
    let new_meta_id = state.fresh_meta(dummy_ty, kept.len(), MetaKind::Term);

    let syn_sol = intersection_syntax_solution(new_meta_id, flex2_arity, &kept);
    let val_sol = intersection_value_solution(new_meta_id, &kept);
    state.solve_meta(flex2_id, syn_sol, val_sol)
        .map_err(RenameError::Hard)?;

    // Produce syntax for ?m'[renamed kept args] in meta scope.
    let new_meta_vid = MetaVariableId::new(new_meta_id.0 as u16);
    Ok(Syntax::metavariable_rc(new_meta_vid, renamed_args))
}

// ─── rename_value: Value → Value in meta scope (for force_flex caching) ──────

fn rename_value<'db>(
    global: &GlobalEnv<'db>,
    state: &mut SolverState<'db>,
    val: &Value<'db>,
    rename: &HashMap<Level, usize>,
    ambiguous: &HashSet<Level>,
    meta_id: MetaId,
) -> Result<RcValue<'db>, RenameError<'db>> {
    match val {
        // ── Gap 4: Rigid variable (empty spine) ──
        Value::Rigid(rigid) if rigid.spine.is_empty() => {
            let level = rigid.head.level;
            if ambiguous.contains(&level) {
                return Err(RenameError::Soft);
            }
            match rename.get(&level) {
                Some(&pos) => {
                    let new_ty = rename_value(global, state, &rigid.ty, rename, ambiguous, meta_id)?;
                    Ok(Rc::new(Value::variable(Level::new(pos), new_ty)))
                }
                None => Err(RenameError::Hard(ElabError::ScopeViolation {
                    meta: meta_id,
                    span: None,
                })),
            }
        }

        // ── Gap 4: Rigid with spine (lowering) ──
        Value::Rigid(rigid) => {
            let level = rigid.head.level;
            if ambiguous.contains(&level) {
                return Err(RenameError::Soft);
            }
            let &pos = match rename.get(&level) {
                Some(p) => p,
                None => return Err(RenameError::Hard(ElabError::ScopeViolation {
                    meta: meta_id,
                    span: None,
                })),
            };
            let new_ty = rename_value(global, state, &rigid.ty, rename, ambiguous, meta_id)?;
            // Rebuild spine with renamed args.
            let mut new_elims = Vec::with_capacity(rigid.spine.len());
            for elim in rigid.spine.iter() {
                match elim {
                    Eliminator::Application(app) => {
                        let new_arg_ty =
                            rename_value(global, state, &app.argument.ty, rename, ambiguous, meta_id)?;
                        let new_arg_val =
                            rename_value(global, state, &app.argument.value, rename, ambiguous, meta_id)?;
                        new_elims.push(Eliminator::application(Normal::new(new_arg_ty, new_arg_val)));
                    }
                    _ => return Err(RenameError::Soft),
                }
            }
            let new_spine = Spine::new(new_elims);
            Ok(Rc::new(Value::Rigid(Rigid::new(
                Variable::new(Level::new(pos)),
                new_spine,
                new_ty,
            ))))
        }

        // ── Gap 3: Flex meta (pruning) ──
        Value::Flex(flex2) => {
            let flex2_id = MetaId(flex2.head.id.local_index as u32);
            if flex2_id == meta_id {
                return Err(RenameError::Hard(ElabError::OccursCheck {
                    meta: meta_id,
                    span: None,
                }));
            }
            // If solved: force and recurse.
            let forced = state.force_flex(global, flex2);
            if let Some(forced_val) = forced {
                return rename_value(global, state, &forced_val, rename, ambiguous, meta_id);
            }
            if !flex2.spine.is_empty() {
                return Err(RenameError::Soft);
            }
            prune_flex_rename(state, flex2, flex2_id, rename, ambiguous, meta_id)
        }

        Value::Lambda(lam) => {
            let new_clos = rename_closure(global, state, &lam.body, rename, ambiguous, meta_id)?;
            Ok(Value::lambda_rc(new_clos))
        }
        Value::PiCode(dom, cod) => {
            let new_dom = rename_value(global, state, dom, rename, ambiguous, meta_id)?;
            let new_cod = rename_closure(global, state, cod, rename, ambiguous, meta_id)?;
            Ok(Rc::new(Value::PiCode(new_dom, new_cod)))
        }
        Value::LiftCode(n, inner) => {
            let new_inner = rename_value(global, state, inner, rename, ambiguous, meta_id)?;
            Ok(Rc::new(Value::LiftCode(*n, new_inner)))
        }
        Value::TypeConstructor(tc) => {
            let new_args: Result<Vec<_>, _> =
                tc.iter().map(|a| rename_value(global, state, a, rename, ambiguous, meta_id)).collect();
            Ok(Rc::new(Value::TypeConstructor(TypeConstructor::new(tc.constructor, new_args?))))
        }
        Value::DataConstructor(dc) => {
            let new_args: Result<Vec<_>, _> =
                dc.iter().map(|a| rename_value(global, state, a, rename, ambiguous, meta_id)).collect();
            Ok(Rc::new(Value::DataConstructor(DataConstructor::new(dc.constructor, new_args?))))
        }
        Value::EqType(eq) => {
            let new_ty = rename_value(global, state, &eq.ty, rename, ambiguous, meta_id)?;
            let new_lhs = rename_value(global, state, &eq.lhs, rename, ambiguous, meta_id)?;
            let new_rhs = rename_value(global, state, &eq.rhs, rename, ambiguous, meta_id)?;
            Ok(Rc::new(Value::EqType(EqType::new(new_ty, new_lhs, new_rhs))))
        }
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
        _ => Err(RenameError::Soft),
    }
}

/// Prune `flex2` (value side): same logic as `prune_flex_quote` but returns a `RcValue`.
fn prune_flex_rename<'db>(
    state: &mut SolverState<'db>,
    flex2: &Flex<'db>,
    flex2_id: MetaId,
    rename: &HashMap<Level, usize>,
    ambiguous: &HashSet<Level>,
    _meta_id: MetaId,
) -> Result<RcValue<'db>, RenameError<'db>> {
    let flex2_arity = flex2.head.local.depth();

    let mut kept: Vec<usize> = Vec::new();
    for i in 0..flex2_arity {
        let arg = flex2.head.local.get(Level::new(i));
        if let Value::Rigid(rigid) = arg.as_ref() {
            if rigid.spine.is_empty() {
                let level = rigid.head.level;
                if !ambiguous.contains(&level) && rename.contains_key(&level) {
                    kept.push(i);
                    continue;
                }
            }
        }
    }

    let dummy_val: RcValue<'db> = Rc::new(Value::UniverseCode(0));

    // Collect renamed args (level positions in meta scope).
    let meta_vid = MetaVariableId::new(flex2_id.0 as u16);
    let mut renamed_local = LocalEnv::new();
    for &k in &kept {
        let arg = flex2.head.local.get(Level::new(k));
        if let Value::Rigid(rigid) = arg.as_ref() {
            let &pos = rename.get(&rigid.head.level).unwrap();
            renamed_local.push(Rc::new(Value::variable(Level::new(pos), dummy_val.clone())));
        }
    }
    if kept.len() == flex2_arity {
        // All args in scope: keep ?flex2 unsolved, just rename its local.
        return Ok(Rc::new(Value::Flex(Flex::new(
            hwml_core::val::MetaVariable::new(meta_vid, renamed_local),
            Spine::empty(),
            dummy_val,
        ))));
    }

    // Some args out of scope: create ?m' and solve ?flex2 ← λ(n). ?m'[kept].
    let dummy_ty: RcTy<'db> = Rc::new(Ty::UniverseType);
    let new_meta_id = state.fresh_meta(dummy_ty, kept.len(), MetaKind::Term);

    let syn_sol = intersection_syntax_solution(new_meta_id, flex2_arity, &kept);
    let val_sol = intersection_value_solution(new_meta_id, &kept);
    state.solve_meta(flex2_id, syn_sol, val_sol)
        .map_err(RenameError::Hard)?;

    let new_meta_vid = MetaVariableId::new(new_meta_id.0 as u16);
    Ok(Rc::new(Value::Flex(Flex::new(
        hwml_core::val::MetaVariable::new(new_meta_vid, renamed_local),
        Spine::empty(),
        dummy_val,
    ))))
}

fn rename_closure<'db>(
    global: &GlobalEnv<'db>,
    state: &mut SolverState<'db>,
    clos: &Closure<'db>,
    rename: &HashMap<Level, usize>,
    ambiguous: &HashSet<Level>,
    meta_id: MetaId,
) -> Result<Closure<'db>, RenameError<'db>> {
    let mut new_local = LocalEnv::new();
    for i in 0..clos.local.depth() {
        let v = clos.local.get(Level::new(i));
        new_local.push(rename_value(global, state, v, rename, ambiguous, meta_id)?);
    }
    Ok(Closure::new(new_local, clos.term.clone()))
}
