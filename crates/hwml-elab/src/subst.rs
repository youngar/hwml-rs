/// Value-level substitution for meta forcing.
///
/// When a meta `?m[x0..xn-1]` is solved to `sol` (in the meta's scope where
/// levels 0..n-1 are the parameters), forcing it with actual values `[v0..vn-1]`
/// requires substituting `level_i → v_i` for `i in 0..n-1`.
///
/// This module implements that substitution by walking a `Value`.
use std::rc::Rc;

use hwml_core::{
    RcValue, Value,
    eval::{self, run_spine},
    val::{
        Closure, DataConstructor, Eliminator, EqType, Flex, GlobalEnv, Lambda, LocalEnv, MetaVariable,
        Normal, Refl, Rigid, Spine, Transport, TypeConstructor, Variable,
    },
};

/// Substitute levels `0..local.depth()-1` throughout a value.
/// Levels >= local.depth() are free (from an outer context) and are unchanged.
pub fn subst_value<'db>(
    global: &GlobalEnv<'db>,
    val: &Value<'db>,
    local: &LocalEnv<'db>,
) -> Result<RcValue<'db>, eval::Error<'db>> {
    if local.depth() == 0 {
        return Ok(Rc::new(val.clone()));
    }
    match val {
        Value::Rigid(rigid) => subst_rigid(global, rigid, local),
        Value::Flex(flex) => subst_flex(global, flex, local),
        Value::Lambda(lam) => subst_lambda(global, lam, local),
        Value::PiCode(source, target) => {
            let new_source = subst_value(global, source, local)?;
            let new_target = subst_closure(target, local);
            Ok(Rc::new(Value::PiCode(new_source, new_target)))
        }
        Value::LiftCode(shift, inner) => {
            let new_inner = subst_value(global, inner, local)?;
            Ok(Rc::new(Value::LiftCode(*shift, new_inner)))
        }
        // Atomic values with no variable occurrences.
        Value::UniverseCode(_) | Value::BitCode => Ok(Rc::new(val.clone())),
        // Data/Type constructors may have argument lists.
        Value::TypeConstructor(tc) => {
            let new_args: Result<Vec<_>, _> =
                tc.iter().map(|a| subst_value(global, a, local)).collect();
            Ok(Rc::new(Value::TypeConstructor(TypeConstructor::new(
                tc.constructor,
                new_args?,
            ))))
        }
        Value::DataConstructor(dc) => {
            let new_args: Result<Vec<_>, _> =
                dc.iter().map(|a| subst_value(global, a, local)).collect();
            Ok(Rc::new(Value::DataConstructor(DataConstructor::new(
                dc.constructor,
                new_args?,
            ))))
        }
        Value::EqType(eq) => {
            let new_ty = subst_value(global, &eq.ty, local)?;
            let new_lhs = subst_value(global, &eq.lhs, local)?;
            let new_rhs = subst_value(global, &eq.rhs, local)?;
            Ok(Rc::new(Value::EqType(EqType::new(new_ty, new_lhs, new_rhs))))
        }
        Value::Refl(_) => Ok(Rc::new(val.clone())), // Refl has no value fields
        Value::Transport(t) => {
            let new_motive = subst_closure(&t.motive, local);
            let new_proof = subst_value(global, &t.proof, local)?;
            let new_value = subst_value(global, &t.value, local)?;
            Ok(Rc::new(Value::Transport(Transport::new(new_motive, new_proof, new_value))))
        }
        // For other values that may contain types/values, substitute conservatively.
        _ => Ok(Rc::new(val.clone())),
    }
}

fn subst_rigid<'db>(
    global: &GlobalEnv<'db>,
    rigid: &Rigid<'db>,
    local: &LocalEnv<'db>,
) -> Result<RcValue<'db>, eval::Error<'db>> {
    let level = rigid.head.level;
    let subst_spine = subst_spine_vals(global, &rigid.spine, local)?;
    if level.0 < local.depth() {
        // Level is in the substitution range: replace with actual value.
        let head_val = local.get(level).clone();
        run_spine(global, head_val, &subst_spine)
    } else {
        // Outer free variable: keep level, substitute in spine and ty.
        let new_ty = subst_value(global, &rigid.ty, local)?;
        Ok(Rc::new(Value::Rigid(Rigid::new(
            Variable::new(level),
            subst_spine,
            new_ty,
        ))))
    }
}

fn subst_flex<'db>(
    global: &GlobalEnv<'db>,
    flex: &Flex<'db>,
    local: &LocalEnv<'db>,
) -> Result<RcValue<'db>, eval::Error<'db>> {
    let new_inner = subst_local_env(global, &flex.head.local, local)?;
    let new_spine = subst_spine_vals(global, &flex.spine, local)?;
    let new_ty = subst_value(global, &flex.ty, local)?;
    let new_head = MetaVariable::new(flex.head.id, new_inner);
    Ok(Rc::new(Value::Flex(Flex::new(new_head, new_spine, new_ty))))
}

fn subst_lambda<'db>(
    _global: &GlobalEnv<'db>,
    lam: &Lambda<'db>,
    local: &LocalEnv<'db>,
) -> Result<RcValue<'db>, eval::Error<'db>> {
    let new_closure = subst_closure(&lam.body, local);
    Ok(Value::lambda_rc(new_closure))
}

/// Substitute into a Closure by substituting its captured local environment.
/// The term is left unchanged (it's syntax with de Bruijn indices, not levels).
fn subst_closure<'db>(clos: &Closure<'db>, local: &LocalEnv<'db>) -> Closure<'db> {
    let mut new_local = LocalEnv::new();
    for i in 0..clos.local.depth() {
        let v = clos.local.get(hwml_core::Level::new(i));
        if let Ok(new_v) = subst_value_no_fail(v, local) {
            new_local.push(new_v);
        } else {
            new_local.push(v.clone());
        }
    }
    Closure::new(new_local, clos.term.clone())
}

/// Substitute throughout all values in a LocalEnv.
pub fn subst_local_env<'db>(
    global: &GlobalEnv<'db>,
    inner: &LocalEnv<'db>,
    outer: &LocalEnv<'db>,
) -> Result<LocalEnv<'db>, eval::Error<'db>> {
    let mut new_local = LocalEnv::new();
    for i in 0..inner.depth() {
        let v = inner.get(hwml_core::Level::new(i));
        new_local.push(subst_value(global, v, outer)?);
    }
    Ok(new_local)
}

fn subst_spine_vals<'db>(
    global: &GlobalEnv<'db>,
    spine: &Spine<'db>,
    local: &LocalEnv<'db>,
) -> Result<Spine<'db>, eval::Error<'db>> {
    let mut new_elims = Vec::with_capacity(spine.len());
    for elim in spine.iter() {
        match elim {
            Eliminator::Application(app) => {
                let new_ty = subst_value(global, &app.argument.ty, local)?;
                let new_val = subst_value(global, &app.argument.value, local)?;
                new_elims.push(Eliminator::application(Normal::new(new_ty, new_val)));
            }
            Eliminator::Case(_) => {
                // Case branches contain closures; substitute them.
                // For Phase 2, clone as-is (conservative; correct for closed case branches).
                new_elims.push(elim.clone());
            }
        }
    }
    Ok(Spine::new(new_elims))
}

/// Infallible version of subst_value (clones on failure).
fn subst_value_no_fail<'db>(val: &Value<'db>, local: &LocalEnv<'db>) -> Result<RcValue<'db>, ()> {
    // We need a GlobalEnv for run_spine; use a dummy substitution for closure locals.
    // This is only called for closure-local values which are typically rigid vars.
    match val {
        Value::Rigid(rigid) if rigid.spine.is_empty() && rigid.head.level.0 < local.depth() => {
            Ok(local.get(rigid.head.level).clone())
        }
        _ => Ok(Rc::new(val.clone())),
    }
}
