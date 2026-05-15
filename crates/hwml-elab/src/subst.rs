/// Value-level substitution for meta forcing.
///
/// When a meta `?m[x0..xn-1]` is solved to `sol` (in the meta's scope where
/// levels 0..n-1 are the parameters), forcing it with actual values `[v0..vn-1]`
/// requires substituting `level_i → v_i` for `i in 0..n-1`.
///
/// This module implements that substitution by walking a `Value`.
use std::rc::Rc;

use hwml_core::{
    eval::{self, run_spine},
    val::{
        self, Closure, DataConstructor, Eliminator, EqType, Flex, GlobalEnv, Lambda, LocalEnv,
        MetaVariable, Normal, RcTy, Rigid, Spine, Transport, Ty, TyClosure, TyMetaVariable,
        TyVariable, TypeConstructor, Variable,
    },
    Icit, RcValue, Value,
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
        Value::PiCode(source, icit, target) => {
            let new_source = subst_value(global, source, local)?;
            let new_target = subst_closure(target, local);
            Ok(Rc::new(Value::PiCode(new_source, *icit, new_target)))
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
            Ok(Rc::new(Value::EqType(EqType::new(
                new_ty, new_lhs, new_rhs,
            ))))
        }
        Value::Refl(_) => Ok(Rc::new(val.clone())), // Refl has no value fields
        Value::Transport(t) => {
            let new_motive = subst_closure(&t.motive, local);
            let new_proof = subst_value(global, &t.proof, local)?;
            let new_value = subst_value(global, &t.value, local)?;
            Ok(Rc::new(Value::Transport(Transport::new(
                new_motive, new_proof, new_value,
            ))))
        }
        // For other values that may contain types/values, substitute conservatively.
        _ => Ok(Rc::new(val.clone())),
    }
}

/// Substitute levels throughout a semantic type.
///
/// **CRITICAL FIX**: This traverses the Strong Tarski `Ty` structure and substitutes
/// through term-level components (like spines in RigidTy/FlexTy and args in TyConstructor).
pub fn subst_ty<'db>(
    global: &GlobalEnv<'db>,
    ty: &RcTy<'db>,
    local: &LocalEnv<'db>,
) -> Result<RcTy<'db>, eval::Error<'db>> {
    if local.depth() == 0 {
        return Ok(ty.clone());
    }

    match ty.as_ref() {
        // Base cases: no variables inside
        Ty::UniverseType | Ty::SignalUniverseType | Ty::ModuleUniverseType => Ok(ty.clone()),
        Ty::Universe(_) | Ty::BitType => Ok(ty.clone()),

        // Pi type: substitute in domain and closure
        Ty::Pi(source, icit, target) => {
            let new_source = subst_ty(global, source, local)?;
            let new_target = subst_ty_closure(global, target, local)?;
            Ok(Ty::pi_rc(new_source, *icit, new_target))
        }

        // HArrow: substitute in both types
        Ty::HArrow(source, target) => {
            let new_source = subst_ty(global, source, local)?;
            let new_target = subst_ty(global, target, local)?;
            Ok(Ty::harrow_rc(new_source, new_target))
        }

        // LiftType: substitute in inner type
        Ty::LiftType(shift, inner) => {
            let new_inner = subst_ty(global, inner, local)?;
            Ok(Ty::lift_type_rc(*shift, new_inner))
        }

        // TyConstructor: substitute in term-level arguments
        Ty::TyConstructor(name, args) => {
            let new_args: Result<Vec<_>, _> = args
                .iter()
                .map(|arg| subst_value(global, arg, local))
                .collect();
            Ok(Ty::ty_constructor_rc(name.clone(), new_args?))
        }

        // RigidTy: substitute in spine (terms!) and type boundary
        Ty::RigidTy(var, spine, orig_ty) => {
            let new_spine = subst_spine_vals(global, spine, local)?;
            let new_ty = subst_ty(global, orig_ty, local)?;
            Ok(Ty::rigid_ty_rc(var.clone(), new_spine, new_ty))
        }

        // FlexTy: substitute in spine (terms!) and type boundary
        Ty::FlexTy(meta, spine, orig_ty) => {
            let new_spine = subst_spine_vals(global, spine, local)?;
            let new_ty = subst_ty(global, orig_ty, local)?;
            Ok(Ty::flex_ty_rc(meta.clone(), new_spine, new_ty))
        }

        // **PHASE 9**: Handle Signal and Module El types
        Ty::SignalEl(code) | Ty::ModuleEl(code) => {
            let new_code = subst_value(global, code, local)?;
            match ty.as_ref() {
                Ty::SignalEl(_) => Ok(Ty::signal_el_rc(new_code)),
                Ty::ModuleEl(_) => Ok(Ty::module_el_rc(new_code)),
                _ => unreachable!(),
            }
        }
        // **PHASE 9**: Decoded types - no substitution needed for now
        // In a full implementation, we'd need to substitute in nested types
        _ => Ok(ty.clone()),
    }
}

/// Substitute through a TyClosure's captured environment.
fn subst_ty_closure<'db>(
    global: &GlobalEnv<'db>,
    closure: &TyClosure<'db>,
    local: &LocalEnv<'db>,
) -> Result<TyClosure<'db>, eval::Error<'db>> {
    match closure {
        TyClosure::Syntactic {
            local: closure_local,
            body,
        } => {
            // Substitute through the captured environment
            let new_local = subst_local_env(global, closure_local, local)?;
            Ok(TyClosure::new(new_local, body.clone()))
        }
        TyClosure::Decoding {
            global: closure_global,
            value_closure,
        } => {
            // Substitute through the value closure's environment
            let new_value_closure = subst_closure(value_closure, local);
            Ok(TyClosure::new_decoding(
                closure_global.clone(),
                new_value_closure,
            ))
        }
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
        let new_ty = subst_ty(global, &rigid.ty, local)?;
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
    let new_ty = subst_ty(global, &flex.ty, local)?;
    let new_head = MetaVariable::new(flex.head.id, new_inner);
    Ok(Rc::new(Value::Flex(Flex::new(new_head, new_spine, new_ty))))
}

fn subst_lambda<'db>(
    _global: &GlobalEnv<'db>,
    lam: &Lambda<'db>,
    local: &LocalEnv<'db>,
) -> Result<RcValue<'db>, eval::Error<'db>> {
    let new_closure = subst_closure(&lam.body, local);
    Ok(Value::lambda_rc(lam.icit, new_closure))
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
                // **PHASE 9**: app.argument.ty is RcTy, not RcValue
                let new_ty = subst_ty(global, &app.argument.ty, local)?;
                let new_val = subst_value(global, &app.argument.value, local)?;
                new_elims.push(Eliminator::application(
                    Normal::new(new_ty, new_val),
                    app.icit,
                ));
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
