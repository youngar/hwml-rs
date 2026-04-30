use std::rc::Rc;

use hwml_core::{Binding, RcSyntax, Syntax, ty::{RcTy, Ty}};
use hwml_surface::Expression;

use crate::{
    error::ElabError,
    kernel::{Checked, Kernel, extract_binder_name},
    meta::MetaKind,
};

use super::Elaborator;

/// Pull-mode: infer (term, type) for a surface expression.
pub fn synth<'a, 'db>(
    elab: &mut Elaborator<'a, 'db>,
    expr: &Expression,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
    match expr {
        Expression::Universe(_) => elab.kernel.synth_universe(None),
        Expression::Id(id) => {
            let name = String::from_utf8_lossy(&id.value).to_string();
            match elab.kernel.ctx.lookup(&name) {
                Some((idx, _)) => elab.kernel.synth_var(idx),
                None => {
                    // Fall back to global name table (constants, primitives, type constructors).
                    match elab.kernel.synth_global_by_bytes(&id.value) {
                        Some(result) => result,
                        None => Err(ElabError::NotInScope { name, span: None }),
                    }
                }
            }
        }
        Expression::App(app) => {
            let mut elems = app.elements.iter();
            let fun_expr = elems.next().ok_or(ElabError::CannotInfer { span: None })?;
            let mut result = synth(elab, fun_expr)?;
            for arg in elems {
                result = elab.kernel.synth_app(result, arg)?;
            }
            Ok(result)
        }
        Expression::Pi(pi) => synth_pi(elab, pi),
        Expression::Arrow(arrow) => synth_arrow(elab, arrow),
        Expression::LetIn(let_in) => synth_let_in(elab, let_in),
        Expression::Underscore(_) => synth_underscore(elab),
        Expression::Paren(p) => synth(elab, &p.expr),
        _ => Err(ElabError::CannotInfer { span: None }),
    }
}

/// Push-mode: check expression against expected type.
pub fn check<'a, 'db>(
    elab: &mut Elaborator<'a, 'db>,
    expr: &Expression,
    expected_ty: RcTy<'db>,
) -> Result<Checked<RcSyntax<'db>>, ElabError<'db>> {
    match expr {
        Expression::Fun(fun) => {
            match elab.kernel.force_to_pi(expected_ty.clone()) {
                Ok((dom_code, cod_clos)) => elab.kernel.check_lambda(fun, dom_code, cod_clos),
                Err(_) => {
                    let s = synth(elab, expr)?;
                    Ok(elab.kernel.expect(expected_ty, s))
                }
            }
        }
        _ => {
            let s = synth(elab, expr)?;
            Ok(elab.kernel.expect(expected_ty, s))
        }
    }
}

// ─── Underscore ──────────────────────────────────────────────────────────────

fn synth_underscore<'a, 'db>(
    elab: &mut Elaborator<'a, 'db>,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
    let depth = elab.kernel.ctx.depth();
    let level_id =
        elab.kernel.state.fresh_meta(Rc::new(Ty::UniverseType), depth, MetaKind::UniverseLevel);
    let (level_syn, _) = elab.kernel.synth_meta(level_id)?.into_inner();
    let level_val = elab.kernel.eval_syn(&level_syn)
        .map_err(|_| ElabError::CannotInfer { span: None })?;
    let term_ty: RcTy<'db> = Rc::new(Ty::El(level_val));
    let term_id = elab.kernel.state.fresh_meta(term_ty.clone(), depth, MetaKind::Term);
    let (term_syn, _) = elab.kernel.synth_meta(term_id)?.into_inner();
    Ok(Checked::new((term_syn, term_ty)))
}

// ─── Pi ──────────────────────────────────────────────────────────────────────

fn synth_pi<'a, 'db>(
    elab: &mut Elaborator<'a, 'db>,
    pi: &hwml_surface::Pi,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
    synth_pi_groups(elab, &pi.bindings.groups, &pi.target)
}

fn synth_pi_groups<'a, 'db>(
    elab: &mut Elaborator<'a, 'db>,
    groups: &[hwml_surface::TypedBindingGroup],
    target: &Expression,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
    if groups.is_empty() {
        let cod_syn = check(elab, target, Rc::new(Ty::UniverseType))?.into_inner();
        return Ok(Checked::new((cod_syn, Rc::new(Ty::UniverseType))));
    }
    let group = &groups[0];
    synth_pi_binders(elab, &group.binders, &group.ty, &groups[1..], target)
}

fn synth_pi_binders<'a, 'db>(
    elab: &mut Elaborator<'a, 'db>,
    binders: &[Box<Expression>],
    dom_ty_expr: &Expression,
    rest_groups: &[hwml_surface::TypedBindingGroup],
    target: &Expression,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
    if binders.is_empty() {
        return synth_pi_groups(elab, rest_groups, target);
    }

    let name = extract_binder_name(&binders[0]).unwrap_or_else(|| "_".to_string());
    let dom_syn = check(elab, dom_ty_expr, Rc::new(Ty::UniverseType))?.into_inner();
    let dom_code = elab.kernel.eval_syn_flex(&dom_syn);

    let dom_ty: RcTy<'db> = Rc::new(Ty::El(dom_code.clone()));
    let var = elab.kernel.ctx.fresh_var(dom_code.clone());
    let ext_ctx = elab.kernel.ctx.push_bound(name, dom_ty, var);

    let cod_checked = {
        let mut inner = Elaborator {
            kernel: Kernel { global: elab.kernel.global, ctx: ext_ctx, state: elab.kernel.state, global_names: elab.kernel.global_names.clone() },
        };
        // Re-check dom_ty_expr in extended ctx for proper de Bruijn shifts.
        synth_pi_binders(&mut inner, &binders[1..], dom_ty_expr, rest_groups, target)?
    };

    let (cod_syn, _) = cod_checked.into_inner();
    let pi_syn: RcSyntax<'db> = Rc::new(Syntax::PiCode(dom_syn, Binding(cod_syn)));
    Ok(Checked::new((pi_syn, Rc::new(Ty::UniverseType))))
}

// ─── Arrow ───────────────────────────────────────────────────────────────────

fn synth_arrow<'a, 'db>(
    elab: &mut Elaborator<'a, 'db>,
    arrow: &hwml_surface::Arrow,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
    let dom_syn = check(elab, &arrow.source, Rc::new(Ty::UniverseType))?.into_inner();
    let dom_code = elab.kernel.eval_syn_flex(&dom_syn);

    let dom_ty: RcTy<'db> = Rc::new(Ty::El(dom_code.clone()));
    let var = elab.kernel.ctx.fresh_var(dom_code.clone());
    let ext_ctx = elab.kernel.ctx.push_bound("_".to_string(), dom_ty, var);

    let cod_syn = {
        let mut inner = Elaborator {
            kernel: Kernel { global: elab.kernel.global, ctx: ext_ctx, state: elab.kernel.state, global_names: elab.kernel.global_names.clone() },
        };
        check(&mut inner, &arrow.target, Rc::new(Ty::UniverseType))?.into_inner()
    };

    let pi_syn: RcSyntax<'db> = Rc::new(Syntax::PiCode(dom_syn, Binding(cod_syn)));
    Ok(Checked::new((pi_syn, Rc::new(Ty::UniverseType))))
}

// ─── Let ─────────────────────────────────────────────────────────────────────

fn synth_let_in<'a, 'db>(
    elab: &mut Elaborator<'a, 'db>,
    let_in: &hwml_surface::LetIn,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
    let name = String::from_utf8_lossy(&let_in.id.value).to_string();

    // Phase 2: require an explicit type annotation.
    let ty_expr = let_in.ty.as_deref().ok_or(ElabError::CannotInfer { span: None })?;

    let ty_syn = check(elab, ty_expr, Rc::new(Ty::UniverseType))?.into_inner();
    let ty_code = elab.kernel.eval_syn_flex(&ty_syn);
    let ty: RcTy<'db> = Rc::new(Ty::El(ty_code.clone()));

    let val_syn = check(elab, &let_in.value, ty.clone())?.into_inner();
    let val_code = elab.kernel.eval_syn_flex(&val_syn);

    let ext_ctx = elab.kernel.ctx.push_let(name, ty, val_code);

    let (body_syn, body_ty) = {
        let mut inner = Elaborator {
            kernel: Kernel { global: elab.kernel.global, ctx: ext_ctx, state: elab.kernel.state, global_names: elab.kernel.global_names.clone() },
        };
        synth(&mut inner, &let_in.expr)?.into_inner()
    };

    let let_syn: RcSyntax<'db> = Rc::new(Syntax::let_expr(ty_syn, val_syn, Binding(body_syn)));
    Ok(Checked::new((let_syn, body_ty)))
}
