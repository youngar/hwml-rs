use std::rc::Rc;

use hwml_core::{
    ty::{RcTy, Ty},
    Binding, RcSyntax, Syntax,
};
use hwml_surface::Expression;

use crate::{
    error::ElabError,
    kernel::{extract_binder_name, Checked, Kernel},
    meta::MetaKind,
    util::bytes_to_path,
};

use super::Elaborator;

/// Pull-mode: infer (term, type) for a surface expression.
pub fn synth<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    expr: &Expression,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>>
where
    Db: salsa::Database,
{
    match expr {
        Expression::Universe(_) => elab.kernel.synth_universe(None),
        Expression::Id(id) => {
            let name = String::from_utf8_lossy(&id.value).to_string();
            match elab.kernel.ctx.lookup(&name) {
                Some((idx, _)) => elab.kernel.synth_var(idx),
                None => {
                    // Use scoped name resolution (Resolver + StubTable).
                    let path = bytes_to_path(db, &id.value);
                    elab.kernel.synth_global_by_path(db, &path)
                }
            }
        }
        Expression::App(app) => {
            let mut elems = app.elements.iter();
            let fun_expr = elems.next().ok_or(ElabError::CannotInfer { span: None })?;
            let mut result = synth(db, elab, fun_expr)?;
            for arg in elems {
                result = elab.kernel.synth_app(db, result, arg)?;
            }
            Ok(result)
        }
        Expression::Pi(pi) => synth_pi(db, elab, pi),
        Expression::Arrow(arrow) => synth_arrow(db, elab, arrow),
        Expression::LetIn(let_in) => synth_let_in(db, elab, let_in),
        Expression::Underscore(_) => synth_underscore(elab),
        Expression::Paren(p) => synth(db, elab, &p.expr),
        _ => Err(ElabError::CannotInfer { span: None }),
    }
}

/// Push-mode: check expression against expected type.
pub fn check<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    expr: &Expression,
    expected_ty: RcTy<'db>,
) -> Result<Checked<RcSyntax<'db>>, ElabError<'db>>
where
    Db: salsa::Database,
{
    match expr {
        Expression::Fun(fun) => match elab.kernel.force_to_pi(expected_ty.clone()) {
            Ok((dom_code, cod_clos)) => elab.kernel.check_lambda(db, fun, dom_code, cod_clos),
            Err(_) => {
                let s = synth(db, elab, expr)?;
                Ok(elab.kernel.expect(expected_ty, s))
            }
        },
        _ => {
            let s = synth(db, elab, expr)?;
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
        elab.kernel
            .state
            .fresh_meta(Rc::new(Ty::UniverseType), depth, MetaKind::UniverseLevel);
    let (level_syn, _) = elab.kernel.synth_meta(level_id)?.into_inner();
    let level_val = elab
        .kernel
        .eval_syn(&level_syn)
        .map_err(|_| ElabError::CannotInfer { span: None })?;
    let term_ty: RcTy<'db> = Rc::new(Ty::El(level_val));
    let term_id = elab
        .kernel
        .state
        .fresh_meta(term_ty.clone(), depth, MetaKind::Term);
    let (term_syn, _) = elab.kernel.synth_meta(term_id)?.into_inner();
    Ok(Checked::new((term_syn, term_ty)))
}

// ─── Pi ──────────────────────────────────────────────────────────────────────

fn synth_pi<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    pi: &hwml_surface::Pi,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>>
where
    Db: salsa::Database,
{
    synth_pi_groups(db, elab, &pi.bindings.groups, &pi.target)
}

fn synth_pi_groups<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    groups: &[hwml_surface::TypedBindingGroup],
    target: &Expression,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>>
where
    Db: salsa::Database,
{
    if groups.is_empty() {
        let cod_syn = check(db, elab, target, Rc::new(Ty::UniverseType))?.into_inner();
        return Ok(Checked::new((cod_syn, Rc::new(Ty::UniverseType))));
    }
    let group = &groups[0];
    synth_pi_binders(db, elab, &group.binders, &group.ty, &groups[1..], target)
}

fn synth_pi_binders<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    binders: &[Box<Expression>],
    dom_ty_expr: &Expression,
    rest_groups: &[hwml_surface::TypedBindingGroup],
    target: &Expression,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>>
where
    Db: salsa::Database,
{
    if binders.is_empty() {
        return synth_pi_groups(db, elab, rest_groups, target);
    }

    let name = extract_binder_name(&binders[0]).unwrap_or_else(|| "_".to_string());
    let dom_syn = check(db, elab, dom_ty_expr, Rc::new(Ty::UniverseType))?.into_inner();
    let dom_code = elab.kernel.eval_syn_flex(&dom_syn);

    let dom_ty: RcTy<'db> = Rc::new(Ty::El(dom_code.clone()));
    let var = elab.kernel.ctx.fresh_var(dom_code.clone());
    let ext_ctx = elab.kernel.ctx.push_bound(name, dom_ty, var);

    let cod_checked = {
        let mut inner = Elaborator {
            kernel: Kernel {
                global: elab.kernel.global,
                ctx: ext_ctx,
                state: elab.kernel.state,
                resolver: elab.kernel.resolver,
                stub_table: elab.kernel.stub_table,
            },
        };
        // Re-check dom_ty_expr in extended ctx for proper de Bruijn shifts.
        synth_pi_binders(
            db,
            &mut inner,
            &binders[1..],
            dom_ty_expr,
            rest_groups,
            target,
        )?
    };

    let (cod_syn, _) = cod_checked.into_inner();
    let pi_syn: RcSyntax<'db> = Rc::new(Syntax::PiCode(dom_syn, Binding(cod_syn)));
    Ok(Checked::new((pi_syn, Rc::new(Ty::UniverseType))))
}

// ─── Arrow ───────────────────────────────────────────────────────────────────

fn synth_arrow<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    arrow: &hwml_surface::Arrow,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>>
where
    Db: salsa::Database,
{
    let dom_syn = check(db, elab, &arrow.source, Rc::new(Ty::UniverseType))?.into_inner();
    let dom_code = elab.kernel.eval_syn_flex(&dom_syn);

    let dom_ty: RcTy<'db> = Rc::new(Ty::El(dom_code.clone()));
    let var = elab.kernel.ctx.fresh_var(dom_code.clone());
    let ext_ctx = elab.kernel.ctx.push_bound("_".to_string(), dom_ty, var);

    let cod_syn = {
        let mut inner = Elaborator {
            kernel: Kernel {
                global: elab.kernel.global,
                ctx: ext_ctx,
                state: elab.kernel.state,
                resolver: elab.kernel.resolver,
                stub_table: elab.kernel.stub_table,
            },
        };
        check(db, &mut inner, &arrow.target, Rc::new(Ty::UniverseType))?.into_inner()
    };

    let pi_syn: RcSyntax<'db> = Rc::new(Syntax::PiCode(dom_syn, Binding(cod_syn)));
    Ok(Checked::new((pi_syn, Rc::new(Ty::UniverseType))))
}

// ─── Let ─────────────────────────────────────────────────────────────────────

fn synth_let_in<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    let_in: &hwml_surface::LetIn,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>>
where
    Db: salsa::Database,
{
    let name = String::from_utf8_lossy(&let_in.id.value).to_string();

    // Phase 2: require an explicit type annotation.
    let ty_expr = let_in
        .ty
        .as_deref()
        .ok_or(ElabError::CannotInfer { span: None })?;

    let ty_syn = check(db, elab, ty_expr, Rc::new(Ty::UniverseType))?.into_inner();
    let ty_code = elab.kernel.eval_syn_flex(&ty_syn);
    let ty: RcTy<'db> = Rc::new(Ty::El(ty_code.clone()));

    let val_syn = check(db, elab, &let_in.value, ty.clone())?.into_inner();
    let val_code = elab.kernel.eval_syn_flex(&val_syn);

    let ext_ctx = elab.kernel.ctx.push_let(name, ty, val_code);

    let (body_syn, body_ty) = {
        let mut inner = Elaborator {
            kernel: Kernel {
                global: elab.kernel.global,
                ctx: ext_ctx,
                state: elab.kernel.state,
                resolver: elab.kernel.resolver,
                stub_table: elab.kernel.stub_table,
            },
        };
        synth(db, &mut inner, &let_in.expr)?.into_inner()
    };

    let let_syn: RcSyntax<'db> = Rc::new(Syntax::let_expr(ty_syn, val_syn, Binding(body_syn)));
    Ok(Checked::new((let_syn, body_ty)))
}
