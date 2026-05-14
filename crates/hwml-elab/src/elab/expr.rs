use std::{ops::Range, rc::Rc};

use hwml_core::{
    common::Icit,
    ty::{RcTy, Ty},
    Binding, Name, RcSyntax, Syntax, Value,
};
use hwml_support::FromWithDb;
use hwml_surface::Expression;

use crate::{
    context::ElabFrameKind,
    error::ElabError,
    kernel::{extract_binder_name, Checked, Kernel},
    meta::{MetaId, MetaKind},
};

use super::Elaborator;

/// Extract the byte range from an expression.
///
/// This is used for source location tracking in elaboration traces.
fn expr_loc(expr: &Expression) -> Range<usize> {
    match expr {
        Expression::Pi(pi) => pi.loc.clone(),
        Expression::Arrow(arrow) => arrow.loc.clone(),
        Expression::FatArrow(fat_arrow) => fat_arrow.loc.clone(),
        Expression::App(app) => app.loc.clone(),
        Expression::Fun(fun) => fun.loc.clone(),
        Expression::LetIn(let_in) => let_in.loc.clone(),
        Expression::Match(m) => {
            // Match doesn't have a loc field, so use scrutinee's location
            expr_loc(&m.scrutinee)
        }
        Expression::TypeAscription(asc) => asc.loc.clone(),
        Expression::Underscore(underscore) => underscore.loc.clone(),
        Expression::Paren(paren) => expr_loc(&paren.expr),
        Expression::Num(num) => num.loc.clone(),
        Expression::Str(_str) => {
            // Str doesn't have a loc field, use 0..0 as placeholder
            0..0
        }
        Expression::Id(id) => id.loc.clone(),
        Expression::Universe(universe) => universe.loc.clone(),
        Expression::Dot(dot) => dot.loc.clone(),
        Expression::Error(err) => err.loc.clone(),
        Expression::Hole(hole) => hole.loc.clone(),
    }
}

/// Get a short description of an expression for diagnostic messages.
fn expr_description(expr: &Expression) -> String {
    match expr {
        Expression::Pi(_) => "function type (Pi)".to_string(),
        Expression::Arrow(_) => "arrow type".to_string(),
        Expression::FatArrow(_) => "hardware arrow type".to_string(),
        Expression::App(app) => {
            // Try to show the function being applied (first element)
            if let Some(first) = app.elements.first() {
                if let Expression::Id(id) = &**first {
                    format!("application of '{}'", id.value)
                } else {
                    "function application".to_string()
                }
            } else {
                "function application".to_string()
            }
        }
        Expression::Fun(_) => "lambda function".to_string(),
        Expression::LetIn(_) => "let expression".to_string(),
        Expression::Match(_) => "match expression".to_string(),
        Expression::TypeAscription(_) => "type ascription".to_string(),
        Expression::Underscore(_) => "underscore placeholder".to_string(),
        Expression::Paren(paren) => expr_description(&paren.expr),
        Expression::Num(n) => format!("number literal {}", n.value),
        Expression::Str(s) => format!("string literal {:?}", s.value),
        Expression::Id(id) => format!("identifier '{}'", id.value),
        Expression::Universe(u) => {
            if let Some(level) = u.level {
                format!("Type {}", level)
            } else {
                "Type".to_string()
            }
        }
        Expression::Dot(_) => "dot expression".to_string(),
        Expression::Error(err) => format!("error: {}", err.message),
        Expression::Hole(hole) => {
            if let Some(name) = &hole.name {
                format!("hole ?{}", name)
            } else {
                "hole".to_string()
            }
        }
    }
}

/// Helper to create a SourceRange from an expression and the current elaboration context.
///
/// This is used when creating errors to capture the source location.
fn expr_span<'db>(
    elab: &Elaborator<'_, 'db>,
    expr: &Expression,
) -> Option<hwml_core::SourceRange<'db>> {
    Some(hwml_core::SourceRange::new(
        elab.context.source(),
        expr_loc(expr),
    ))
}

/// Check if a type is meta-headed (DOE helper).
///
/// Returns `Some(MetaId)` if the type is headed by an unsolved metavariable,
/// `None` otherwise.
///
/// A type is meta-headed when it's `Ty::El(Flex(?m, ...))` where `?m` is unsolved.
/// This is used to detect when we need to postpone type-checking for DOE.
fn is_meta_headed<'db>(ty: &RcTy<'db>) -> Option<MetaId> {
    match ty.as_ref() {
        Ty::El(val) => match val.as_ref() {
            Value::Flex(flex) => Some(MetaId(flex.head.id.local_index as u32)),
            _ => None,
        },
        _ => None,
    }
}

/// Helper to enrich an error with span and backtrace information if missing.
///
/// This is called when an error bubbles up from the kernel or unification,
/// which don't have access to surface syntax locations.
fn enrich_error<'db>(
    mut err: ElabError<'db>,
    elab: &Elaborator<'_, 'db>,
    expr: &Expression,
) -> ElabError<'db> {
    use crate::error::ElabError;

    // If the error doesn't have a span, add one from the current expression
    let needs_span = err.span().is_none();
    let needs_backtrace = err.backtrace().is_empty();

    if needs_span || needs_backtrace {
        let span = if needs_span {
            expr_span(elab, expr)
        } else {
            err.span().cloned()
        };
        let backtrace = if needs_backtrace {
            elab.context.snapshot()
        } else {
            err.backtrace().to_vec()
        };

        // Reconstruct the error with populated fields
        match err {
            ElabError::TypeMismatch {
                expected, actual, ..
            } => ElabError::TypeMismatch {
                expected,
                actual,
                span,
                elab_backtrace: backtrace,
            },
            ElabError::UnificationFailure { lhs, rhs, .. } => ElabError::UnificationFailure {
                lhs,
                rhs,
                span,
                elab_backtrace: backtrace,
            },
            ElabError::OccursCheck { meta, .. } => ElabError::OccursCheck {
                meta,
                span,
                elab_backtrace: backtrace,
            },
            ElabError::ScopeViolation { meta, .. } => ElabError::ScopeViolation {
                meta,
                span,
                elab_backtrace: backtrace,
            },
            // Other error types already have their spans set or don't need enrichment
            other => other,
        }
    } else {
        err
    }
}

/// Helper function to synthesize a dot expression: `receiver.field_name`
/// This handles the type-directed resolution logic.
fn synth_dot<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    receiver_syn: RcSyntax<'db>,
    receiver_ty: RcTy<'db>,
    field_name: Name<'db>,
    dot_loc: Option<hwml_core::SourceRange<'db>>,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>>
where
    Db: salsa::Database,
{
    let depth = elab.kernel.ctx.depth();

    // Create fresh metavariables for the result
    let result_ty_code_meta = if let Some(loc) = dot_loc.clone() {
        elab.kernel.state.fresh_meta_with_provenance(
            Rc::new(Ty::UniverseType),
            depth,
            MetaKind::UniverseLevel,
            loc.clone(),
            format!(
                "dot resolution for field '{}' at {:?}",
                field_name.to_string(db),
                loc
            ),
        )
    } else {
        elab.kernel
            .state
            .fresh_meta(Rc::new(Ty::UniverseType), depth, MetaKind::UniverseLevel)
    };
    let (result_ty_code_syn, _) = elab.kernel.synth_meta(result_ty_code_meta)?.into_inner();
    let result_ty_code = elab.kernel.eval_syn_flex(&result_ty_code_syn);
    let result_ty: RcTy<'db> = Rc::new(Ty::El(result_ty_code));

    let result_val_meta = if let Some(loc) = dot_loc.clone() {
        elab.kernel.state.fresh_meta_with_provenance(
            result_ty.clone(),
            depth,
            MetaKind::Term,
            loc.clone(),
            format!(
                "dot resolution for field '{}' at {:?}",
                field_name.to_string(db),
                loc
            ),
        )
    } else {
        elab.kernel
            .state
            .fresh_meta(result_ty.clone(), depth, MetaKind::Term)
    };
    let (result_syn, _) = elab.kernel.synth_meta(result_val_meta)?.into_inner();

    // Emit the ResolveDot constraint
    elab.kernel.state.emit_resolve_dot(
        receiver_syn,
        receiver_ty,
        field_name,
        result_val_meta,
        result_ty_code_meta,
        depth,
    );

    // CRITICAL FIX FOR BUG #3: Pump Solver Immediately
    //
    // For chained dot resolution like `r.field1.field2`, we must solve constraints
    // incrementally. If we don't run the solver here, the constraint for `field1`
    // won't be resolved before we try to elaborate `field2`.
    //
    // Example: r.field1.field2
    //   1. Synth r → MyRecord
    //   2. Emit ResolveDot(MyRecord, "field1", ?M1)
    //   3. **SOLVE NOW** → ?M1 = SomeType
    //   4. Synth .field2 on ?M1
    //   5. Emit ResolveDot(SomeType, "field2", ?M2)  // Only works if ?M1 is solved!
    //
    // We use a lenient solver (doesn't error on NoProgress) because during
    // mutual recursion, some constraints might be blocked on other declarations.
    crate::elab::decl::run_solver_lenient(db, elab)?;

    Ok(Checked::new((result_syn, result_ty)))
}

/// Pull-mode: infer (term, type) for a surface expression.
pub fn synth<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    expr: &Expression,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>>
where
    Db: salsa::Database,
{
    // Phase 4.3: Push trace frame with actual source location and expression description
    let desc = expr_description(expr);
    elab.push_trace(
        format!("synthesizing type for {}", desc),
        expr_loc(expr),
        ElabFrameKind::SynthesizingType,
    );

    let result = synth_impl(db, elab, expr);

    // Pop trace frame
    elab.pop_trace();

    // Enrich errors with span and backtrace if missing
    result.map_err(|err| enrich_error(err, elab, expr))
}

/// Internal implementation of synth (separated to ensure pop_trace is always called)
fn synth_impl<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    expr: &Expression,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>>
where
    Db: salsa::Database,
{
    match expr {
        Expression::Universe(u) => {
            let source = elab.context.source();
            let loc = hwml_core::SourceRange::new(source, u.loc.clone());
            elab.kernel.synth_universe(None, Some(loc))
        }
        Expression::Id(id) => {
            let name = &*id.value;

            eprintln!("[EXPR] Synthesizing identifier: {}", name);

            // Try local context first
            if let Some((idx, _)) = elab.kernel.ctx.lookup(name) {
                eprintln!(
                    "[EXPR] Found '{}' in local context at index {:?}",
                    name, idx
                );
                return elab.kernel.synth_var(idx);
            }

            eprintln!(
                "[EXPR] '{}' not found in local context, trying global resolution",
                name
            );

            // Try global resolution
            match crate::util::str_to_path(db, &id.value) {
                Ok(path) => {
                    eprintln!(
                        "[EXPR] Converted '{}' to path with {} segments",
                        name,
                        path.len()
                    );
                    match elab.kernel.synth_global_by_path(db, &path) {
                        Ok(result) => {
                            eprintln!("[EXPR] Successfully resolved '{}' globally", name);
                            return Ok(result);
                        }
                        Err(e) => {
                            eprintln!("[EXPR] Global resolution failed for '{}': {:?}", name, e);
                        }
                    }
                }
                Err(e) => {
                    eprintln!("[EXPR] Malformed identifier '{}': {:?}", name, e);
                }
            }

            // Check if this is a dotted identifier like "x.foo" or "x.foo.bar"
            if let Some(dot_pos) = id.value.find('.') {
                let receiver_name = &id.value[..dot_pos];

                // Check if the first segment is a local variable
                if let Some((idx, _)) = elab.kernel.ctx.lookup(receiver_name) {
                    // Split segments: ["x", "foo", "bar", ...]
                    let segments: Vec<&str> = id.value.split('.').collect();

                    // Start with the receiver
                    let (mut current_syn, mut current_ty) =
                        elab.kernel.synth_var(idx)?.into_inner();

                    // Chain through all field accesses
                    for field_str in &segments[1..] {
                        let field_name = hwml_core::str_to_name(db, *field_str)
                            .expect("Lexer should prevent malformed field names");
                        // Note: We don't have individual location info for each segment in "x.foo.bar"
                        let result =
                            synth_dot(db, elab, current_syn, current_ty, field_name, None)?;
                        let (syn, ty) = result.into_inner();
                        current_syn = syn;
                        current_ty = ty;
                    }

                    return Ok(Checked::new((current_syn, current_ty)));
                }
            }

            // If all resolution attempts fail, return a helpful error
            if id.value.contains('.') {
                let segments: Vec<&str> = name.split('.').collect();
                Err(ElabError::NotInScope {
                    name: format!(
                        "Unknown identifier '{}'. If you intended this as a field access, the receiver '{}' is not in scope.",
                        name, segments[0]
                    ),
                    span: Some(hwml_core::SourceRange::new(
                        elab.context.source(),
                        id.loc.clone(),
                    )),
                    elab_backtrace: Vec::new(),
                })
            } else {
                Err(ElabError::NotInScope {
                    name: name.to_string(),
                    span: Some(hwml_core::SourceRange::new(
                        elab.context.source(),
                        id.loc.clone(),
                    )),
                    elab_backtrace: Vec::new(),
                })
            }
        }
        Expression::Dot(dot) => {
            // Elaborate receiver
            let (receiver_syn, receiver_ty) = synth_impl(db, elab, &dot.receiver)?.into_inner();
            // Extract field name
            let word = hwml_core::Word::new(db, &*dot.field.value);
            let atom = hwml_core::Atom::new(word);
            let field_name = Name::new(db, hwml_core::Fixity::Closed, Box::from([atom]));
            let source = elab.context.source();
            let dot_loc = hwml_core::SourceRange::new(source, dot.loc.clone());
            synth_dot(
                db,
                elab,
                receiver_syn,
                receiver_ty,
                field_name,
                Some(dot_loc),
            )
        }
        Expression::App(app) => {
            let mut elems = app.elements.iter();
            let fun_expr = elems.next().ok_or(ElabError::CannotInfer {
                span: expr_span(elab, expr),
                elab_backtrace: elab.context.snapshot(),
            })?;
            let mut result = synth_impl(db, elab, fun_expr)?;
            for arg in elems {
                result = elab
                    .kernel
                    .synth_app(db, result, arg, elab.context.source())?;
            }
            Ok(result)
        }
        Expression::Pi(pi) => synth_pi(db, elab, pi),
        Expression::Arrow(arrow) => synth_arrow(db, elab, arrow),
        Expression::LetIn(let_in) => synth_let_in(db, elab, let_in),
        Expression::Underscore(underscore) => synth_underscore(elab, underscore),
        Expression::Paren(p) => synth_impl(db, elab, &p.expr),
        _ => Err(ElabError::CannotInfer {
            span: expr_span(elab, expr),
            elab_backtrace: elab.context.snapshot(),
        }),
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
    // Phase 4.3: Push trace frame with actual source location and expression description
    let desc = expr_description(expr);
    elab.push_trace(
        format!("checking {} against expected type", desc),
        expr_loc(expr),
        ElabFrameKind::CheckingExpression,
    );

    let result = check_impl(db, elab, expr, expected_ty);

    // Pop trace frame
    elab.pop_trace();

    // Enrich errors with span and backtrace if missing
    result.map_err(|err| enrich_error(err, elab, expr))
}

/// Internal implementation of check (separated to ensure pop_trace is always called)
fn check_impl<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    expr: &Expression,
    expected_ty: RcTy<'db>,
) -> Result<Checked<RcSyntax<'db>>, ElabError<'db>>
where
    Db: salsa::Database,
{
    // DOE (Dynamic Order Elaboration): Postpone lambda checks when type is meta-headed
    //
    // Key insight: We only postpone checks for LAMBDAS, because those are the only
    // expressions where we might need to insert implicit lambdas based on the type.
    // For other expressions (like `Type`, numbers, etc.), we can just switch to synth mode.
    //
    // The solver will collect ready checks and return them as Vec<ReadyCheck>.
    // The caller (run_solver in decl.rs) processes them by creating elaborators
    // and running the checks, then solving the placeholder metas.
    if matches!(expr, Expression::Fun(_)) {
        if let Some(meta_id) = is_meta_headed(&expected_ty) {
            let depth = elab.kernel.ctx.depth();

            // Create a placeholder meta that will be solved to the checked result
            let placeholder =
                elab.kernel
                    .state
                    .fresh_meta(expected_ty.clone(), depth, MetaKind::Term);

            // Emit the PostponedCheck constraint
            let cid = elab.kernel.state.emit_postponed_check(
                Box::new(expr.clone()),
                expected_ty.clone(),
                elab.kernel.ctx.clone(),
                placeholder,
                depth,
            );

            // Block the constraint on the meta
            elab.kernel.state.block_on(cid, &[meta_id]);

            // Return the placeholder as a "promise" for the result
            let (placeholder_syn, _placeholder_ty) =
                elab.kernel.synth_meta(placeholder)?.into_inner();
            return Ok(Checked::new(placeholder_syn));
        }
    }

    // Normal checking: type is not meta-headed
    match expr {
        Expression::Fun(fun) => match elab.kernel.force_to_pi(expected_ty.clone()) {
            Ok((dom_code, icit, cod_clos)) => {
                elab.kernel
                    .check_lambda(db, fun, dom_code, icit, cod_clos, elab.context.source())
            }
            Err(_) => {
                // Switch to synth mode (the "switch rule")
                let desc = expr_description(expr);
                elab.push_trace(
                    format!("switching to synthesis for {}", desc),
                    expr_loc(expr),
                    ElabFrameKind::SwitchingToSynth,
                );
                let result = synth_impl(db, elab, expr);
                elab.pop_trace();

                let s = result?;
                let loc = elab.context.current_location();
                Ok(elab.kernel.expect_with_loc(expected_ty, s, loc))
            }
        },
        _ => {
            // Switch to synth mode (the "switch rule")
            let desc = expr_description(expr);
            elab.push_trace(
                format!("switching to synthesis for {}", desc),
                expr_loc(expr),
                ElabFrameKind::SwitchingToSynth,
            );
            let result = synth_impl(db, elab, expr);
            elab.pop_trace();

            let s = result?;
            let loc = elab.context.current_location();
            Ok(elab.kernel.expect_with_loc(expected_ty, s, loc))
        }
    }
}

// ─── Underscore ──────────────────────────────────────────────────────────────

fn synth_underscore<'a, 'db>(
    elab: &mut Elaborator<'a, 'db>,
    underscore: &hwml_surface::Underscore,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
    let depth = elab.kernel.ctx.depth();
    let source = elab.context.source();
    let loc = hwml_core::SourceRange::new(source, underscore.loc.clone());

    let level_id = elab.kernel.state.fresh_meta_with_provenance(
        Rc::new(Ty::UniverseType),
        depth,
        MetaKind::UniverseLevel,
        loc.clone(),
        format!("underscore placeholder at {:?}", underscore.loc),
    );
    let (level_syn, _) = elab.kernel.synth_meta(level_id)?.into_inner();
    let level_val = elab
        .kernel
        .eval_syn(&level_syn)
        .map_err(|_| ElabError::CannotInfer {
            span: Some(loc.clone()),
            elab_backtrace: elab.context.snapshot(),
        })?;
    let term_ty: RcTy<'db> = Rc::new(Ty::El(level_val));
    let term_id = elab.kernel.state.fresh_meta_with_provenance(
        term_ty.clone(),
        depth,
        MetaKind::Term,
        loc.clone(),
        format!("underscore placeholder at {:?}", underscore.loc),
    );
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
    synth_pi_binders(
        db,
        elab,
        &group.binders,
        &group.ty,
        group.icit,
        &groups[1..],
        target,
    )
}

fn synth_pi_binders<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    binders: &[hwml_surface::Binder],
    dom_ty_expr: &Expression,
    icit: Icit,
    rest_groups: &[hwml_surface::TypedBindingGroup],
    target: &Expression,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>>
where
    Db: salsa::Database,
{
    if binders.is_empty() {
        return synth_pi_groups(db, elab, rest_groups, target);
    }

    let name_str = extract_binder_name(&binders[0]).unwrap_or_else(|| "_".to_string());
    let dom_syn = check(db, elab, dom_ty_expr, Rc::new(Ty::UniverseType))?.into_inner();
    let dom_code = elab.kernel.eval_syn_flex(&dom_syn);

    let dom_ty: RcTy<'db> = Rc::new(Ty::El(dom_code.clone()));
    let var = elab.kernel.ctx.fresh_var(dom_code.clone());
    let ext_ctx = elab.kernel.ctx.push_bound(name_str.clone(), dom_ty, var);

    let cod_checked = {
        let mut inner = Elaborator {
            kernel: Kernel {
                global: elab.kernel.global,
                ctx: ext_ctx,
                state: elab.kernel.state,
                resolver: elab.kernel.resolver,
                stub_table: elab.kernel.stub_table,
            },
            context: elab.context.clone(),
        };
        // Re-check dom_ty_expr in extended ctx for proper de Bruijn shifts.
        synth_pi_binders(
            db,
            &mut inner,
            &binders[1..],
            dom_ty_expr,
            icit,
            rest_groups,
            target,
        )?
    };

    let (cod_syn, _) = cod_checked.into_inner();
    let binder_name = if name_str == "_" {
        Name::anonymous(db)
    } else {
        Name::from_with_db(db, name_str)
    };
    let pi_syn: RcSyntax<'db> = Rc::new(Syntax::PiCode(
        dom_syn,
        icit,
        Binding::new(binder_name, cod_syn),
    ));
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
            context: elab.context.clone(),
        };
        check(db, &mut inner, &arrow.target, Rc::new(Ty::UniverseType))?.into_inner()
    };

    let pi_syn: RcSyntax<'db> = Rc::new(Syntax::PiCode(
        dom_syn,
        Icit::Explicit,
        Binding::new(Name::anonymous(db), cod_syn),
    ));
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
    let name_str = let_in.id.value.to_string();

    // Phase 2: require an explicit type annotation.
    let ty_expr = let_in.ty.as_deref().ok_or(ElabError::CannotInfer {
        span: Some(hwml_core::SourceRange::new(
            elab.context.source(),
            let_in.loc.clone(),
        )),
        elab_backtrace: elab.context.snapshot(),
    })?;

    let ty_syn = check(db, elab, ty_expr, Rc::new(Ty::UniverseType))?.into_inner();
    let ty_code = elab.kernel.eval_syn_flex(&ty_syn);
    let ty: RcTy<'db> = Rc::new(Ty::El(ty_code.clone()));

    let val_syn = check(db, elab, &let_in.value, ty.clone())?.into_inner();
    let val_code = elab.kernel.eval_syn_flex(&val_syn);

    let ext_ctx = elab.kernel.ctx.push_let(name_str.clone(), ty, val_code);

    let (body_syn, body_ty) = {
        let mut inner = Elaborator {
            kernel: Kernel {
                global: elab.kernel.global,
                ctx: ext_ctx,
                state: elab.kernel.state,
                resolver: elab.kernel.resolver,
                stub_table: elab.kernel.stub_table,
            },
            context: elab.context.clone(),
        };
        synth(db, &mut inner, &let_in.expr)?.into_inner()
    };

    let binder_name = Name::from_with_db(db, name_str);
    let let_syn: RcSyntax<'db> = Rc::new(Syntax::let_expr(
        ty_syn,
        val_syn,
        Binding::new(binder_name, body_syn),
    ));
    Ok(Checked::new((let_syn, body_ty)))
}
