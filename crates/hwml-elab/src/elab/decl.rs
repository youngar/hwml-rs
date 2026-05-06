use std::rc::Rc;

use hwml_core::{
    eval,
    ty::Ty,
    val::{Environment, GlobalEnv},
    RcSyntax, Syntax,
};
use hwml_surface::{BindingGroup, Def, Inductive, TypedBindingGroup};

use crate::{
    elab::{self, Elaborator},
    error::ElabError,
    solver::{SolveError, Solver},
    state::SolverState,
    zonk::zonk,
};

// ─── Result types ─────────────────────────────────────────────────────────────

/// Elaborated constant (type-checked type and value).
#[derive(Debug, Clone)]
pub struct ElaboratedConstant<'db> {
    pub name: Vec<u8>,
    pub ty: RcSyntax<'db>,
    pub value: RcSyntax<'db>,
}

/// Elaborated data constructor.
#[derive(Debug, Clone)]
pub struct ElaboratedConstructor<'db> {
    pub name: Vec<u8>,
    /// Parameter types (telescope).
    pub params: Vec<RcSyntax<'db>>,
    /// Return type of the constructor.
    pub result: RcSyntax<'db>,
}

/// Elaborated inductive type declaration.
#[derive(Debug, Clone)]
pub struct ElaboratedInductive<'db> {
    pub name: Vec<u8>,
    /// Type parameters (telescope).
    pub params: Vec<RcSyntax<'db>>,
    /// Index types (telescope).
    pub indices: Vec<RcSyntax<'db>>,
    /// Universe expression.
    pub universe: RcSyntax<'db>,
    pub constructors: Vec<ElaboratedConstructor<'db>>,
}

// ─── Top-level elaboration entry points ───────────────────────────────────────

/// Elaborate a surface `def` declaration.
///
/// Handles:
/// - `def f : T = v` — no bindings, explicit type
/// - `def f (x:A) ... : T = v` — typed bindings desugared to Pi/Lambda
/// - `def f = v` — no annotation, infer type
///
/// Runs the constraint solver (strict mode) after elaboration. Does NOT run zonk (caller decides when).
pub fn elab_constant<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    def: &Def,
) -> Result<ElaboratedConstant<'db>, ElabError<'db>>
where
    Db: salsa::Database,
{
    elab_constant_impl(db, elab, def, false)
}

/// Elaborate a constant in lenient mode (for use during mutual recursion).
///
/// Same as `elab_constant`, but uses lenient solver that tolerates `NoProgress`.
pub fn elab_constant_lenient<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    def: &Def,
) -> Result<ElaboratedConstant<'db>, ElabError<'db>>
where
    Db: salsa::Database,
{
    elab_constant_impl(db, elab, def, true)
}

/// Internal implementation of constant elaboration.
fn elab_constant_impl<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    def: &Def,
    lenient: bool,
) -> Result<ElaboratedConstant<'db>, ElabError<'db>>
where
    Db: salsa::Database,
{
    let name = def.id.value.to_vec();

    // CRITICAL: Push the constant's namespace for ALL elaboration (type and value).
    // This matches the pattern used in elab_inductive_impl.
    // For example, `def Foo.myFunc : Type = helper`
    // - We enter namespace Foo.myFunc
    // - Type and value expressions see this namespace
    // - Bare `helper` references resolve by walking up to parent `Foo` → finds `Foo.helper`
    let def_path = crate::util::surface_id_to_path(db, &def.id).ok_or(ElabError::NotInScope {
        name: String::from_utf8_lossy(&def.id.value).to_string(),
        span: None,
    })?;

    // Push a namespace scope for the constant
    let def_resolver = elab.kernel.resolver.push_namespace(db, &def_path);

    // Elaborate type and value expressions in the constant's namespace
    let (ty_syn, value_syn) = {
        let mut inner = Elaborator {
            kernel: crate::kernel::Kernel::new(
                elab.kernel.global,
                elab.kernel.ctx.clone(),
                elab.kernel.state,
                &def_resolver,
                elab.kernel.stub_table,
            ),
        };

        if def.bindings.groups.is_empty() {
            // No bindings: simple case.
            match &def.ty {
                Some(ty_expr) => {
                    let ty_syn =
                        elab::expr::check(db, &mut inner, ty_expr, Rc::new(Ty::UniverseType))?
                            .into_inner();
                    let ty_code = inner.kernel.eval_syn_flex(&ty_syn);
                    let val_syn =
                        elab::expr::check(db, &mut inner, &def.value, Rc::new(Ty::El(ty_code)))?
                            .into_inner();
                    (ty_syn, val_syn)
                }
                None => {
                    // No annotation: synth the value, get its type.
                    let (val_syn, val_ty) =
                        elab::expr::synth(db, &mut inner, &def.value)?.into_inner();
                    let ty_syn = quote_type(&mut inner, &val_ty)?;
                    (ty_syn, val_syn)
                }
            }
        } else {
            // Has bindings: desugar into Pi + Fun.
            let typed_groups = collect_typed_groups(&def.bindings.groups);

            let ty_syn = match &def.ty {
                Some(ty_expr) => {
                    if typed_groups.is_empty() {
                        // Only untyped binders: check the declared type, use Fun for value.
                        elab::expr::check(db, &mut inner, ty_expr, Rc::new(Ty::UniverseType))?
                            .into_inner()
                    } else {
                        // Pi type from typed bindings + target.
                        let pi = build_pi_expr(typed_groups, ty_expr);
                        elab::expr::check(
                            db,
                            &mut inner,
                            &hwml_surface::Expression::Pi(pi),
                            Rc::new(Ty::UniverseType),
                        )?
                        .into_inner()
                    }
                }
                None => return Err(ElabError::CannotInfer { span: None }),
            };

            let ty_code = inner.kernel.eval_syn_flex(&ty_syn);
            let fun_expr = build_fun_expr(&def.bindings.groups, &def.value);
            let val_syn = elab::expr::check(db, &mut inner, &fun_expr, Rc::new(Ty::El(ty_code)))?
                .into_inner();

            (ty_syn, val_syn)
        }
    };

    // Run solver based on mode
    if lenient {
        run_solver_lenient(db, elab)?;
    } else {
        run_solver(db, elab)?;
    }

    Ok(ElaboratedConstant {
        name,
        ty: ty_syn,
        value: value_syn,
    })
}

/// Elaborate a surface `inductive` declaration.
///
/// Runs the constraint solver (strict mode) after elaboration. Does NOT run zonk.
pub fn elab_inductive<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    ind: &Inductive,
) -> Result<ElaboratedInductive<'db>, ElabError<'db>>
where
    Db: salsa::Database,
{
    elab_inductive_impl(db, elab, ind, false)
}

/// Elaborate an inductive in lenient mode (for use during mutual recursion).
///
/// Same as `elab_inductive`, but uses lenient solver that tolerates `NoProgress`.
pub fn elab_inductive_lenient<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    ind: &Inductive,
) -> Result<ElaboratedInductive<'db>, ElabError<'db>>
where
    Db: salsa::Database,
{
    elab_inductive_impl(db, elab, ind, true)
}

/// Internal implementation of inductive elaboration.
fn elab_inductive_impl<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    ind: &Inductive,
    lenient: bool,
) -> Result<ElaboratedInductive<'db>, ElabError<'db>>
where
    Db: salsa::Database,
{
    let name = ind.name.value.to_vec();

    // CRITICAL: Push the inductive type's namespace for ALL elaboration (params, indices, universe, constructors).
    // For example, `inductive Std.Vec (A : Type) : (n : Nat) -> Type`
    // - We enter namespace Std.Vec
    // - Parameters, indices, and constructors all see this namespace
    // - Bare `Nat` references resolve by walking up to parent `Std` → finds `Std.Nat`
    // This differs slightly from Lean but provides consistent scoping.
    let ind_path = crate::util::surface_id_to_path(db, &ind.name).ok_or(ElabError::NotInScope {
        name: String::from_utf8_lossy(&ind.name.value).to_string(),
        span: None,
    })?;

    // Push a namespace scope for the inductive type
    let ind_resolver = elab.kernel.resolver.push_namespace(db, &ind_path);

    // Elaborate parameters in the inductive's namespace.
    let (params, param_ctx) = {
        let mut inner = Elaborator {
            kernel: crate::kernel::Kernel::new(
                elab.kernel.global,
                elab.kernel.ctx.clone(),
                elab.kernel.state,
                &ind_resolver,
                elab.kernel.stub_table,
            ),
        };
        elab_telescope(db, &mut inner, &ind.parameters.groups)?
    };

    // Elaborate indices in the extended param context (still in inductive's namespace).
    let (indices, _idx_ctx) = {
        let mut inner = Elaborator {
            kernel: crate::kernel::Kernel::new(
                elab.kernel.global,
                param_ctx.clone(),
                elab.kernel.state,
                &ind_resolver,
                elab.kernel.stub_table,
            ),
        };
        elab_telescope(db, &mut inner, &ind.indices.groups)?
    };

    // Elaborate universe in the param+index context (still in inductive's namespace).
    let universe_syn = {
        let mut inner = Elaborator {
            kernel: crate::kernel::Kernel::new(
                elab.kernel.global,
                param_ctx.clone(),
                elab.kernel.state,
                &ind_resolver,
                elab.kernel.stub_table,
            ),
        };
        elab::expr::check(db, &mut inner, &ind.universe, Rc::new(Ty::UniverseType))?.into_inner()
    };

    // Elaborate constructors in the param context (using same namespace).
    // Constructors become TypeName.ConstructorName (e.g., Std.Vec.vnil, Std.Vec.vcons)
    let constructors = {
        let mut inner = Elaborator {
            kernel: crate::kernel::Kernel::new(
                elab.kernel.global,
                param_ctx,
                elab.kernel.state,
                &ind_resolver,
                elab.kernel.stub_table,
            ),
        };
        ind.constructors
            .iter()
            .map(|ctor| elab_constructor(db, &mut inner, ctor))
            .collect::<Result<Vec<_>, _>>()?
    };

    // Run solver based on mode
    if lenient {
        run_solver_lenient(db, elab)?;
    } else {
        run_solver(db, elab)?;
    }

    Ok(ElaboratedInductive {
        name,
        params,
        indices,
        universe: universe_syn,
        constructors,
    })
}

/// Elaborate a constructor: type expression is `(A:T) -> ... -> Result`.
/// For now, treat the entire constructor type as one expression.
fn elab_constructor<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    ctor: &hwml_surface::Constructor,
) -> Result<ElaboratedConstructor<'db>, ElabError<'db>>
where
    Db: salsa::Database,
{
    let name = ctor.name.value.to_vec();
    // Elaborate the constructor type as a type-code.
    let ty_syn = elab::expr::check(db, elab, &ctor.ty, Rc::new(Ty::UniverseType))?.into_inner();
    // The full type is a Pi chain; for now store as empty params + result.
    Ok(ElaboratedConstructor {
        name,
        params: vec![],
        result: ty_syn,
    })
}

// ─── Telescope elaboration ────────────────────────────────────────────────────

/// Elaborate a list of typed binding groups into a telescope.
/// Returns both the type syntax list and the extended context after adding all binders.
pub(crate) fn elab_telescope<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
    groups: &[TypedBindingGroup],
) -> Result<(Vec<RcSyntax<'db>>, crate::ctx::ElabCtx<'db>), ElabError<'db>>
where
    Db: salsa::Database,
{
    let mut types = Vec::new();
    let mut current_ctx = elab.kernel.ctx.clone();

    for group in groups {
        let ty_syn = {
            let mut inner = Elaborator {
                kernel: crate::kernel::Kernel::new(
                    elab.kernel.global,
                    current_ctx.clone(),
                    elab.kernel.state,
                    elab.kernel.resolver,
                    elab.kernel.stub_table,
                ),
            };
            elab::expr::check(db, &mut inner, &group.ty, Rc::new(Ty::UniverseType))?.into_inner()
        };

        let ty_code = {
            let inner = crate::kernel::Kernel::new(
                elab.kernel.global,
                current_ctx.clone(),
                elab.kernel.state,
                elab.kernel.resolver,
                elab.kernel.stub_table,
            );
            inner.eval_syn_flex(&ty_syn)
        };

        let dom_ty: hwml_core::ty::RcTy<'db> = Rc::new(Ty::El(ty_code.clone()));

        for binder in &group.binders {
            let binder_name = binder_to_name(binder);
            let var = current_ctx.fresh_var(ty_code.clone());
            current_ctx = current_ctx.push_bound(binder_name, dom_ty.clone(), var);
            types.push(ty_syn.clone());
        }
    }

    Ok((types, current_ctx))
}

// ─── Helpers ──────────────────────────────────────────────────────────────────

/// Run the constraint solver after elaboration (strict mode).
///
/// Throws an error if the solver makes no progress.
/// Use this for standalone declarations outside of mutual recursion.
fn run_solver<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
) -> Result<(), ElabError<'db>>
where
    Db: salsa::Database,
{
    let mut solver = Solver::new(elab.kernel.state, elab.kernel.global, db);
    solver.run().map_err(|e| match e {
        SolveError::Elab(e) => e,
        SolveError::NoProgress => ElabError::CannotInfer { span: None },
    })
}

/// Run the constraint solver in lenient mode (for use during mutual recursion).
///
/// If the solver hits `NoProgress`, this is OK - constraints might be blocked
/// on metavariables that will be solved by other declarations in the SCC.
/// The final strict solver run at the end of the SCC will catch any real errors.
pub fn run_solver_lenient<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
) -> Result<(), ElabError<'db>>
where
    Db: salsa::Database,
{
    let mut solver = Solver::new(elab.kernel.state, elab.kernel.global, db);
    match solver.run() {
        Ok(()) => Ok(()),
        Err(SolveError::Elab(e)) => Err(e), // Real errors still propagate
        Err(SolveError::NoProgress) => Ok(()), // NoProgress is OK during mutual recursion
    }
}

/// Run solver then zonk. Use when a definition is complete and all metas must be resolved.
pub fn run_solver_and_zonk<'a, 'db, Db>(
    db: &'db Db,
    elab: &mut Elaborator<'a, 'db>,
) -> Result<(), ElabError<'db>>
where
    Db: salsa::Database,
{
    run_solver(db, elab)?;
    zonk(elab.kernel.state)
}

/// Collect only the typed binding groups from a mixed binding list.
pub fn collect_typed_groups(groups: &[BindingGroup]) -> Vec<TypedBindingGroup> {
    groups
        .iter()
        .filter_map(|g| match g {
            BindingGroup::Typed(tg) => Some(tg.clone()),
            BindingGroup::Untyped(_) => None,
        })
        .collect()
}

/// Build a surface `Pi` expression from typed groups + target.
pub fn build_pi_expr(
    typed_groups: Vec<TypedBindingGroup>,
    target: &hwml_surface::Expression,
) -> hwml_surface::Pi {
    hwml_surface::Pi {
        loc: 0..0,
        bindings: hwml_surface::TypedBindings {
            groups: typed_groups,
        },
        target: Box::new(target.clone()),
    }
}

/// Build a surface `Fun` expression from all binding groups + body.
/// If groups is empty, returns the body expression directly.
fn build_fun_expr(
    groups: &[BindingGroup],
    body: &hwml_surface::Expression,
) -> hwml_surface::Expression {
    if groups.is_empty() {
        return body.clone();
    }
    hwml_surface::Expression::Fun(hwml_surface::Fun {
        loc: 0..0,
        bindings: hwml_surface::Bindings {
            groups: groups.to_vec(),
        },
        expr: Box::new(body.clone()),
    })
}

/// Extract a name string from a binder expression.
fn binder_to_name(expr: &hwml_surface::Expression) -> String {
    if let hwml_surface::Expression::Id(id) = expr {
        String::from_utf8_lossy(&id.value).to_string()
    } else {
        "_".to_string()
    }
}

/// Post-hoc verification of an elaborated constant via the hwml-core kernel checker.
///
/// After zonk all metas in `state` have solutions. This function:
/// 1. Substitutes all meta solutions into `ty_syn` and `value_syn` (syntax-level).
/// 2. Runs `check_type` + `type_check` from `hwml_core::check` on the clean syntax.
///
/// This is the MLIR-verifier sanity check — should never fail if elaboration is sound.
pub fn verify_elaborated_constant<'db>(
    global: &GlobalEnv<'db>,
    state: &SolverState<'db>,
    db: &'db dyn salsa::Database,
    ty_syn: &Syntax<'db>,
    value_syn: &Syntax<'db>,
) -> Result<(), hwml_core::check::Error<'db>> {
    // Produce meta-free syntax by substituting all solved metas.
    let ty_clean = crate::zonk::substitute_metas_in_syntax(ty_syn, state);
    let val_clean = crate::zonk::substitute_metas_in_syntax(value_syn, state);

    let mut env = hwml_core::check::TCEnvironment {
        db,
        values: Environment::new(global),
        types: Vec::new(),
    };
    hwml_core::check::check_type(&mut env, &ty_clean)?;
    let mut eval_env = Environment::new(global);
    let ty_val =
        eval::eval(&mut eval_env, &ty_clean).map_err(hwml_core::check::Error::EvaluationFailure)?;
    hwml_core::check::type_check(&mut env, &val_clean, &ty_val)
}

/// Quote a `Ty` value to a `Syntax` term (for use as type annotation).
/// Only handles `Ty::El(code)` (returns the code) and `Ty::UniverseType`.
/// Returns Err(CannotInfer) for complex types that can't be directly represented.
fn quote_type<'a, 'db>(
    elab: &mut Elaborator<'a, 'db>,
    ty: &hwml_core::ty::Ty<'db>,
) -> Result<RcSyntax<'db>, ElabError<'db>> {
    use hwml_core::{ty::Ty as CoreTy, Value};
    match ty {
        CoreTy::UniverseType => {
            let (syn, _) = elab.kernel.synth_universe(None)?.into_inner();
            Ok(syn)
        }
        CoreTy::El(code) => {
            let depth = elab.kernel.ctx.depth();
            let universe_val = Value::UniverseCode(0);
            match hwml_core::quote::quote(elab.kernel.global, depth, code, &universe_val) {
                Ok(syn) => Ok(syn),
                Err(_) => Err(ElabError::CannotInfer { span: None }),
            }
        }
        _ => Err(ElabError::CannotInfer { span: None }),
    }
}
