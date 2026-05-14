use std::rc::Rc;

use hwml_core::{
    common::Icit,
    eval,
    ty::{RcTy, Ty},
    val::{
        Closure, ConstantInfo, DataConstructorInfo, GlobalEnv, LocalEnv, PrimitiveInfo,
        TypeConstructorInfo,
    },
    Binding, Index, Level, Name, QualifiedName, RcSyntax, RcValue, Source, SourceInfo, Syntax,
    Value, Word,
};
use hwml_support::FromWithDb;
use hwml_surface::Expression;

use crate::{
    context::ElabContext,
    ctx::ElabCtx,
    error::ElabError,
    meta::{MetaId, MetaKind},
    names::GlobalNameKind,
    resolver::{resolve_path, Resolver},
    state::SolverState,
    stub_table::StubTable,
};

/// Zero-cost proof a term was built by a kernel typing rule.
/// `new` is `pub(crate)` — only this module can construct `Checked` values.
pub struct Checked<T>(T);

impl<T> Checked<T> {
    pub(crate) fn new(v: T) -> Self {
        Checked(v)
    }

    pub fn into_inner(self) -> T {
        self.0
    }
}

pub struct Kernel<'a, 'db> {
    pub global: &'a GlobalEnv<'db>,
    pub ctx: ElabCtx<'db>,
    pub state: &'a mut SolverState<'db>,
    /// Scoped name resolution using Resolver + StubTable.
    /// The resolver tracks the current namespace and open directives.
    /// The stub table contains all harvested global declarations.
    pub resolver: &'a Resolver<'db>,
    pub stub_table: &'a StubTable<'db>,
}

/// Helper to format a path of Names as a dotted string for error messages
fn format_path<'db>(db: &'db dyn salsa::Database, path: &[Name<'db>]) -> String {
    path.iter()
        .map(|name| name.to_string(db))
        .collect::<Vec<_>>()
        .join(".")
}

impl<'a, 'db> Kernel<'a, 'db> {
    /// Create a kernel with resolver and stub table for scoped name resolution.
    pub fn new(
        global: &'a GlobalEnv<'db>,
        ctx: ElabCtx<'db>,
        state: &'a mut SolverState<'db>,
        resolver: &'a Resolver<'db>,
        stub_table: &'a StubTable<'db>,
    ) -> Self {
        Kernel {
            global,
            ctx,
            state,
            resolver,
            stub_table,
        }
    }

    // -------------------------------------------------------------------------
    // Global name lookup
    // -------------------------------------------------------------------------

    /// Synthesize a constant reference.
    pub fn synth_constant(
        &self,
        name: QualifiedName<'db>,
        info: &ConstantInfo<'db>,
    ) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
        let syn = hwml_core::Syntax::constant_rc(name);
        let ty_val = self.eval_syn_flex(&info.ty);
        Ok(Checked::new((syn, Rc::new(Ty::El(ty_val)))))
    }

    /// Synthesize a primitive reference.
    pub fn synth_primitive(
        &self,
        name: QualifiedName<'db>,
        info: &PrimitiveInfo<'db>,
    ) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
        let syn = hwml_core::Syntax::prim_rc(name);
        let ty_val = self.eval_syn_flex(&info.ty);
        Ok(Checked::new((syn, Rc::new(Ty::El(ty_val)))))
    }

    /// Synthesize a type constructor reference (zero arguments).
    /// If the type constructor has parameters/indices, its type is a Pi type.
    /// For example, `List` has type `(A : Type) → Type`.
    pub fn synth_type_constructor(
        &self,
        db: &'db dyn salsa::Database,
        name: QualifiedName<'db>,
        info: &TypeConstructorInfo<'db>,
    ) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
        let syn = hwml_core::Syntax::type_constructor_rc(name, vec![]);

        // Build the type from the telescope
        // If there are no arguments, the type is just `Type_level`
        // Otherwise, it's a Pi type: (x1 : A1) -> ... -> (xn : An) -> Type_level
        let ty_val = if info.arguments.is_empty() {
            // No parameters: just a universe type
            let universe_syn: RcSyntax<'db> = Rc::new(Syntax::UniverseCode(info.level.into()));
            self.eval_syn_flex(&universe_syn)
        } else {
            // Has parameters: build a Pi type from the telescope
            self.build_pi_type_from_telescope(db, &info.arguments, info.level.into())
        };

        Ok(Checked::new((syn, Rc::new(Ty::El(ty_val)))))
    }

    /// Synthesize a data constructor reference (zero arguments).
    pub fn synth_data_constructor(
        &self,
        name: QualifiedName<'db>,
        info: &DataConstructorInfo<'db>,
    ) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
        let syn = hwml_core::Syntax::data_constructor_rc(name, vec![]);
        let ty_val = self.eval_syn_flex(&info.ty);
        Ok(Checked::new((syn, Rc::new(Ty::El(ty_val)))))
    }

    /// Look up a surface name using scoped resolution (Resolver + StubTable) and synthesize it.
    /// Respects the current namespace and `open` directives.
    pub fn synth_global_by_path<Db>(
        &self,
        db: &'db Db,
        path: &[Name<'db>],
    ) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>>
    where
        Db: salsa::Database,
    {
        let path_str = format_path(db, path);
        eprintln!(
            "[KERNEL] synth_global_by_path called with path: {}",
            path_str
        );
        eprintln!(
            "[KERNEL] Current resolver namespace: {:?}",
            self.resolver.namespace().map(|n| n.to_string(db))
        );

        // Use resolver to find all matching qualified names in scope
        let candidates = resolve_path(db, self.stub_table, self.resolver, path);

        if candidates.is_empty() {
            return Err(ElabError::NotInScope {
                name: format_path(db, path),
                span: None,
                elab_backtrace: Vec::new(),
            });
        }

        if candidates.len() > 1 {
            return Err(ElabError::NotInScope {
                name: format!("Ambiguous: {}", format_path(db, path)),
                span: None,
                elab_backtrace: Vec::new(),
            });
        }

        let qname = candidates[0];

        // Look up the kind from the stub table
        let stub = self
            .stub_table
            .get(qname)
            .ok_or_else(|| ElabError::NotInScope {
                name: format_path(db, path),
                span: None,
                elab_backtrace: Vec::new(),
            })?;

        // Synthesize based on kind
        match stub.kind {
            GlobalNameKind::Constant => {
                let info = self
                    .global
                    .constant(qname)
                    .map_err(|e| ElabError::NotInScope {
                        name: format!("{:?}: {:?}", path, e),
                        span: None,
                        elab_backtrace: Vec::new(),
                    })?;
                self.synth_constant(qname, info)
            }
            GlobalNameKind::Primitive => {
                let info = self
                    .global
                    .primitive(qname)
                    .map_err(|e| ElabError::NotInScope {
                        name: format!("{:?}: {:?}", path, e),
                        span: None,
                        elab_backtrace: Vec::new(),
                    })?;
                self.synth_primitive(qname, info)
            }
            GlobalNameKind::TypeConstructor => {
                let info =
                    self.global
                        .type_constructor(qname)
                        .map_err(|e| ElabError::NotInScope {
                            name: format!("{:?}: {:?}", path, e),
                            span: None,
                            elab_backtrace: Vec::new(),
                        })?;
                self.synth_type_constructor(db, qname, info)
            }
            GlobalNameKind::DataConstructor => {
                let info =
                    self.global
                        .data_constructor(qname)
                        .map_err(|e| ElabError::NotInScope {
                            name: format!("{:?}: {:?}", path, e),
                            span: None,
                            elab_backtrace: Vec::new(),
                        })?;
                self.synth_data_constructor(qname, info)
            }
        }
    }

    // -------------------------------------------------------------------------
    // Variable
    // -------------------------------------------------------------------------

    /// Synthesize a variable: look up the type from the context.
    pub fn synth_var(
        &self,
        idx: Index,
    ) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
        let depth = self.ctx.depth();
        if idx.0 >= depth {
            return Err(ElabError::CannotInfer {
                span: None,
                elab_backtrace: Vec::new(),
            });
        }
        // Convert de Bruijn index to level.
        let level = Level::new(depth - 1 - idx.0);
        let entry = self.ctx.lookup_level(level).ok_or(ElabError::CannotInfer {
            span: None,
            elab_backtrace: Vec::new(),
        })?;
        let syn = Syntax::variable_rc(idx);
        Ok(Checked::new((syn, entry.ty.clone())))
    }

    // -------------------------------------------------------------------------
    // Metavariable
    // -------------------------------------------------------------------------

    /// Synthesize a metavariable applied to all current context variables.
    /// Substitution: [Var(0), Var(1), ..., Var(depth-1)] (innermost = index 0).
    pub fn synth_meta(
        &self,
        id: MetaId,
    ) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
        let entry = self.state.meta(id).ok_or(ElabError::UnsolvedMeta {
            meta: id,
            span: None,
            elab_backtrace: Vec::new(),
        })?;
        let ty = entry.ty.clone();
        let depth = self.ctx.depth();
        let substitution: Vec<RcSyntax<'db>> =
            (0..depth).map(|i| Syntax::variable_rc(Index(i))).collect();
        let meta_id = hwml_core::MetaVariableId::new(id.0 as u16);
        let syn = Syntax::metavariable_rc(meta_id, substitution);
        Ok(Checked::new((syn, ty)))
    }

    // -------------------------------------------------------------------------
    // Universe
    // -------------------------------------------------------------------------

    /// Synthesize the `Type` keyword.
    /// `hint = Some(n)` → concrete `UniverseCode(n)`.
    /// `hint = None` → fresh `?u : UniverseType` (McBride/Sterling shunting).
    pub fn synth_universe(
        &mut self,
        hint: Option<usize>,
        loc: Option<hwml_core::SourceRange<'db>>,
    ) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
        let universe_ty: RcTy<'db> = Rc::new(Ty::UniverseType);
        match hint {
            Some(n) => {
                let syn = Rc::new(Syntax::UniverseCode(n));
                Ok(Checked::new((syn, universe_ty)))
            }
            None => {
                let level_meta_id = if let Some(loc) = loc {
                    self.state.fresh_meta_with_provenance(
                        universe_ty.clone(),
                        self.ctx.depth(),
                        MetaKind::UniverseLevel,
                        loc.clone(),
                        format!("Type keyword at {:?}", loc),
                    )
                } else {
                    self.state.fresh_meta(
                        universe_ty.clone(),
                        self.ctx.depth(),
                        MetaKind::UniverseLevel,
                    )
                };
                self.synth_meta(level_meta_id)
            }
        }
    }

    // -------------------------------------------------------------------------
    // Application
    // -------------------------------------------------------------------------

    /// Synthesize an application: function already synthesized, check arg against domain.
    ///
    /// Expects `fun_ty` to be `Ty::El(Value::PiCode(dom_code, cod_clos))` after forcing.
    ///
    /// # Arguments
    /// * `source` - Source file identifier for error messages (inherited from parent elaborator)
    pub fn synth_app<Db>(
        &mut self,
        db: &'db Db,
        fun: Checked<(RcSyntax<'db>, RcTy<'db>)>,
        arg: &Expression,
        source: Source<'db>,
    ) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>>
    where
        Db: salsa::Database,
    {
        let (fun_syn, fun_ty) = fun.into_inner();

        // Force fun_ty to find a PiCode.
        let (dom_code, _icit, cod_clos) = self.force_to_pi(fun_ty)?;

        // Check argument against the domain.
        let dom_ty: RcTy<'db> = Rc::new(Ty::El(dom_code.clone()));
        let arg_syn = {
            // Use the source from the parent elaborator, not a synthetic one
            let arg_checked = crate::elab::expr::check(
                db,
                // We need a temporary Elaborator view; borrow self's fields.
                // Use a scope to avoid borrow issues by building the Elaborator inline.
                &mut crate::elab::Elaborator {
                    kernel: Kernel {
                        global: self.global,
                        ctx: self.ctx.clone(),
                        state: self.state,
                        resolver: self.resolver,
                        stub_table: self.stub_table,
                    },
                    context: ElabContext::new(source),
                },
                arg,
                dom_ty,
            )?;
            arg_checked.into_inner()
        };

        // Evaluate the argument to compute the return type.
        let arg_val = self.eval_syn_flex(&arg_syn);

        // Compute the return type by applying the codomain closure.
        let ret_code = self.flex_apply_clos(&cod_clos, &arg_val);
        let ret_ty: RcTy<'db> = Rc::new(Ty::El(ret_code));

        let app_syn = Syntax::application_rc(fun_syn, arg_syn, Icit::Explicit);
        Ok(Checked::new((app_syn, ret_ty)))
    }

    // -------------------------------------------------------------------------
    // Lambda
    // -------------------------------------------------------------------------

    /// Check a lambda against a Pi type.
    ///
    /// `dom_code` = value-level type code for the domain.
    /// `icit` = implicitness of the Pi binder (Explicit or Implicit)
    /// `cod_clos` = codomain closure: `cod_clos.apply(global, &var)` gives the return type code.
    /// `source` = Source file identifier for error messages (inherited from parent elaborator)
    pub fn check_lambda<Db>(
        &mut self,
        db: &'db Db,
        fun: &hwml_surface::Fun,
        dom_code: RcValue<'db>,
        icit: Icit,
        cod_clos: Closure<'db>,
        source: Source<'db>,
    ) -> Result<Checked<RcSyntax<'db>>, ElabError<'db>>
    where
        Db: salsa::Database,
    {
        // Collect the names from the first binding group.
        let (names, rest_groups) = peel_first_binder_group(&fun.bindings);

        if names.is_empty() {
            // No binders left: check body directly against the remaining type.
            let body_ty: RcTy<'db> = Rc::new(Ty::El(dom_code));
            let word = Word::new(db, "check_fun");
            let source = Source::new(db, SourceInfo::Synthetic(word));
            return crate::elab::expr::check(
                db,
                &mut crate::elab::Elaborator {
                    kernel: Kernel {
                        global: self.global,
                        ctx: self.ctx.clone(),
                        state: self.state,
                        resolver: self.resolver,
                        stub_table: self.stub_table,
                    },
                    context: ElabContext::new(source),
                },
                &fun.expr,
                body_ty,
            );
        }

        let name = names[0].clone();
        let remaining_names = names[1..].to_vec();

        // Extend context with a fresh variable of the domain type.
        let var = self.ctx.fresh_var(dom_code.clone());
        let dom_ty: RcTy<'db> = Rc::new(Ty::El(dom_code));
        let extended_ctx = self.ctx.push_bound(name.clone(), dom_ty, var.clone());

        // Compute the codomain type for the remaining binders.
        let ret_code = self.flex_apply_clos(&cod_clos, &var);

        let body_syn = {
            let mut inner_kernel = Kernel {
                global: self.global,
                ctx: extended_ctx,
                state: self.state,
                resolver: self.resolver,
                stub_table: self.stub_table,
            };

            if !remaining_names.is_empty() || !rest_groups.is_empty() {
                // More binders remain: build a synthetic Fun with the remaining
                // binders and recurse via check_lambda.
                let remaining_fun = build_remaining_fun(fun, &remaining_names, &rest_groups);
                let ret_ty_el: RcTy<'db> = Rc::new(Ty::El(ret_code.clone()));
                match inner_kernel.force_to_pi(ret_ty_el) {
                    Ok((dom2, icit2, cod2)) => inner_kernel
                        .check_lambda(db, &remaining_fun, dom2, icit2, cod2, source)?
                        .into_inner(),
                    Err(_) => {
                        // Codomain not yet a Pi (unsolved meta). Mint a fresh meta for
                        // each remaining binder and recurse so binders are still consumed.
                        let binder_count = count_binders(&remaining_fun.bindings);
                        if binder_count == 0 {
                            let ret_ty = Rc::new(Ty::El(ret_code));
                            // Use the source from parent elaborator
                            crate::elab::expr::check(
                                db,
                                &mut crate::elab::Elaborator {
                                    kernel: inner_kernel,
                                    context: ElabContext::new(source),
                                },
                                &remaining_fun.expr,
                                ret_ty,
                            )?
                            .into_inner()
                        } else {
                            // Create a fresh Pi meta for the stuck type and recurse.
                            let depth = inner_kernel.ctx.depth();
                            let universe_ty: RcTy<'db> = Rc::new(Ty::UniverseType);
                            let dom_meta = inner_kernel.state.fresh_meta(
                                universe_ty.clone(),
                                depth,
                                MetaKind::Term,
                            );
                            let (dom_syn, _) = inner_kernel.synth_meta(dom_meta)?.into_inner();
                            let dom_val = inner_kernel.eval_syn_flex(&dom_syn);
                            let cod_term = Rc::new(Syntax::UniverseCode(0));
                            let cod_clos2 = Closure::new(inner_kernel.ctx.to_local_env(), cod_term);
                            inner_kernel
                                .check_lambda(
                                    db,
                                    &remaining_fun,
                                    dom_val,
                                    Icit::Explicit,
                                    cod_clos2,
                                    source,
                                )?
                                .into_inner()
                        }
                    }
                }
            } else {
                // No remaining binders: check body against return type.
                let ret_ty: RcTy<'db> = Rc::new(Ty::El(ret_code));
                // Use the source from parent elaborator
                crate::elab::expr::check(
                    db,
                    &mut crate::elab::Elaborator {
                        kernel: inner_kernel,
                        context: ElabContext::new(source),
                    },
                    &fun.expr,
                    ret_ty,
                )?
                .into_inner()
            }
        };

        // Wrap in a lambda binding with the correct icit from the Pi type.
        // This implements Phase 3: automatic implicit lambda insertion!
        let binder_name = if name == "_" {
            Name::anonymous(db)
        } else {
            Name::from_with_db(db, name)
        };
        let lambda_syn = Syntax::lambda_rc(icit, Binding::new(binder_name, body_syn));
        Ok(Checked::new(lambda_syn))
    }

    // -------------------------------------------------------------------------
    // Expect (bidirectional typechecking)
    // -------------------------------------------------------------------------

    /// The `expect` primitive for bidirectional typechecking.
    ///
    /// Given `rhs : actual_ty`, ensures it can be used where `expected_ty` is required.
    ///
    /// Fast path: If types are equal, return `rhs` unchanged.
    /// Slow path: Emit constraint `actual_ty = expected_ty : Type` and return `rhs` unchanged.
    ///
    /// The witness meta is an internal detail of the constraint solver and is not
    /// exposed to the caller. This function returns the original elaborated term.
    pub fn expect(
        &mut self,
        expected_ty: RcTy<'db>,
        rhs: Checked<(RcSyntax<'db>, RcTy<'db>)>,
    ) -> Checked<RcSyntax<'db>> {
        self.expect_with_loc(expected_ty, rhs, None)
    }

    /// Check that a value has an expected type, emitting an equality constraint.
    /// This version accepts an optional location for better error messages.
    pub fn expect_with_loc(
        &mut self,
        expected_ty: RcTy<'db>,
        rhs: Checked<(RcSyntax<'db>, RcTy<'db>)>,
        loc: Option<hwml_core::SourceRange<'db>>,
    ) -> Checked<RcSyntax<'db>> {
        let (rhs_syn, actual_ty) = rhs.into_inner();

        // Fast path: pointer equality (same Rc allocation = definitely same type).
        if Rc::ptr_eq(&expected_ty, &actual_ty) {
            return Checked::new(rhs_syn);
        }

        // Also check structural equality for common cases.
        if types_syntactically_equal(&expected_ty, &actual_ty) {
            return Checked::new(rhs_syn);
        }

        // Slow path: emit type equality constraint.
        let depth = self.ctx.depth();

        // Extract type codes from El(...) wrapper
        let actual_code = match actual_ty.as_ref() {
            Ty::El(code) => code.clone(),
            Ty::UniverseType => Rc::new(Value::UniverseCode(0)), // Type itself
            _ => Rc::new(Value::UniverseCode(0)),                // Fallback for other type forms
        };

        let expected_code = match expected_ty.as_ref() {
            Ty::El(code) => code.clone(),
            Ty::UniverseType => Rc::new(Value::UniverseCode(0)),
            _ => Rc::new(Value::UniverseCode(0)),
        };

        // Emit constraint: actual_code = expected_code : Type
        self.state.emit_eq_with_loc(
            actual_code,
            expected_code,
            Rc::new(Ty::UniverseType),
            depth,
            loc,
        );

        // Return the original elaborated term.
        // It has type actual_ty, but the constraint ensures actual_ty = expected_ty.
        Checked::new(rhs_syn)
    }

    // -------------------------------------------------------------------------
    // Internal helpers
    // -------------------------------------------------------------------------

    /// Evaluate a syntax term in the current context.
    pub fn eval_syn(&self, syn: &Syntax<'db>) -> Result<RcValue<'db>, eval::Error<'db>> {
        let local = self.ctx.to_local_env();
        eval::substitute(self.global, syn, local)
    }

    /// Evaluate a syntax term, substituting Flex neutrals for unsolved metas.
    /// Unlike `eval_syn`, handles syntax that references metas only in SolverState.
    pub fn eval_syn_flex(&self, syn: &Syntax<'db>) -> RcValue<'db> {
        let local = self.ctx.to_local_env();
        match eval::substitute(self.global, syn, local.clone()) {
            Ok(val) => val,
            Err(_) => self.flex_eval_with_local(syn, local),
        }
    }

    /// Apply a closure to an argument using flex evaluation.
    /// Handles closures whose bodies contain unsolved metas.
    pub(crate) fn flex_apply_clos(&self, clos: &Closure<'db>, arg: &RcValue<'db>) -> RcValue<'db> {
        let mut local = clos.local.clone();
        local.push(arg.clone());
        // Try normal evaluation first; fall back to flex eval.
        match eval::substitute(self.global, &clos.term, local.clone()) {
            Ok(v) => v,
            Err(_) => self.flex_eval_with_local(&clos.term, local),
        }
    }

    /// Recursive flex evaluator: evaluates syntax to value, creating Flex
    /// neutrals for metas that exist only in SolverState (not GlobalEnv).
    fn flex_eval_with_local(&self, syn: &Syntax<'db>, local: LocalEnv<'db>) -> RcValue<'db> {
        match syn {
            Syntax::UniverseCode(n) => Rc::new(Value::UniverseCode(*n)),
            Syntax::Variable(var) => {
                let level = var.index.to_level(local.depth());
                local.get(level).clone()
            }
            Syntax::Metavariable(meta) => {
                let id = MetaId(meta.id.local_index as u32);
                if let Some(sol) = self.state.meta_solution(id) {
                    return sol.clone();
                }
                // Build Flex with arguments evaluated in current local env.
                let mut meta_local = LocalEnv::new();
                for arg in meta.iter() {
                    meta_local.push(self.flex_eval_with_local(arg, local.clone()));
                }
                let mv = hwml_core::val::MetaVariable::new(meta.id, meta_local);
                let dummy_ty: RcValue<'db> = Rc::new(Value::UniverseCode(0));
                Rc::new(Value::Flex(hwml_core::val::Flex::new(
                    mv,
                    hwml_core::val::Spine::empty(),
                    dummy_ty,
                )))
            }
            Syntax::PiCode(dom, _icit, binding) => {
                let cod = &binding.body;
                let dom_val = self.flex_eval_with_local(dom, local.clone());
                let cod_clos = Closure::new(local, cod.clone());
                Rc::new(Value::PiCode(dom_val, *_icit, cod_clos))
            }
            Syntax::Lambda(lam) => {
                let body_clos = Closure::new(local, lam.body.body.clone());
                Value::lambda_rc(lam.icit, body_clos)
            }
            Syntax::Application(app) => {
                let fun_val = self.flex_eval_with_local(&app.function, local.clone());
                let arg_val = self.flex_eval_with_local(&app.argument, local.clone());
                eval::run_application(self.global, &fun_val, arg_val, app.icit)
                    .unwrap_or_else(|_| Rc::new(Value::UniverseCode(0)))
            }
            _ => eval::substitute(self.global, syn, local)
                .unwrap_or_else(|_| Rc::new(Value::UniverseCode(0))),
        }
    }

    /// Force top-level Flex recursively by applying solved metavariable substitutions.
    fn force_deep(&self, val: RcValue<'db>) -> RcValue<'db> {
        if let Value::Flex(flex) = val.as_ref() {
            if let Some(forced) = self.state.force_flex(self.global, flex) {
                return self.force_deep(forced);
            }
        }
        val
    }

    /// Force a semantic type to `Pi` shape: extract `(dom_code, icit, cod_clos)`.
    /// Handles `Ty::El(Value::PiCode(dom, icit, cod))` and `Ty::Pi(dom, cod)`.
    pub fn force_to_pi(
        &self,
        ty: RcTy<'db>,
    ) -> Result<(RcValue<'db>, Icit, Closure<'db>), ElabError<'db>> {
        match ty.as_ref() {
            Ty::El(code) => {
                // Force the code to resolve any solved metavariables
                let forced_code = self.force_deep(code.clone());
                match forced_code.as_ref() {
                    Value::PiCode(dom, icit, cod) => Ok((dom.clone(), *icit, cod.clone())),
                    _ => Err(ElabError::TypeMismatch {
                        expected: Rc::new(Ty::El(Rc::new(Value::PiCode(
                            Rc::new(Value::UniverseCode(0)),
                            Icit::Explicit,
                            hwml_core::val::Closure::new(
                                hwml_core::val::LocalEnv::new(),
                                Rc::new(Syntax::UniverseCode(0)),
                            ),
                        )))),
                        actual: ty.clone(),
                        span: None,
                        elab_backtrace: Vec::new(),
                    }),
                }
            }
            Ty::Pi(dom, cod) => {
                // Convert TyClosure.body (RcTy) to a Closure<'db> — use a dummy Syntax.
                // This only works for non-dependent codomains (same type for all inputs).
                // Full dependent support requires PiCode representation.
                let dom_code =
                    ty_to_value_code(dom).unwrap_or_else(|| Rc::new(Value::UniverseCode(0)));
                // The TyClosure.body is already a Ty, not evaluatable — synthesize a dummy closure.
                let _ = cod;
                Ok((
                    dom_code,
                    Icit::Explicit, // Legacy Pi types are always explicit
                    Closure::new(
                        hwml_core::val::LocalEnv::new(),
                        Rc::new(Syntax::UniverseCode(0)),
                    ),
                ))
            }
            _ => Err(ElabError::TypeMismatch {
                expected: Rc::new(Ty::UniverseType), // placeholder
                actual: ty,
                span: None,
                elab_backtrace: Vec::new(),
            }),
        }
    }

    // -------------------------------------------------------------------------
    // Telescope utilities
    // -------------------------------------------------------------------------

    /// Build a Pi type from a telescope of types, ending with a universe level.
    /// For a telescope `(x1 : A1) (x2 : A2) ... (xn : An)` and level `L`,
    /// returns `(x1 : A1) -> (x2 : A2) -> ... -> (xn : An) -> Type_L`.
    ///
    /// This is used to compute the type of a type constructor with parameters.
    /// For example, `List` with parameter `(A : Type)` gets type `(A : Type) -> Type`.
    fn build_pi_type_from_telescope(
        &self,
        db: &'db dyn salsa::Database,
        telescope: &hwml_core::syn::Telescope<'db>,
        result_level: usize,
    ) -> RcValue<'db> {
        // Build the result type: UniverseCode(result_level)
        let result_ty = Rc::new(Value::UniverseCode(result_level));

        // If telescope is empty, just return the result type
        if telescope.is_empty() {
            return result_ty;
        }

        // Build Pi types from right to left (innermost to outermost)
        // We need to evaluate each binding in the context of previous bindings
        let mut result = result_ty;

        // Process bindings in reverse order to build the nested Pi
        for (idx, cell) in telescope.iter().enumerate().rev() {
            let binding_syn = &cell.ty;
            // Evaluate this binding's type in the environment with all previous bindings
            // For simplicity, we create a fresh environment with variables for preceding bindings
            let mut env = hwml_core::val::Environment {
                global: self.global,
                local: hwml_core::val::LocalEnv::new(),
                transparent: hwml_core::val::TransparentEnv::new(),
            };

            // Push placeholder variables for all preceding bindings (indices 0..idx)
            for i in 0..idx {
                let preceding_binding = &telescope.cells[i].ty;
                // Evaluate the preceding binding's type
                let preceding_ty = match hwml_core::eval::eval(&mut env, preceding_binding) {
                    Ok(ty) => ty,
                    Err(_) => {
                        // Fallback: use UniverseCode(0)
                        Rc::new(Value::UniverseCode(0))
                    }
                };
                // Push a variable of this type
                let var = Value::variable_rc(hwml_core::Level::new(i), preceding_ty.clone());
                env.push_var(preceding_ty);
            }

            // Now evaluate this binding's type
            let dom_val = match hwml_core::eval::eval(&mut env, binding_syn) {
                Ok(val) => val,
                Err(_) => {
                    // Fallback: use UniverseCode(0)
                    Rc::new(Value::UniverseCode(0))
                }
            };

            // Build a closure for the codomain
            // The closure body is the `result` we're building up
            // But we need it as syntax, so we quote it back
            let cod_syn = match hwml_core::quote::type_quote(db, self.global, idx, &result) {
                Ok(syn) => syn,
                Err(_) => {
                    // Fallback: use UniverseCode(result_level)
                    Rc::new(Syntax::UniverseCode(result_level))
                }
            };

            // Create a closure with the current local environment
            let cod_clos = hwml_core::val::Closure::new(env.local.clone(), cod_syn);

            // Wrap in a PiCode
            result = Rc::new(Value::PiCode(dom_val, Icit::Explicit, cod_clos));
        }

        result
    }
}

// ─── Free functions ───────────────────────────────────────────────────────────

/// Convert a semantic `Ty` to a value-level type code, if possible.
/// Returns `None` for types without a clear code representation.
pub(crate) fn ty_to_value_code<'db>(ty: &Ty<'db>) -> Option<RcValue<'db>> {
    match ty {
        Ty::El(code) => Some(code.clone()),
        _ => None,
    }
}

/// Structural equality check for the common `Ty` cases.
fn types_syntactically_equal<'db>(a: &Ty<'db>, b: &Ty<'db>) -> bool {
    match (a, b) {
        (Ty::UniverseType, Ty::UniverseType) => true,
        (Ty::SignalUniverseType, Ty::SignalUniverseType) => true,
        (Ty::ModuleUniverseType, Ty::ModuleUniverseType) => true,
        // For El: pointer-equal codes.
        (Ty::El(c1), Ty::El(c2)) => Rc::ptr_eq(c1, c2),
        _ => false,
    }
}

/// Count total binders across all groups in a `Bindings`.
fn count_binders(bindings: &hwml_surface::Bindings) -> usize {
    bindings
        .groups
        .iter()
        .map(|g| match g {
            hwml_surface::BindingGroup::Untyped(_) => 1,
            hwml_surface::BindingGroup::Typed(tg) => tg.binders.len(),
        })
        .sum()
}

/// Build a synthetic `Fun` with the remaining binders for recursive lambda checking.
fn build_remaining_fun(
    fun: &hwml_surface::Fun,
    remaining_names: &[String],
    rest_groups: &[hwml_surface::BindingGroup],
) -> hwml_surface::Fun {
    let mut groups: Vec<hwml_surface::BindingGroup> = remaining_names
        .iter()
        .map(|n| {
            let binder = hwml_surface::Binder::new(
                0..0,
                hwml_surface::Pattern::Id(hwml_surface::Id {
                    loc: 0..0,
                    value: n.clone().into_boxed_str(),
                }),
            );
            hwml_surface::BindingGroup::Untyped(hwml_surface::UntypedBindingGroup {
                binders: vec![binder],
            })
        })
        .collect();
    groups.extend_from_slice(rest_groups);
    hwml_surface::Fun {
        loc: fun.loc.clone(),
        bindings: hwml_surface::Bindings { groups },
        expr: fun.expr.clone(),
    }
}

/// Extract binder names from the first group of a `Bindings`.
/// Returns `(names_from_first_group, remaining_groups)`.
fn peel_first_binder_group(
    bindings: &hwml_surface::Bindings,
) -> (Vec<String>, Vec<hwml_surface::BindingGroup>) {
    let mut groups_iter = bindings.groups.iter();
    let first = match groups_iter.next() {
        None => return (vec![], vec![]),
        Some(g) => g,
    };
    let rest: Vec<_> = groups_iter.cloned().collect();

    let names = match first {
        hwml_surface::BindingGroup::Untyped(ug) => {
            // The binders are a Vec<Binder>
            ug.binders
                .iter()
                .filter_map(|b| extract_binder_name(b))
                .collect()
        }
        hwml_surface::BindingGroup::Typed(tg) => tg
            .binders
            .iter()
            .filter_map(|b| extract_binder_name(b))
            .collect(),
    };
    (names, rest)
}

pub(crate) fn extract_binder_name(binder: &hwml_surface::Binder) -> Option<String> {
    match &binder.pattern {
        hwml_surface::Pattern::Id(id) => Some(id.value.to_string()),
        hwml_surface::Pattern::Paren(p) => {
            // For parenthesized patterns, recursively extract from the inner pattern
            match &*p.inner {
                hwml_surface::Pattern::Id(id) => Some(id.value.to_string()),
                _ => None,
            }
        }
        _ => None,
    }
}

// Removed dead function rhs_val_clone - was never called
