//! Bidirectional type checking elaborator.
//!
//! This module implements the elaborator that converts surface syntax (hwml-surface)
//! into the core IR (hwml-core) using bidirectional type checking with metavariables.
//!
//! ## Architecture
//!
//! The elaborator uses **bidirectional type checking** with two modes:
//!
//! - **Check mode**: `check(expr, expected_type)` - Used for introduction forms (lambda, pi, etc.)
//!   where we know the expected type and check that the expression has that type.
//!
//! - **Synth mode**: `synth(expr) -> (term, type)` - Used for elimination forms (application, variable)
//!   where we infer the type from the expression.
//!
//! ## Name Resolution
//!
//! The elaborator maintains a **scope stack** that maps surface-level names to de Bruijn indices.
//! As we traverse binders, we push names onto the scope and convert them to indices.
//!
//! ## Error Recovery
//!
//! When elaboration encounters an error (undefined variable, type mismatch, etc.), it creates
//! a **poisoned metavariable** instead of failing. This allows elaboration to continue and
//! report multiple errors at once.

use crate::trusted::trusted::{Trusted, TrustedTypedSyntax};
use crate::TrustedSyntax;
use hwml_core::binding::DynBinding;
use hwml_core::common::{Index, Location, UniverseLevel};
use hwml_core::eval;
use hwml_core::quote::type_quote;
use hwml_core::syn::CaseBranch;
use hwml_core::{Syntax, TypedSyntax};

use hwml_core::val::{Closure, Environment, LocalEnv, RcValue, TransparentEnv, Value};
use hwml_core::ConstantId;
use hwml_support::{FromWithDb, SourceFile};
use hwml_surface::syntax as surface;
use std::collections::HashMap;
use std::rc::Rc;

use crate::engine::SolverEnvironment;
use crate::force::force;
use crate::unify::unify;

use crate::*;

// ============================================================================
// Diagnostics and Context
// ============================================================================

/// Information about a declared primitive
#[derive(Clone, Debug)]
pub struct PrimitiveInfo<'db> {
    /// The elaborated type of the primitive
    pub ty: RcValue<'db>,
    /// The core syntax term representing the primitive
    pub term: Rc<Syntax<'db>>,
}

/// The elaboration context tracks the current scope and solver state.
pub struct ElaborationContext<'db, 'g> {
    /// The Salsa database for location interning
    db: &'db dyn salsa::Database,

    /// The source file being elaborated (for location tracking)
    source_file: Option<SourceFile>,

    /// The solver environment for creating metavariables and unifying types
    pub solver: SolverEnvironment<'db, 'g>,

    /// Name resolution scope: maps variable names to their de Bruijn levels
    /// Level 0 is the outermost binding, level N is the innermost
    scope: Vec<String>,

    /// Type environment: tracks the types of bound variables
    /// Parallel to the scope, indexed by de Bruijn level
    types: Vec<RcValue<'db>>,

    /// Primitive declarations: maps primitive names to their types and terms
    primitives: std::collections::HashMap<String, PrimitiveInfo<'db>>,

    /// Collected diagnostics
    diagnostics: Vec<Diagnostic>,
}

/// RAII guard that automatically pops bindings when dropped
pub struct ScopeGuard<'db, 'g, 'ctx> {
    ctx: &'ctx mut ElaborationContext<'db, 'g>,
    count: usize,
}

impl<'db, 'g, 'ctx> Drop for ScopeGuard<'db, 'g, 'ctx> {
    fn drop(&mut self) {
        for _ in 0..self.count {
            self.ctx.scope.pop();
            self.ctx.types.pop();
        }
    }
}

impl<'db, 'g, 'ctx> std::ops::Deref for ScopeGuard<'db, 'g, 'ctx> {
    type Target = ElaborationContext<'db, 'g>;

    fn deref(&self) -> &Self::Target {
        self.ctx
    }
}

impl<'db, 'g, 'ctx> std::ops::DerefMut for ScopeGuard<'db, 'g, 'ctx> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.ctx
    }
}

impl<'db, 'g> ElaborationContext<'db, 'g> {
    /// Create a new elaboration context with the given solver environment
    pub fn new(
        db: &'db dyn salsa::Database,
        source_file: Option<SourceFile>,
        solver: SolverEnvironment<'db, 'g>,
    ) -> Self {
        ElaborationContext {
            db,
            source_file,
            solver,
            scope: Vec::new(),
            types: Vec::new(),
            primitives: std::collections::HashMap::new(),
            diagnostics: Vec::new(),
        }
    }

    /// Register a primitive with its type and term
    pub fn register_primitive(&mut self, name: String, info: PrimitiveInfo<'db>) {
        self.primitives.insert(name, info);
    }

    /// Look up a primitive by name
    pub fn lookup_primitive(&self, name: &str) -> Option<&PrimitiveInfo<'db>> {
        self.primitives.get(name)
    }

    /// Push bindings and return an RAII guard that will pop them on drop
    ///
    /// Usage:
    /// ```ignore
    /// {
    ///     let mut scoped_ctx = ctx.push_bindings(&bindings);
    ///     // Use scoped_ctx like normal ctx
    ///     elaborate_something(&mut scoped_ctx, ...).await?;
    /// } // Bindings automatically popped here
    /// ```
    pub fn push_bindings(
        &mut self,
        bindings: &[(String, RcValue<'db>)],
    ) -> ScopeGuard<'db, 'g, '_> {
        for (name, ty) in bindings {
            self.push_binding(name.clone(), ty.clone());
        }
        ScopeGuard {
            ctx: self,
            count: bindings.len(),
        }
    }

    /// Get an iterator over all registered primitives
    pub fn primitives(&self) -> impl Iterator<Item = (&String, &PrimitiveInfo<'db>)> {
        self.primitives.iter()
    }

    /// Get the collected diagnostics
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    /// Take ownership of the collected diagnostics
    pub fn take_diagnostics(self) -> Vec<Diagnostic> {
        self.diagnostics
    }

    /// Report a solver error as a diagnostic
    pub fn report_solver_error(&mut self, error: String) {
        let loc = Location::UNKNOWN;
        self.diagnostics.push(Diagnostic {
            location: loc,
            message: format!("Solver error: {}", error),
        });
    }

    /// Public wrapper for synth that can be called from pipeline
    pub async fn synth_expr(
        &mut self,
        expr: &surface::Expression,
    ) -> Result<TrustedTypedSyntax<'db>, String> {
        Ok(synth(self, expr).await)
    }

    /// Public wrapper for check that can be called from pipeline
    pub async fn check_expr(
        &mut self,
        expr: &surface::Expression,
        expected_ty: RcValue<'db>,
    ) -> Result<TrustedSyntax<'db>, String> {
        Ok(check(self, expr, expected_ty).await)
    }

    /// Convert a surface AST location (Range<usize>) to a Salsa-interned Location
    pub fn convert_location(&self, _range: &std::ops::Range<usize>) -> Location {
        // For now, just use UNKNOWN since we've simplified Location to not track source info
        // TODO: Implement proper location tracking with a location allocator
        Location::UNKNOWN
    }

    /// Push a new binding onto the scope
    pub fn push_binding(&mut self, name: String, ty: RcValue<'db>) {
        self.scope.push(name);
        self.types.push(ty);
    }

    /// Pop a binding from the scope
    pub fn pop_binding(&mut self) {
        self.scope.pop();
        self.types.pop();
    }

    /// Get the current depth (number of bindings in scope)
    pub fn depth(&self) -> usize {
        self.scope.len()
    }

    /// Look up a variable name and return its de Bruijn index
    /// Returns None if the variable is not in scope
    pub fn lookup_var(&self, name: &str) -> Option<usize> {
        // Search from the end (innermost binding) to the start (outermost)
        // The de Bruijn index is the distance from the end
        self.scope.iter().rev().position(|n| n == name)
    }

    /// Get the type of a variable by its de Bruijn index
    pub fn get_var_type(&self, index: usize) -> Option<&RcValue<'db>> {
        let level = self.scope.len().checked_sub(index + 1)?;
        self.types.get(level)
    }

    /// Get the current de Bruijn level (depth of the scope)
    pub fn level(&self) -> usize {
        self.scope.len()
    }

    /// Extract location from a surface expression
    pub fn expr_location(&self, expr: &surface::Expression) -> Location {
        use surface::Expression;
        match expr {
            Expression::Id(id) => self.convert_location(&id.loc),
            Expression::Num(num) => self.convert_location(&num.loc),
            Expression::Fun(fun) => self.convert_location(&fun.loc),
            Expression::Pi(pi) => self.convert_location(&pi.loc),
            Expression::Arrow(arrow) => self.convert_location(&arrow.loc),
            Expression::FatArrow(fat_arrow) => self.convert_location(&fat_arrow.loc),
            Expression::App(app) => self.convert_location(&app.loc),
            Expression::LetIn(let_in) => self.convert_location(&let_in.loc),
            Expression::Underscore(underscore) => self.convert_location(&underscore.loc),
            Expression::Paren(paren) => self.expr_location(&paren.expr),
            Expression::Match(m) => self.expr_location(&m.scrutinee),
            Expression::Universe(univ) => self.convert_location(&univ.loc),
            Expression::Str(_) => Location::UNKNOWN,
        }
    }

    /// Create a fresh metavariable with the given type at the given location
    pub fn fresh_meta(&self, ty: RcValue<'db>, loc: Location) -> TrustedSyntax<'db> {
        let meta_id = self.solver.fresh_meta_id(ty, loc);
        crate::rules::form_meta(meta_id)
    }

    /// Create a poisoned metavariable for error recovery
    pub fn fresh_poisoned_meta(&self, ty: RcValue<'db>, loc: Location) -> TrustedSyntax<'db> {
        // Create a poisoned metavariable ID
        let meta_id = self
            .solver
            .state
            .borrow_mut()
            .fresh_poisoned_meta(ty.clone(), loc);
        crate::rules::form_meta(meta_id)
    }

    /// Report an error and return a poisoned metavariable
    pub fn error(
        &mut self,
        loc: Location,
        message: String,
        expected_ty: RcValue<'db>,
    ) -> TrustedSyntax<'db> {
        // Collect the diagnostic instead of printing
        self.diagnostics.push(Diagnostic {
            location: loc,
            message,
        });
        self.fresh_poisoned_meta(expected_ty, loc)
    }

    /// Evaluate a syntax term to a value in the current context
    pub fn eval(&self, term: &TrustedSyntax<'db>) -> Result<RcValue<'db>, eval::Error> {
        let mut env = Environment {
            global: self.solver.tc_env.values.global,
            local: self.build_value_env(),
            transparent: TransparentEnv::new(),
        };
        eval::eval(&mut env, &**term)
    }

    /// Build a LocalEnv containing values for all bound variables in scope
    /// This is used for evaluation - each variable becomes a rigid variable value
    fn build_value_env(&self) -> LocalEnv<'db> {
        let mut local = LocalEnv::new();
        for (level, ty) in self.types.iter().enumerate() {
            let var_value = Rc::new(Value::variable(level.into(), ty.clone()));
            local.push(var_value);
        }
        local
    }

    /// Force a value to weak head normal form (async)
    pub async fn whnf(&self, value: RcValue<'db>) -> RcValue<'db> {
        // Use the force function from hwml-elab to substitute solved metavariables
        force(&self.solver, value).unwrap_or_else(|e| {
            eprintln!("Warning: force failed during whnf: {}", e);
            // Return a poisoned meta on error
            let error_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
            self.solver.fresh_poisoned_meta(error_ty, Location::UNKNOWN)
        })
    }

    // ========================================================================
    // Pattern Matching Helpers
    // ========================================================================

    /// Generate a fresh variable name for pattern matching
    pub fn fresh_var_name(&self, prefix: &str, index: usize) -> String {
        format!("{}_{}", prefix, index)
    }

    /// Look up the arity of a data constructor from the global environment
    pub fn get_constructor_arity(&self, ctor: ConstantId<'db>) -> Result<usize, String> {
        // Query the global environment for the data constructor
        match self.solver.tc_env.values.global.data_constructor(ctor) {
            Ok(data_info) => {
                // The arity is the number of arguments the constructor takes
                Ok(data_info.arguments.len())
            }
            Err(_) => Err(format!(
                "Unknown data constructor: {}",
                ctor.name(self.solver.tc_env.db)
            )),
        }
    }

    // ========================================================================
    // Implicit Lifting Helpers
    // ========================================================================

    /// Check if a type requires lifting from object-level to meta-level.
    /// Returns Some(inner_ty) if expected_ty is Lift(inner_ty), None otherwise.
    fn is_lift_type(&self, ty: &Value<'db>) -> Option<RcValue<'db>> {
        match ty {
            Value::Lift(lift) => Some(lift.ty.clone()),
            _ => None,
        }
    }

    /// Check if a type requires signal lifting.
    /// Returns Some(inner_ty) if expected_ty is SLift(inner_ty), None otherwise.
    fn is_slift_type(&self, ty: &Value<'db>) -> Option<RcValue<'db>> {
        match ty {
            Value::SLift(slift) => Some(slift.ty.clone()),
            _ => None,
        }
    }

    /// Check if a type requires module lifting.
    /// Returns Some(inner_ty) if expected_ty is MLift(inner_ty), None otherwise.
    fn is_mlift_type(&self, ty: &Value<'db>) -> Option<RcValue<'db>> {
        match ty {
            Value::MLift(mlift) => Some(mlift.ty.clone()),
            _ => None,
        }
    }

    /// Determine if we should insert implicit lifting.
    /// This checks if the expected type is a lifted type and the inferred type is not.
    fn should_insert_lift(
        &self,
        expected_ty: &Value<'db>,
        inferred_ty: &Value<'db>,
    ) -> Option<LiftKind> {
        // Check for Lift: if expected is Lift(A) and inferred is A, insert Lift
        if let Some(_inner) = self.is_lift_type(expected_ty) {
            if !matches!(inferred_ty, Value::Lift(_)) {
                return Some(LiftKind::Lift);
            }
        }

        // Check for SLift: if expected is SLift(A) and inferred is A, insert SLift
        if let Some(_inner) = self.is_slift_type(expected_ty) {
            if !matches!(inferred_ty, Value::SLift(_)) {
                return Some(LiftKind::SLift);
            }
        }

        // Check for MLift: if expected is MLift(A) and inferred is A, insert MLift
        if let Some(_inner) = self.is_mlift_type(expected_ty) {
            if !matches!(inferred_ty, Value::MLift(_)) {
                return Some(LiftKind::MLift);
            }
        }

        None
    }
}

/// The kind of lifting to insert.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LiftKind {
    /// Regular universe lifting (Lift)
    Lift,
    /// Signal lifting (SLift)
    SLift,
    /// Module lifting (MLift)
    MLift,
}

#[async_recursion::async_recursion(?Send)]
pub async fn check<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    expr: &surface::Expression,
    expected_ty: RcValue<'db>,
) -> TrustedSyntax<'db> {
    use surface::Expression;

    match expr {
        Expression::Fun(fun) => check_fun(ctx, fun, expected_ty).await,
        Expression::Pi(pi) => check_pi(ctx, pi, expected_ty).await,
        Expression::Arrow(arrow) => check_arrow(ctx, arrow, expected_ty).await,
        Expression::FatArrow(fat_arrow) => check_fat_arrow(ctx, fat_arrow, expected_ty).await,
        Expression::Match(match_expr) => todo!("foo"), // check_match(ctx, match_expr, expected_ty).await,
        Expression::Underscore(underscore) => {
            let loc = ctx.convert_location(&underscore.loc);
            ctx.fresh_meta(expected_ty, loc)
        }
        _ => {
            let synth_result = synth(ctx, expr).await;
            let term = Trusted(synth_result.subject.clone());
            let inferred_ty = synth_result.ty.clone();

            // Check if we need to insert implicit lifting
            if let Some(lift_kind) = ctx.should_insert_lift(&expected_ty, &inferred_ty) {
                let loc = ctx.expr_location(expr);

                // Insert the appropriate lifting construct
                let lifted_term = match lift_kind {
                    LiftKind::Lift => Trusted(Syntax::lift_rc(term.unwrap())),
                    LiftKind::SLift => Trusted(Syntax::slift_rc(term.unwrap())),
                    LiftKind::MLift => Trusted(Syntax::mlift_rc(term.unwrap())),
                };

                // The lifted term should now have the expected type
                // We still verify this with unification
                let lifted_ty = match lift_kind {
                    LiftKind::Lift => Value::lift(inferred_ty).into(),
                    LiftKind::SLift => Value::slift(inferred_ty).into(),
                    LiftKind::MLift => Value::mlift(inferred_ty).into(),
                };

                let db = ctx.solver.tc_env.db;
                let solver_env = ctx.solver.clone();
                if let Err(e) = unify(
                    db,
                    solver_env,
                    lifted_ty,
                    expected_ty.clone(),
                    Rc::new(Value::universe(UniverseLevel::new(0))),
                )
                .await
                {
                    return ctx.error(
                        loc,
                        format!("Type mismatch after lifting: {:?}", e),
                        expected_ty,
                    );
                }

                return lifted_term;
            }

            // No lifting needed, just unify as before
            let db = ctx.solver.tc_env.db;
            let solver_env = ctx.solver.clone();
            if let Err(e) = unify(
                db,
                solver_env,
                inferred_ty.clone(),
                expected_ty.clone(),
                Rc::new(Value::universe(UniverseLevel::new(0))),
            )
            .await
            {
                let loc = ctx.expr_location(expr);
                return ctx.error(loc, format!("Type mismatch: {:?}", e), expected_ty);
            }
            term
        }
    }
}

#[async_recursion::async_recursion(?Send)]
pub async fn synth<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    expr: &surface::Expression,
) -> TrustedTypedSyntax<'db> {
    use surface::Expression;

    match expr {
        Expression::Id(id) => synth_id(ctx, id).await,
        Expression::App(app) => synth_app(ctx, app).await,
        Expression::LetIn(let_in) => synth_let(ctx, let_in).await,
        Expression::Paren(paren) => synth(ctx, &paren.expr).await,
        Expression::Num(num) => synth_num(ctx, num).await,
        Expression::Universe(univ) => synth_universe(ctx, univ).await,
        Expression::Fun(_) | Expression::Pi(_) | Expression::Arrow(_) | Expression::FatArrow(_) => {
            let loc = ctx.expr_location(expr);
            let message = "Cannot infer type for lambda/pi/arrow without annotation".to_string();
            let error_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
            let error_term = ctx.error(loc, message, error_ty.clone());
            Trusted(TypedSyntax {
                subject: error_term.unwrap(),
                ty: error_ty,
            })
        }
        Expression::Underscore(_) => {
            let loc = ctx.expr_location(expr);
            let message = "Cannot infer type for underscore".to_string();
            let error_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
            let error_term = ctx.error(loc, message, error_ty.clone());
            Trusted(TypedSyntax {
                subject: error_term.unwrap(),
                ty: error_ty,
            })
        }
        Expression::Str(_) => {
            let loc = ctx.expr_location(expr);
            let message = "String literals not yet supported".to_string();
            let error_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
            let error_term = ctx.error(loc, message, error_ty.clone());
            Trusted(TypedSyntax {
                subject: error_term.unwrap(),
                ty: error_ty,
            })
        }
        Expression::Match(_) => {
            let loc = ctx.expr_location(expr);
            let message = "Cannot infer type for match expression without annotation".to_string();
            let error_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
            let error_term = ctx.error(loc, message, error_ty.clone());
            Trusted(TypedSyntax {
                subject: error_term.unwrap(),
                ty: error_ty,
            })
        }
    }
}

// Helper functions for specific expression types

async fn check_fun<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    fun: &surface::Fun,
    expected_ty: RcValue<'db>,
) -> TrustedSyntax<'db> {
    // Lambda checking: we expect a Pi type
    // For now, handle the simple case of a single untyped parameter
    // TODO: Handle multiple parameters and typed parameters

    if fun.bindings.groups.is_empty() {
        let loc = ctx.convert_location(&fun.loc);
        return ctx.error(loc, "Lambda with no parameters".to_string(), expected_ty);
    }

    // For now, only handle a single untyped parameter
    if fun.bindings.groups.len() > 1 {
        let loc = ctx.convert_location(&fun.loc);
        return ctx.error(
            loc,
            "Multiple parameter groups not yet supported".to_string(),
            expected_ty,
        );
    }

    let binding_group = &fun.bindings.groups[0];
    match binding_group {
        surface::BindingGroup::Untyped(untyped) => {
            // Extract the parameter name
            let param_name = match &*untyped.binders {
                surface::Expression::Id(id) => std::str::from_utf8(&id.value)
                    .unwrap_or("<invalid>")
                    .to_string(),
                _ => {
                    let loc = ctx.expr_location(&untyped.binders);
                    return ctx.error(
                        loc,
                        "Complex binder patterns not yet supported".to_string(),
                        expected_ty,
                    );
                }
            };

            // Force the expected type to weak head normal form
            let expected_ty = ctx.whnf(expected_ty).await;

            // The expected type should be a Pi type
            match &*expected_ty {
                Value::Pi(pi) => {
                    // Extract the parameter type and target closure
                    let param_ty = pi.source.clone();
                    let target_closure = &pi.target;

                    // Push the binding and elaborate the body
                    ctx.push_binding(param_name, param_ty.clone());

                    // Apply the closure to get the target type
                    // Create a fresh variable for the parameter
                    let param_var = Rc::new(Value::variable(ctx.depth().into(), param_ty.clone()));
                    let target_ty = eval::run_closure(
                        ctx.solver.tc_env.values.global,
                        target_closure,
                        [param_var],
                    )
                    .unwrap_or_else(|e| {
                        eprintln!("Failed to apply Pi closure: {}", e);
                        Rc::new(Value::universe(UniverseLevel::new(0)))
                    });

                    let body = check(ctx, &fun.expr, target_ty).await;
                    ctx.pop_binding();

                    // Use the kernel API to construct the lambda
                    crate::rules::check_lam(&ctx.solver, expected_ty.clone(), body)
                        .await
                        .unwrap_or_else(|e| {
                            let loc = ctx.expr_location(&surface::Expression::Fun(fun.clone()));
                            ctx.error(
                                loc,
                                format!("Lambda checking failed: {}", e),
                                expected_ty.clone(),
                            )
                        })
                }
                _ => {
                    // Expected type is not a Pi type - create a fresh metavariable for param type
                    let loc = ctx.expr_location(&surface::Expression::Fun(fun.clone()));
                    ctx.error(
                        loc,
                        format!("Expected Pi type for lambda, got {:?}", expected_ty),
                        expected_ty,
                    )
                }
            }
        }
        surface::BindingGroup::Typed(_) => {
            let loc = ctx.convert_location(&fun.loc);
            ctx.error(
                loc,
                "Typed lambda parameters not yet supported".to_string(),
                expected_ty,
            )
        }
    }
}

async fn check_pi<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    pi: &surface::Pi,
    expected_ty: RcValue<'db>,
) -> TrustedSyntax<'db> {
    // Pi type checking: (x : A) -> B
    // The expected type should be a universe
    // TODO: Check that expected_ty is actually a universe

    if pi.bindings.groups.is_empty() {
        let loc = ctx.convert_location(&pi.loc);
        return ctx.error(loc, "Pi with no parameters".to_string(), expected_ty);
    }

    // For now, handle only a single typed binding group
    if pi.bindings.groups.len() > 1 {
        let loc = ctx.convert_location(&pi.loc);
        return ctx.error(
            loc,
            "Multiple parameter groups in Pi not yet supported".to_string(),
            expected_ty,
        );
    }

    let binding_group = &pi.bindings.groups[0];

    // Extract parameter names and type
    let param_names: Vec<String> = binding_group
        .binders
        .iter()
        .map(|b| match &**b {
            surface::Expression::Id(id) => std::str::from_utf8(&id.value)
                .unwrap_or("<invalid>")
                .to_string(),
            _ => "<complex>".to_string(),
        })
        .collect();

    // Elaborate the parameter type using synth to infer its universe level
    let param_ty_expr = &binding_group.ty;
    let param_ty_result = synth(ctx, param_ty_expr).await;
    let param_ty_term = Trusted(param_ty_result.subject.clone());
    let param_ty_type = param_ty_result.ty.clone();

    // Evaluate the parameter type to get a Value
    let param_ty_val = ctx.eval(&param_ty_term).unwrap_or_else(|e| {
        eprintln!("Failed to evaluate parameter type: {}", e);
        Rc::new(Value::universe(UniverseLevel::new(0)))
    });

    // The target type should also be checked against the same universe as the parameter type
    // Extract the universe level from param_ty_type
    let target_universe_ty = param_ty_type;

    // For simplicity, handle only single parameter for now
    if param_names.len() > 1 {
        let loc = ctx.expr_location(&surface::Expression::Pi(pi.clone()));
        return ctx.error(
            loc,
            "Multiple parameters in single group not yet supported".to_string(),
            expected_ty,
        );
    }

    let param_name = param_names[0].clone();

    // Push binding and elaborate target type
    ctx.push_binding(param_name, param_ty_val);
    let target_term = check(ctx, &pi.target, target_universe_ty).await;
    ctx.pop_binding();

    // Use the kernel API to construct the Pi term
    crate::rules::form_pi(param_ty_term, target_term)
        .await
        .unwrap_or_else(|e| {
            let loc = ctx.expr_location(&surface::Expression::Pi(pi.clone()));
            ctx.error(loc, format!("Pi formation failed: {}", e), expected_ty)
        })
}

async fn check_arrow<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    arrow: &surface::Arrow,
    expected_ty: RcValue<'db>,
) -> TrustedSyntax<'db> {
    // Arrow type: A -> B
    // Desugar to Pi with unused parameter: (_ : A) -> B

    let universe_ty = Rc::new(Value::universe(UniverseLevel::new(0))); // TODO: proper universe

    // Elaborate source type
    let source_term = check(ctx, &arrow.source, universe_ty.clone()).await;

    // Elaborate target type (no binding needed since parameter is unused)
    let target_term = check(ctx, &arrow.target, universe_ty).await;

    // Use the kernel API to construct the Pi term
    crate::rules::form_pi(source_term, target_term)
        .await
        .unwrap_or_else(|e| {
            let loc = ctx.expr_location(&surface::Expression::Arrow(arrow.clone()));
            ctx.error(loc, format!("Arrow formation failed: {}", e), expected_ty)
        })
}

async fn check_fat_arrow<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    fat_arrow: &surface::FatArrow,
    _expected_ty: RcValue<'db>,
) -> TrustedSyntax<'db> {
    // Hardware arrow type: A => B
    // This is the hardware arrow (HArrow) type constructor

    let signal_universe_ty = Rc::new(Value::signal_universe());
    let module_universe_ty = Rc::new(Value::module_universe());

    // Elaborate source type (should be a signal type)
    let source_term = check(ctx, &fat_arrow.source, signal_universe_ty).await;

    // Elaborate target type (should be a module type)
    let target_term = check(ctx, &fat_arrow.target, module_universe_ty).await;

    // Use the kernel API to construct the HArrow term
    crate::rules::form_harrow(source_term, target_term)
}

async fn synth_universe<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    univ: &surface::Universe,
) -> TrustedTypedSyntax<'db> {
    // Type : Type1, Type 0 : Type 1, Type n : Type (n+1)
    let level = univ.level.unwrap_or(0) as usize;
    let term = Trusted(Syntax::universe_rc(UniverseLevel::new(level)));
    let ty = Rc::new(Value::universe(UniverseLevel::new(level + 1)));
    Trusted(TypedSyntax {
        subject: term.unwrap(),
        ty,
    })
}

async fn synth_id<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    id: &surface::Id,
) -> TrustedTypedSyntax<'db> {
    let name = std::str::from_utf8(&id.value).unwrap_or("<invalid utf8>");
    let loc = ctx.convert_location(&id.loc);

    eprintln!("[Elaborator] synth_id: {}", name);

    let (term, ty) = match ctx.lookup_var(name) {
        Some(index) => {
            eprintln!("[Elaborator] Found variable {} at index {}", name, index);
            let ty = ctx.get_var_type(index).unwrap().clone();
            let term = crate::rules::var_ref(Index::from(index));
            (term, ty)
        }
        None => {
            eprintln!(
                "[Elaborator] Variable {} not in context, checking primitives",
                name
            );
            // Look up in primitive declarations
            if let Some(prim_info) = ctx.lookup_primitive(name) {
                eprintln!("[Elaborator] Found primitive: {}", name);
                (Trusted(prim_info.term.clone()), prim_info.ty.clone())
            } else {
                // Fall back to built-in primitives
                match name {
                    "Signal" => {
                        eprintln!("[Elaborator] Recognized Signal built-in");
                        let term = Trusted(Syntax::signal_universe_rc());
                        let ty = Rc::new(Value::universe(UniverseLevel::new(0)));
                        (term, ty)
                    }
                    _ => {
                        eprintln!("[Elaborator] Unknown identifier: {}", name);
                        let message = format!("Undefined variable: {}", name);
                        let error_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
                        let error_term = ctx.error(loc, message, error_ty.clone());
                        (error_term, error_ty)
                    }
                }
            }
        }
    };
    Trusted(TypedSyntax {
        subject: term.unwrap(),
        ty,
    })
}

async fn synth_app<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    app: &surface::App,
) -> TrustedTypedSyntax<'db> {
    // Application: f x y z
    // Synthesize the type of f, then check each argument

    if app.elements.is_empty() {
        let loc = ctx.convert_location(&app.loc);
        let message = "Empty application".to_string();
        let error_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
        let error_term = ctx.error(loc, message, error_ty.clone());
        return Trusted(TypedSyntax {
            subject: error_term.unwrap(),
            ty: error_ty,
        });
    }

    // If there's only one element, it's not really an application
    if app.elements.len() == 1 {
        return synth(ctx, &app.elements[0]).await;
    }

    // Synthesize the function type
    let func_result = synth(ctx, &app.elements[0]).await;
    let mut func_term = Trusted(func_result.subject.clone());
    let mut func_ty = func_result.ty.clone();

    // Apply each argument
    for arg_expr in &app.elements[1..] {
        // Force func_ty to weak head normal form
        func_ty = ctx.whnf(func_ty).await;

        // The function type should be a Pi type
        match &*func_ty {
            Value::Pi(pi) => {
                // Extract the argument type
                let arg_ty = pi.source.clone();

                // Check the argument
                let arg_term = check(ctx, arg_expr, arg_ty.clone()).await;

                // Create a temporary solver environment with the current local bindings
                // This is necessary because rules::synth_app needs to evaluate the argument term
                // in the correct environment (with all local bindings in scope)
                let temp_tc_env = hwml_core::check::TCEnvironment {
                    db: ctx.solver.tc_env.db,
                    values: hwml_core::val::Environment {
                        global: ctx.solver.tc_env.values.global,
                        local: ctx.build_value_env(),
                        transparent: hwml_core::val::TransparentEnv::new(),
                    },
                    types: ctx.types.clone(),
                };
                let temp_solver = crate::engine::SolverEnvironment {
                    state: ctx.solver.state.clone(),
                    tc_env: temp_tc_env,
                    spawner: ctx.solver.spawner.clone(),
                };

                // Use the kernel API to construct the application and get the result type
                match crate::rules::synth_app(
                    &temp_solver,
                    func_term,
                    func_ty.clone(),
                    arg_term,
                    arg_ty,
                )
                .await
                {
                    Ok((result_ty, app_term)) => {
                        func_term = app_term;
                        func_ty = result_ty;
                    }
                    Err(e) => {
                        let loc = ctx.expr_location(arg_expr);
                        let message = format!("Application failed: {}", e);
                        let error_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
                        let error_term = ctx.error(loc, message, error_ty.clone());
                        return Trusted(TypedSyntax {
                            subject: error_term.unwrap(),
                            ty: error_ty,
                        });
                    }
                }
            }
            _ => {
                // Function type is not a Pi - error
                let loc = ctx.expr_location(arg_expr);
                let message = format!("Expected function type, got {:?}", func_ty);
                let error_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
                let error_term = ctx.error(loc, message, error_ty.clone());
                return Trusted(TypedSyntax {
                    subject: error_term.unwrap(),
                    ty: error_ty,
                });
            }
        }
    }

    Trusted(TypedSyntax {
        subject: func_term.unwrap(),
        ty: func_ty,
    })
}

async fn synth_let<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    let_in: &surface::LetIn,
) -> TrustedTypedSyntax<'db> {
    // Let binding: let x : T = v in body
    // Elaborate the value, bind it, then elaborate the body

    let name = std::str::from_utf8(&let_in.id.value)
        .unwrap_or("<invalid>")
        .to_string();

    // Elaborate the type annotation if present
    let value_ty = if let Some(ty_expr) = &let_in.ty {
        let universe_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
        let ty_term = check(ctx, ty_expr, universe_ty.clone()).await;
        // Evaluate the type term to get a Value
        ctx.eval(&ty_term).unwrap_or_else(|e| {
            eprintln!("Failed to evaluate let type annotation: {}", e);
            universe_ty
        })
    } else {
        // No type annotation, synthesize
        let synth_result = synth(ctx, &let_in.value).await;
        synth_result.ty.clone()
    };

    // Elaborate the value
    let value_term = check(ctx, &let_in.value, value_ty.clone()).await;

    // Quote the value type to syntax before moving value_ty
    let value_ty_syntax = type_quote(ctx.solver.tc_env.values.global, 0, &value_ty)
        .unwrap_or_else(|_| Syntax::universe_rc(UniverseLevel::new(0)));

    // Push binding and elaborate body
    ctx.push_binding(name, value_ty);
    let body_result = synth(ctx, &let_in.expr).await;
    let body_term = Trusted(body_result.subject.clone());
    let body_ty = body_result.ty.clone();
    ctx.pop_binding();

    // Use the kernel API to construct the let term
    let let_term = crate::rules::form_let(Trusted(value_ty_syntax), value_term, body_term);

    Trusted(TypedSyntax {
        subject: let_term.unwrap(),
        ty: body_ty,
    })
}

async fn synth_num<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    num: &surface::Num,
) -> TrustedTypedSyntax<'db> {
    // Numeric literals: 0 and 1 are the only valid bit values
    let loc = ctx.convert_location(&num.loc);
    let num_str = std::str::from_utf8(&num.value).unwrap_or("0");

    let (term, ty) = match num_str {
        "0" => {
            // Zero : Bit
            (Trusted(Syntax::zero_rc()), Rc::new(Value::bit()))
        }
        "1" => {
            // One : Bit
            (Trusted(Syntax::one_rc()), Rc::new(Value::bit()))
        }
        _ => {
            // Invalid numeric literal - only 0 and 1 are supported for Bit
            let message = format!(
                "Invalid numeric literal '{}': only 0 and 1 are supported",
                num_str
            );
            let error_ty = Rc::new(Value::bit());
            let error_term = ctx.error(loc, message, error_ty.clone());
            (error_term, error_ty)
        }
    };

    Trusted(TypedSyntax {
        subject: term.unwrap(),
        ty,
    })
}
