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

use hwml_core::common::{Index, Location, UniverseLevel};
use hwml_core::eval;
use hwml_core::quote::type_quote;
use hwml_core::syn::{Syntax, SyntaxData};
use hwml_core::val::{Closure, Environment, LocalEnv, TransparentEnv, Value};
use hwml_support::{LocationData, SourceFile};
use hwml_surface::syntax as surface;
use std::collections::HashMap;
use std::rc::Rc;

use crate::engine::SolverEnvironment;
use crate::force::force;
use crate::unify::unify;

/// A diagnostic message collected during elaboration.
#[derive(Clone, Debug)]
pub struct Diagnostic {
    /// The location where the error occurred
    pub location: Location,
    /// The error message
    pub message: String,
    /// The expected type (if applicable)
    pub expected_type: Option<Rc<Value<'static>>>,
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
    types: Vec<Rc<Value<'db>>>,

    /// Collected diagnostics
    diagnostics: Vec<Diagnostic>,
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
            diagnostics: Vec::new(),
        }
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
            expected_type: None,
        });
    }

    /// Public wrapper for synth that can be called from pipeline
    pub async fn synth_expr(
        &mut self,
        expr: &surface::Expression,
    ) -> Result<(Rc<Syntax<'db>>, Rc<Value<'db>>), String> {
        Ok(synth(self, expr).await)
    }

    /// Public wrapper for check that can be called from pipeline
    pub async fn check_expr(
        &mut self,
        expr: &surface::Expression,
        expected_ty: Rc<Value<'db>>,
    ) -> Result<Rc<Syntax<'db>>, String> {
        Ok(check(self, expr, expected_ty).await)
    }

    /// Convert a surface AST location (Range<usize>) to a Salsa-interned Location
    fn convert_location(&self, range: &std::ops::Range<usize>) -> Location {
        // For now, just use UNKNOWN since we've simplified Location to not track source info
        // TODO: Implement proper location tracking with a location allocator
        Location::UNKNOWN
    }

    /// Push a new binding onto the scope
    pub fn push_binding(&mut self, name: String, ty: Rc<Value<'db>>) {
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
    pub fn get_var_type(&self, index: usize) -> Option<&Rc<Value<'db>>> {
        let level = self.scope.len().checked_sub(index + 1)?;
        self.types.get(level)
    }

    /// Get the current de Bruijn level (depth of the scope)
    pub fn level(&self) -> usize {
        self.scope.len()
    }

    /// Extract location from a surface expression
    fn expr_location(&self, expr: &surface::Expression) -> Location {
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
            Expression::Quote(q) => self.expr_location(&q.expr),
            Expression::Splice(s) => self.expr_location(&s.expr),
            Expression::Raise(r) => self.expr_location(&r.expr),
            Expression::Str(_) => Location::UNKNOWN,
        }
    }

    /// Create a fresh metavariable with the given type
    pub fn fresh_meta(&self, loc: Location, ty: Rc<Value<'db>>) -> Rc<Syntax<'db>> {
        let meta_id = self.solver.fresh_meta_id(ty);
        Syntax::metavariable_rc(loc, meta_id, vec![])
    }

    /// Create a poisoned metavariable for error recovery
    pub fn fresh_poisoned_meta(&self, loc: Location, ty: Rc<Value<'db>>) -> Rc<Syntax<'db>> {
        // Create a poisoned metavariable ID
        let meta_id = self
            .solver
            .state
            .borrow_mut()
            .fresh_poisoned_meta(loc, ty.clone());
        Syntax::metavariable_rc(loc, meta_id, vec![])
    }

    /// Report an error and return a poisoned metavariable
    pub fn error(
        &mut self,
        loc: Location,
        message: String,
        expected_ty: Rc<Value<'db>>,
    ) -> Rc<Syntax<'db>> {
        // Collect the diagnostic instead of printing
        self.diagnostics.push(Diagnostic {
            location: loc,
            message,
            expected_type: None, // We could store this if needed for better error messages
        });
        self.fresh_poisoned_meta(loc, expected_ty)
    }

    /// Evaluate a syntax term to a value in the current context
    fn eval(&self, term: &Syntax<'db>) -> Result<Rc<Value<'db>>, eval::Error> {
        let mut env = Environment {
            global: self.solver.tc_env.values.global,
            local: self.build_value_env(),
            transparent: TransparentEnv::new(),
        };
        eval::eval(&mut env, term)
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
    async fn whnf(&self, value: Rc<Value<'db>>) -> Rc<Value<'db>> {
        // Use the force function from hwml-elab to substitute solved metavariables
        force(&self.solver, value).unwrap_or_else(|e| {
            eprintln!("Warning: force failed during whnf: {}", e);
            // Return a poisoned meta on error
            let error_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
            self.solver.fresh_poisoned_meta(error_ty)
        })
    }
}

#[async_recursion::async_recursion(?Send)]
pub async fn check<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    expr: &surface::Expression,
    expected_ty: Rc<Value<'db>>,
) -> Rc<Syntax<'db>> {
    use surface::Expression;

    match expr {
        Expression::Fun(fun) => check_fun(ctx, fun, expected_ty).await,
        Expression::Pi(pi) => check_pi(ctx, pi, expected_ty).await,
        Expression::Arrow(arrow) => check_arrow(ctx, arrow, expected_ty).await,
        Expression::Underscore(underscore) => {
            let loc = ctx.convert_location(&underscore.loc);
            ctx.fresh_meta(loc, expected_ty)
        }
        _ => {
            let (term, inferred_ty) = synth(ctx, expr).await;
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
) -> (Rc<Syntax<'db>>, Rc<Value<'db>>) {
    use surface::Expression;

    match expr {
        Expression::Id(id) => synth_id(ctx, id).await,
        Expression::App(app) => synth_app(ctx, app).await,
        Expression::LetIn(let_in) => synth_let(ctx, let_in).await,
        Expression::Paren(paren) => synth(ctx, &paren.expr).await,
        Expression::Fun(_) | Expression::Pi(_) | Expression::Arrow(_) => {
            let loc = ctx.expr_location(expr);
            let message = "Cannot infer type for lambda/pi without annotation".to_string();
            let error_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
            let error_term = ctx.error(loc, message, error_ty.clone());
            (error_term, error_ty)
        }
        Expression::Underscore(_) => {
            let loc = ctx.expr_location(expr);
            let message = "Cannot infer type for underscore".to_string();
            let error_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
            let error_term = ctx.error(loc, message, error_ty.clone());
            (error_term, error_ty)
        }
        _ => {
            let loc = ctx.expr_location(expr);
            let message = format!("Elaboration not yet implemented for this expression");
            let error_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
            let error_term = ctx.error(loc, message, error_ty.clone());
            (error_term, error_ty)
        }
    }
}

// Helper functions for specific expression types

async fn check_fun<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    fun: &surface::Fun,
    expected_ty: Rc<Value<'db>>,
) -> Rc<Syntax<'db>> {
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

                    // Build the lambda term
                    let loc = ctx.expr_location(&surface::Expression::Fun(fun.clone()));
                    Syntax::lambda_rc(loc, body)
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
    expected_ty: Rc<Value<'db>>,
) -> Rc<Syntax<'db>> {
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

    // Elaborate the parameter type
    let param_ty_expr = &binding_group.ty;
    let universe_ty = Rc::new(Value::universe(UniverseLevel::new(0))); // TODO: proper universe
    let param_ty_term = check(ctx, param_ty_expr, universe_ty.clone()).await;

    // Evaluate the parameter type to get a Value
    let param_ty_val = ctx.eval(&param_ty_term).unwrap_or_else(|e| {
        eprintln!("Failed to evaluate parameter type: {}", e);
        universe_ty.clone()
    });

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
    let target_term = check(ctx, &pi.target, universe_ty).await;
    ctx.pop_binding();

    // Build Pi term
    let loc = ctx.expr_location(&surface::Expression::Pi(pi.clone()));
    Syntax::pi_rc(loc, param_ty_term, target_term)
}

async fn check_arrow<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    arrow: &surface::Arrow,
    expected_ty: Rc<Value<'db>>,
) -> Rc<Syntax<'db>> {
    // Arrow type: A -> B
    // Desugar to Pi with unused parameter: (_ : A) -> B

    let universe_ty = Rc::new(Value::universe(UniverseLevel::new(0))); // TODO: proper universe

    // Elaborate source type
    let source_term = check(ctx, &arrow.source, universe_ty.clone()).await;

    // Elaborate target type (no binding needed since parameter is unused)
    let target_term = check(ctx, &arrow.target, universe_ty).await;

    // Build Pi term
    let loc = ctx.expr_location(&surface::Expression::Arrow(arrow.clone()));
    Syntax::pi_rc(loc, source_term, target_term)
}

async fn synth_id<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    id: &surface::Id,
) -> (Rc<Syntax<'db>>, Rc<Value<'db>>) {
    let name = std::str::from_utf8(&id.value).unwrap_or("<invalid utf8>");
    let loc = ctx.convert_location(&id.loc);

    match ctx.lookup_var(name) {
        Some(index) => {
            let ty = ctx.get_var_type(index).unwrap().clone();
            let term = Syntax::variable_rc(loc, Index::from(index));
            (term, ty)
        }
        None => {
            let message = format!("Undefined variable: {}", name);
            let error_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
            let error_term = ctx.error(loc, message, error_ty.clone());
            (error_term, error_ty)
        }
    }
}

async fn synth_app<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    app: &surface::App,
) -> (Rc<Syntax<'db>>, Rc<Value<'db>>) {
    // Application: f x y z
    // Synthesize the type of f, then check each argument

    if app.elements.is_empty() {
        let loc = ctx.convert_location(&app.loc);
        let message = "Empty application".to_string();
        let error_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
        let error_term = ctx.error(loc, message, error_ty.clone());
        return (error_term, error_ty);
    }

    // If there's only one element, it's not really an application
    if app.elements.len() == 1 {
        return synth(ctx, &app.elements[0]).await;
    }

    // Synthesize the function type
    let (mut func_term, mut func_ty) = synth(ctx, &app.elements[0]).await;

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

                // Evaluate the argument to apply the Pi closure
                let arg_val = ctx.eval(&arg_term).unwrap_or_else(|e| {
                    eprintln!("Failed to evaluate argument: {}", e);
                    Rc::new(Value::universe(UniverseLevel::new(0)))
                });

                // Apply the closure to get the result type
                func_ty = eval::run_closure(
                    ctx.solver.tc_env.values.global,
                    &pi.target,
                    std::iter::once(arg_val),
                )
                .unwrap_or_else(|e| {
                    eprintln!("Failed to apply Pi closure: {}", e);
                    Rc::new(Value::universe(UniverseLevel::new(0)))
                });

                // Build application
                let loc = ctx.expr_location(&surface::Expression::App(app.clone()));
                func_term = Syntax::application_rc(loc, func_term, arg_term);
            }
            _ => {
                // Function type is not a Pi - error
                let loc = ctx.expr_location(arg_expr);
                let message = format!("Expected function type, got {:?}", func_ty);
                let error_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
                let error_term = ctx.error(loc, message, error_ty.clone());
                return (error_term, error_ty);
            }
        }
    }

    (func_term, func_ty)
}

async fn synth_let<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    let_in: &surface::LetIn,
) -> (Rc<Syntax<'db>>, Rc<Value<'db>>) {
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
        let (_, inferred_ty) = synth(ctx, &let_in.value).await;
        inferred_ty
    };

    // Elaborate the value
    let value_term = check(ctx, &let_in.value, value_ty.clone()).await;

    // Quote the value type to syntax before moving value_ty
    let value_ty_syntax = type_quote(ctx.solver.tc_env.values.global, 0, &value_ty)
        .unwrap_or_else(|_| Syntax::universe_rc(Location::UNKNOWN, UniverseLevel::new(0)));

    // Push binding and elaborate body
    ctx.push_binding(name, value_ty);
    let (body_term, body_ty) = synth(ctx, &let_in.expr).await;
    ctx.pop_binding();

    // Build let term
    let loc = ctx.expr_location(&surface::Expression::LetIn(let_in.clone()));
    let let_term = Syntax::let_rc(loc, value_ty_syntax, value_term, body_term);

    (let_term, body_ty)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::{SingleThreadedExecutor, SolverEnvironment, SolverState};
    use hwml_core::check::TCEnvironment;
    use hwml_core::env::Environment;
    use hwml_core::global::GlobalEnv;

    fn setup_test_context<'db>(
        db: &'db dyn salsa::Database,
    ) -> (GlobalEnv<'db>, ElaborationContext<'db, 'static>) {
        let global = GlobalEnv::new(db);
        let executor = SingleThreadedExecutor::new();
        let tc_env = TCEnvironment {
            db,
            values: Environment::new(&global),
            types: Vec::new(),
        };
        let solver = SolverEnvironment::new(tc_env, executor.spawner());
        let elab_ctx = ElaborationContext::new(db, None, solver);
        (global, elab_ctx)
    }

    #[test]
    fn test_context_scope() {
        // Test basic scope operations
        let db = salsa::DatabaseImpl::default();
        let (_global, mut ctx) = setup_test_context(&db);

        // Initially empty
        assert_eq!(ctx.level(), 0);
        assert_eq!(ctx.lookup_var("x"), None);

        // Push a binding
        let ty = Rc::new(Value::universe(UniverseLevel::new(0)));
        ctx.push_binding("x".to_string(), ty.clone());
        assert_eq!(ctx.level(), 1);
        assert_eq!(ctx.lookup_var("x"), Some(0));

        // Push another binding
        ctx.push_binding("y".to_string(), ty.clone());
        assert_eq!(ctx.level(), 2);
        assert_eq!(ctx.lookup_var("y"), Some(0)); // Most recent
        assert_eq!(ctx.lookup_var("x"), Some(1)); // One level out

        // Pop a binding
        ctx.pop_binding();
        assert_eq!(ctx.level(), 1);
        assert_eq!(ctx.lookup_var("x"), Some(0));
        assert_eq!(ctx.lookup_var("y"), None);
    }

    #[test]
    fn test_fresh_meta() {
        let db = salsa::DatabaseImpl::default();
        let (_global, ctx) = setup_test_context(&db);

        let ty = Rc::new(Value::universe(UniverseLevel::new(0)));
        let loc = Location::unknown(&db);
        let meta = ctx.fresh_meta(loc, ty.clone());

        // Should be a metavariable
        assert!(matches!(&meta.data, SyntaxData::Metavariable(_)));
    }

    #[test]
    fn test_fresh_poisoned_meta() {
        let db = salsa::DatabaseImpl::default();
        let (_global, ctx) = setup_test_context(&db);

        let ty = Rc::new(Value::universe(UniverseLevel::new(0)));
        let loc = Location::unknown(&db);
        let meta = ctx.fresh_poisoned_meta(loc, ty.clone());

        // Should be a metavariable
        assert!(
            matches!(&meta.data, SyntaxData::Metavariable(m) if ctx.solver.state.borrow().is_poisoned(m.id))
        );
    }

    #[test]
    fn test_location_tracking() {
        let db = salsa::DatabaseImpl::default();
        let (_global, _ctx) = setup_test_context(&db);

        // Test that we can create physical locations
        let source = SourceFile::new(&db, "test.hwml".to_string(), "fun x => x".to_string());
        let loc = Location::physical(&db, source, 0, 10);

        // Verify location data
        assert_eq!(loc.display(&db), "test.hwml:0..10");
        assert_eq!(loc.snippet(&db), Some("fun x => x"));
    }

    #[test]
    fn test_diagnostic_collection() {
        let db = salsa::DatabaseImpl::default();
        let (_global, mut ctx) = setup_test_context(&db);

        // Initially no diagnostics
        assert_eq!(ctx.diagnostics().len(), 0);

        // Report an error
        let ty = Rc::new(Value::universe(UniverseLevel::new(0)));
        let loc = Location::unknown(&db);
        let _error_term = ctx.error(loc, "Test error".to_string(), ty.clone());

        // Should have one diagnostic
        assert_eq!(ctx.diagnostics().len(), 1);
        assert_eq!(ctx.diagnostics()[0].message, "Test error");

        // Report another error
        let _error_term2 = ctx.error(loc, "Another error".to_string(), ty);

        // Should have two diagnostics
        assert_eq!(ctx.diagnostics().len(), 2);
        assert_eq!(ctx.diagnostics()[1].message, "Another error");
    }

    // TODO: Add more tests once evaluation and unification are integrated
    // - test_synth_variable
    // - test_check_lambda
    // - test_synth_application
    // - test_check_pi
    // - test_error_recovery
}
