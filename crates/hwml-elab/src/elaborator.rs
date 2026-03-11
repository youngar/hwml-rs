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
use hwml_core::syn::{CaseBranch, Syntax, SyntaxData};
use hwml_core::val::{Environment, LocalEnv, TransparentEnv, Value};
use hwml_core::ConstantId;
use hwml_support::{FromWithDb, SourceFile};
use hwml_surface::syntax as surface;
use std::collections::HashMap;
use std::rc::Rc;

use crate::engine::SolverEnvironment;
use crate::force::force;
use crate::unify::unify;

// ============================================================================
// Pattern Matching Compilation
// ============================================================================

/// A pattern from the surface AST, used in pattern matching compilation.
#[derive(Clone, Debug)]
pub enum Pat {
    /// Variable pattern: binds the scrutinee to a name
    Var(String),
    /// Constructor pattern: matches a specific constructor with sub-patterns
    Constructor(ConstantId<'static>, Vec<Pat>),
    /// Wildcard pattern: matches anything without binding
    Wildcard,
}

/// A single row in the pattern matrix.
/// Represents one clause from the user's match expression.
#[derive(Clone, Debug)]
pub struct Clause {
    /// The patterns for this clause (one per scrutinee)
    pub patterns: Vec<Pat>,
    /// The body expression to evaluate if this clause matches
    pub body: Box<surface::Expression>,
}

/// The pattern matrix: a collection of clauses being compiled.
#[derive(Clone, Debug)]
pub struct Matrix {
    /// The rows of the matrix
    pub rows: Vec<Clause>,
}

impl Matrix {
    /// Create a new empty matrix
    pub fn new() -> Self {
        Matrix { rows: Vec::new() }
    }

    /// Check if the first row consists only of variables and wildcards
    pub fn is_pure_variable_row(&self, row_idx: usize) -> bool {
        if row_idx >= self.rows.len() {
            return false;
        }
        self.rows[row_idx]
            .patterns
            .iter()
            .all(|p| matches!(p, Pat::Var(_) | Pat::Wildcard))
    }
}

// ============================================================================
// Diagnostics and Context
// ============================================================================

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

/// Information about a declared primitive
#[derive(Clone, Debug)]
pub struct PrimitiveInfo<'db> {
    /// The elaborated type of the primitive
    pub ty: Rc<Value<'db>>,
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
    types: Vec<Rc<Value<'db>>>,

    /// Primitive declarations: maps primitive names to their types and terms
    primitives: std::collections::HashMap<String, PrimitiveInfo<'db>>,

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
    pub fn convert_location(&self, _range: &std::ops::Range<usize>) -> Location {
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
    pub fn eval(&self, term: &Syntax<'db>) -> Result<Rc<Value<'db>>, eval::Error> {
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

    // ========================================================================
    // Pattern Matching Helpers
    // ========================================================================

    /// Generate a fresh variable name for pattern matching
    fn fresh_var_name(&self, prefix: &str, index: usize) -> String {
        format!("{}_{}", prefix, index)
    }

    /// Look up the arity of a data constructor from the global environment
    fn get_constructor_arity(&self, ctor: ConstantId<'db>) -> Result<usize, String> {
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

    /// Parse a surface expression as a pattern
    fn parse_pattern(&self, expr: &surface::Expression) -> Result<Pat, String> {
        use surface::Expression;
        match expr {
            // Variable pattern: any identifier
            Expression::Id(id) => {
                let name = std::str::from_utf8(&id.value)
                    .map_err(|_| "Invalid UTF-8 in pattern variable")?
                    .to_string();

                // Check if this is a constructor (starts with @) or a variable
                if name.starts_with('@') {
                    // Constructor with no arguments
                    // SAFETY: We're creating a ConstantId with 'static lifetime because
                    // patterns need to outlive the elaboration context. The string is
                    // interned in the database which has a 'static lifetime.
                    let ctor_id: ConstantId<'static> = unsafe {
                        std::mem::transmute(ConstantId::from_with_db(
                            self.solver.tc_env.db,
                            &name[1..],
                        ))
                    };
                    Ok(Pat::Constructor(ctor_id, Vec::new()))
                } else {
                    Ok(Pat::Var(name))
                }
            }
            // Wildcard pattern
            Expression::Underscore(_) => Ok(Pat::Wildcard),
            // Constructor application: @Cons x xs
            Expression::App(app) => {
                if app.elements.is_empty() {
                    return Err("Empty application in pattern".to_string());
                }

                // First element should be a constructor
                let ctor_pat = self.parse_pattern(&app.elements[0])?;
                match ctor_pat {
                    Pat::Constructor(ctor_id, inner_pats) => {
                        if !inner_pats.is_empty() {
                            return Err("Nested constructor in pattern head".to_string());
                        }
                        // Parse the rest as sub-patterns
                        let mut sub_pats = Vec::new();
                        for elem in &app.elements[1..] {
                            sub_pats.push(self.parse_pattern(elem)?);
                        }
                        Ok(Pat::Constructor(ctor_id, sub_pats))
                    }
                    _ => Err("Pattern application must start with a constructor".to_string()),
                }
            }
            Expression::Paren(paren) => self.parse_pattern(&paren.expr),
            _ => Err(format!("Invalid pattern: {:?}", expr)),
        }
    }

    /// Synthesize a motive for pattern matching by abstracting the expected type
    /// over the scrutinee variable.
    ///
    /// Given an expected type and a scrutinee term, this creates a closure
    /// that abstracts over the scrutinee: λz. expected_type[scrutinee := z]
    fn synthesize_motive(
        &self,
        expected_ty: &Rc<Value<'db>>,
        _scrutinee: &Rc<Syntax<'db>>,
    ) -> Result<hwml_core::syn::Closure<'db>, String> {
        // Quote the expected type to syntax
        let expected_ty_syntax =
            type_quote(self.solver.tc_env.values.global, self.depth(), expected_ty)
                .map_err(|e| format!("Failed to quote expected type: {:?}", e))?;

        // For now, we create a simple closure that just returns the expected type
        // TODO: In a full implementation, we would need to:
        // 1. Identify occurrences of the scrutinee in the expected type
        // 2. Replace them with variable 0 (the bound variable in the closure)
        // 3. Properly handle dependent types
        //
        // For simple cases where the expected type doesn't depend on the scrutinee,
        // this is sufficient: λz. expected_ty
        Ok(hwml_core::syn::Closure::new(expected_ty_syntax))
    }

    // ========================================================================
    // Implicit Lifting Helpers
    // ========================================================================

    /// Check if a type requires lifting from object-level to meta-level.
    /// Returns Some(inner_ty) if expected_ty is Lift(inner_ty), None otherwise.
    fn is_lift_type(&self, ty: &Value<'db>) -> Option<Rc<Value<'db>>> {
        match ty {
            Value::Lift(lift) => Some(lift.ty.clone()),
            _ => None,
        }
    }

    /// Check if a type requires signal lifting.
    /// Returns Some(inner_ty) if expected_ty is SLift(inner_ty), None otherwise.
    fn is_slift_type(&self, ty: &Value<'db>) -> Option<Rc<Value<'db>>> {
        match ty {
            Value::SLift(slift) => Some(slift.ty.clone()),
            _ => None,
        }
    }

    /// Check if a type requires module lifting.
    /// Returns Some(inner_ty) if expected_ty is MLift(inner_ty), None otherwise.
    fn is_mlift_type(&self, ty: &Value<'db>) -> Option<Rc<Value<'db>>> {
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
    expected_ty: Rc<Value<'db>>,
) -> Rc<Syntax<'db>> {
    use surface::Expression;

    match expr {
        Expression::Fun(fun) => check_fun(ctx, fun, expected_ty).await,
        Expression::Pi(pi) => check_pi(ctx, pi, expected_ty).await,
        Expression::Arrow(arrow) => check_arrow(ctx, arrow, expected_ty).await,
        Expression::FatArrow(fat_arrow) => check_fat_arrow(ctx, fat_arrow, expected_ty).await,
        Expression::Match(match_expr) => check_match(ctx, match_expr, expected_ty).await,
        Expression::Underscore(underscore) => {
            let loc = ctx.convert_location(&underscore.loc);
            ctx.fresh_meta(loc, expected_ty)
        }
        _ => {
            let (term, inferred_ty) = synth(ctx, expr).await;

            // Check if we need to insert implicit lifting
            if let Some(lift_kind) = ctx.should_insert_lift(&expected_ty, &inferred_ty) {
                let loc = ctx.expr_location(expr);

                // Insert the appropriate lifting construct
                let lifted_term = match lift_kind {
                    LiftKind::Lift => Syntax::lift_rc(loc, term),
                    LiftKind::SLift => Syntax::slift_rc(loc, term),
                    LiftKind::MLift => Syntax::mlift_rc(loc, term),
                };

                // The lifted term should now have the expected type
                // We still verify this with unification
                let lifted_ty = match lift_kind {
                    LiftKind::Lift => Rc::new(Value::lift(inferred_ty)),
                    LiftKind::SLift => Rc::new(Value::slift(inferred_ty)),
                    LiftKind::MLift => Rc::new(Value::mlift(inferred_ty)),
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
) -> (Rc<Syntax<'db>>, Rc<Value<'db>>) {
    use surface::Expression;

    match expr {
        Expression::Id(id) => synth_id(ctx, id).await,
        Expression::App(app) => synth_app(ctx, app).await,
        Expression::LetIn(let_in) => synth_let(ctx, let_in).await,
        Expression::Paren(paren) => synth(ctx, &paren.expr).await,
        Expression::Num(num) => synth_num(ctx, num).await,
        Expression::Fun(_) | Expression::Pi(_) | Expression::Arrow(_) | Expression::FatArrow(_) => {
            let loc = ctx.expr_location(expr);
            let message = "Cannot infer type for lambda/pi/arrow without annotation".to_string();
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
        Expression::Str(_) => {
            let loc = ctx.expr_location(expr);
            let message = "String literals not yet supported".to_string();
            let error_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
            let error_term = ctx.error(loc, message, error_ty.clone());
            (error_term, error_ty)
        }
        Expression::Match(_) => {
            let loc = ctx.expr_location(expr);
            let message = "Cannot infer type for match expression without annotation".to_string();
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
    _expected_ty: Rc<Value<'db>>,
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

async fn check_fat_arrow<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    fat_arrow: &surface::FatArrow,
    _expected_ty: Rc<Value<'db>>,
) -> Rc<Syntax<'db>> {
    // Hardware arrow type: A => B
    // This is the hardware arrow (HArrow) type constructor

    let signal_universe_ty = Rc::new(Value::signal_universe());
    let module_universe_ty = Rc::new(Value::module_universe());

    // Elaborate source type (should be a signal type)
    let source_term = check(ctx, &fat_arrow.source, signal_universe_ty).await;

    // Elaborate target type (should be a module type)
    let target_term = check(ctx, &fat_arrow.target, module_universe_ty).await;

    // Build HArrow term
    let loc = ctx.expr_location(&surface::Expression::FatArrow(fat_arrow.clone()));
    Syntax::harrow_rc(loc, source_term, target_term)
}

async fn synth_id<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    id: &surface::Id,
) -> (Rc<Syntax<'db>>, Rc<Value<'db>>) {
    let name = std::str::from_utf8(&id.value).unwrap_or("<invalid utf8>");
    let loc = ctx.convert_location(&id.loc);

    eprintln!("[Elaborator] synth_id: {}", name);

    match ctx.lookup_var(name) {
        Some(index) => {
            eprintln!("[Elaborator] Found variable {} at index {}", name, index);
            let ty = ctx.get_var_type(index).unwrap().clone();
            let term = Syntax::variable_rc(loc, Index::from(index));
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
                (prim_info.term.clone(), prim_info.ty.clone())
            } else {
                // Fall back to built-in primitives
                match name {
                    "Signal" => {
                        eprintln!("[Elaborator] Recognized Signal built-in");
                        let term = Syntax::signal_universe_rc(loc);
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

async fn synth_num<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    num: &surface::Num,
) -> (Rc<Syntax<'db>>, Rc<Value<'db>>) {
    // Numeric literals: 0 and 1 are the only valid bit values
    let loc = ctx.convert_location(&num.loc);
    let num_str = std::str::from_utf8(&num.value).unwrap_or("0");

    let (term, ty) = match num_str {
        "0" => {
            // Zero : Bit
            (Syntax::zero_rc(loc), Rc::new(Value::bit()))
        }
        "1" => {
            // One : Bit
            (Syntax::one_rc(loc), Rc::new(Value::bit()))
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

    (term, ty)
}

// ============================================================================
// Pattern Matching Compilation
// ============================================================================

/// Elaborate a match expression into a case tree with transport.
/// This is the main entry point for pattern matching elaboration.
#[async_recursion::async_recursion(?Send)]
async fn check_match<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    match_expr: &surface::Match,
    expected_ty: Rc<Value<'db>>,
) -> Rc<Syntax<'db>> {
    let loc = ctx.expr_location(&surface::Expression::Match(match_expr.clone()));

    // Step 1: Infer the scrutinee and bind it to a rigid variable
    let (scrutinee_term, scrutinee_ty) = synth(ctx, &match_expr.scrutinee).await;

    // Generate a fresh name for the scrutinee variable
    let scrutinee_var_name = ctx.fresh_var_name("scrut", 0);

    // Step 2: Generate the equality proof variable name
    let proof_var_name = ctx.fresh_var_name("p_eq", 0);

    // Step 3: Synthesize the motive
    let motive = match ctx.synthesize_motive(&expected_ty, &scrutinee_term) {
        Ok(m) => m,
        Err(e) => {
            return ctx.error(
                loc,
                format!("Failed to synthesize motive: {}", e),
                expected_ty,
            );
        }
    };

    // Step 4: Build the pattern matrix from the surface clauses
    let mut matrix_rows = Vec::new();
    for clause in &match_expr.clauses {
        // Parse the pattern
        let pattern = match ctx.parse_pattern(&clause.pattern) {
            Ok(p) => p,
            Err(e) => {
                ctx.diagnostics.push(Diagnostic {
                    location: loc,
                    message: format!("Invalid pattern: {}", e),
                    expected_type: None,
                });
                continue;
            }
        };

        matrix_rows.push(Clause {
            patterns: vec![pattern],
            body: clause.body.clone(),
        });
    }

    let matrix = Matrix { rows: matrix_rows };

    // Step 5: Push the scrutinee binding
    ctx.push_binding(scrutinee_var_name.clone(), scrutinee_ty.clone());
    let scrutinee_var = Syntax::variable_rc(loc, Index::from(0));

    // Step 6: Push the proof binding (p : Eq scrutinee_ty scrutinee scrutinee = refl)
    // For now, we create a simple proof type
    let proof_ty = Syntax::eq_rc(
        loc,
        type_quote(ctx.solver.tc_env.values.global, ctx.depth(), &scrutinee_ty)
            .unwrap_or_else(|_| Syntax::universe_rc(loc, UniverseLevel::new(0))),
        scrutinee_term.clone(),
        scrutinee_var.clone(),
    );
    let proof_ty_val = ctx
        .eval(&proof_ty)
        .unwrap_or_else(|_| Rc::new(Value::universe(UniverseLevel::new(0))));
    ctx.push_binding(proof_var_name.clone(), proof_ty_val);

    // Step 7: Run the pattern matrix compiler
    let decision_tree = match compile_matrix(
        ctx,
        vec![scrutinee_var.clone()],
        matrix,
        &motive,
        &proof_var_name,
        &expected_ty,
    )
    .await
    {
        Ok(tree) => tree,
        Err(e) => {
            ctx.pop_binding(); // Pop proof
            ctx.pop_binding(); // Pop scrutinee
            return ctx.error(
                loc,
                format!("Pattern compilation failed: {}", e),
                expected_ty,
            );
        }
    };

    // Pop the bindings
    ctx.pop_binding(); // Pop proof
    ctx.pop_binding(); // Pop scrutinee

    // Step 8: Wrap in let bindings for the scrutinee and proof
    // let p = refl in decision_tree
    let refl_proof = Syntax::refl_rc(loc);
    let with_proof = Syntax::let_rc(loc, proof_ty, refl_proof, decision_tree);

    // let scrut = scrutinee_term in with_proof
    let scrutinee_ty_syntax =
        type_quote(ctx.solver.tc_env.values.global, ctx.depth(), &scrutinee_ty)
            .unwrap_or_else(|_| Syntax::universe_rc(loc, UniverseLevel::new(0)));
    Syntax::let_rc(loc, scrutinee_ty_syntax, scrutinee_term, with_proof)
}

/// Group matrix rows by their outer constructor in the first column.
/// Returns a list of (constructor, arity, specialized_matrix) tuples.
fn group_by_constructor<'db, 'g>(
    ctx: &ElaborationContext<'db, 'g>,
    matrix: &Matrix,
) -> Result<Vec<(ConstantId<'db>, usize, Matrix)>, String> {
    let mut groups: HashMap<String, Vec<Clause>> = HashMap::new();

    for clause in &matrix.rows {
        if clause.patterns.is_empty() {
            continue;
        }

        match &clause.patterns[0] {
            Pat::Constructor(ctor_id, sub_pats) => {
                let ctor_name = ctor_id.name(ctx.solver.tc_env.db).to_string();

                // Specialize this row: replace the constructor pattern with its sub-patterns
                let mut new_patterns = sub_pats.clone();
                new_patterns.extend_from_slice(&clause.patterns[1..]);

                let specialized_clause = Clause {
                    patterns: new_patterns,
                    body: clause.body.clone(),
                };

                groups
                    .entry(ctor_name)
                    .or_insert_with(Vec::new)
                    .push(specialized_clause);
            }
            Pat::Var(_) | Pat::Wildcard => {
                // Variable/wildcard patterns match all constructors
                // We need to handle this by duplicating the row for each constructor
                // For now, we'll skip this and handle it in a more complete implementation
                return Err(
                    "Variable/wildcard patterns in non-final position not yet supported"
                        .to_string(),
                );
            }
        }
    }

    // Convert groups to the result format
    let mut result = Vec::new();
    for (ctor_name, clauses) in groups {
        let ctor_id: ConstantId<'db> = ConstantId::from_with_db(ctx.solver.tc_env.db, &ctor_name);
        let arity = ctx.get_constructor_arity(ctor_id)?;
        let specialized_matrix = Matrix { rows: clauses };
        result.push((ctor_id, arity, specialized_matrix));
    }

    Ok(result)
}

/// The core pattern matrix compilation algorithm.
/// Recursively compiles a pattern matrix into a case tree.
#[async_recursion::async_recursion(?Send)]
async fn compile_matrix<'db, 'g>(
    ctx: &mut ElaborationContext<'db, 'g>,
    scrutinees: Vec<Rc<Syntax<'db>>>,
    matrix: Matrix,
    motive: &hwml_core::syn::Closure<'db>,
    proof_var_name: &str,
    expected_ty: &Rc<Value<'db>>,
) -> Result<Rc<Syntax<'db>>, String> {
    // BASE CASE 1: Empty matrix (inexhaustive match)
    if matrix.rows.is_empty() {
        let loc = Location::UNKNOWN;
        ctx.diagnostics.push(Diagnostic {
            location: loc,
            message: "Inexhaustive pattern match".to_string(),
            expected_type: None,
        });
        return Ok(ctx.fresh_poisoned_meta(loc, expected_ty.clone()));
    }

    // BASE CASE 2: Pure variable row (all patterns are variables/wildcards)
    if matrix.is_pure_variable_row(0) {
        let winning_clause = &matrix.rows[0];

        // Bind the pattern variables to the scrutinees
        for (pat, _scrutinee_term) in winning_clause.patterns.iter().zip(scrutinees.iter()) {
            if let Pat::Var(name) = pat {
                // Get the type of the scrutinee
                // For now, we'll use a placeholder type
                // TODO: Track scrutinee types properly
                let scrutinee_ty = Rc::new(Value::universe(UniverseLevel::new(0)));

                ctx.push_binding(name.clone(), scrutinee_ty);
            }
        }

        // Elaborate the body
        let core_body = check(ctx, &winning_clause.body, expected_ty.clone()).await;

        // Pop the bindings
        let var_count = winning_clause
            .patterns
            .iter()
            .filter(|p| matches!(p, Pat::Var(_)))
            .count();
        for _ in 0..var_count {
            ctx.pop_binding();
        }

        // Wrap in transport
        let loc = Location::UNKNOWN;
        let proof_var = Syntax::variable_rc(
            loc,
            Index::from(ctx.lookup_var(proof_var_name).unwrap_or(0)),
        );

        return Ok(Syntax::transport_rc(
            loc,
            motive.clone(),
            proof_var,
            core_body,
        ));
    }

    // INDUCTIVE CASE: Split on the first scrutinee
    if scrutinees.is_empty() {
        return Err("No scrutinees left to split on".to_string());
    }

    let current_scrutinee = &scrutinees[0];
    let remaining_scrutinees = &scrutinees[1..];

    // Group rows by constructor
    let groups = group_by_constructor(ctx, &matrix)?;

    let mut core_branches = Vec::new();

    for (ctor_id, arity, specialized_matrix) in groups {
        // Generate fresh variables for the constructor arguments
        let mut fresh_vars = Vec::new();
        for i in 0..arity {
            let var_name = ctx.fresh_var_name("arg", i);
            let var_ty = Rc::new(Value::universe(UniverseLevel::new(0))); // TODO: Get actual type
            ctx.push_binding(var_name.clone(), var_ty);

            let var_index = Index::from(0); // Most recently bound
            fresh_vars.push(Syntax::variable_rc(Location::UNKNOWN, var_index));
        }

        // Build the new scrutinee list: [fresh_vars..., remaining_scrutinees...]
        let mut next_scrutinees = fresh_vars.clone();
        next_scrutinees.extend_from_slice(remaining_scrutinees);

        // Recurse
        let branch_body = compile_matrix(
            ctx,
            next_scrutinees,
            specialized_matrix,
            motive,
            proof_var_name,
            expected_ty,
        )
        .await?;

        // Pop the fresh variable bindings
        for _ in 0..arity {
            ctx.pop_binding();
        }

        // Create the case branch
        core_branches.push(CaseBranch::new(ctor_id, arity, branch_body));
    }

    // Build the case expression
    // The scrutinee must be a variable, so extract its index
    let scrutinee_var = match &current_scrutinee.data {
        SyntaxData::Variable(var) => var.clone(),
        _ => return Err("Scrutinee must be a variable in core case expression".to_string()),
    };

    let loc = Location::UNKNOWN;
    Ok(Syntax::case_rc(loc, scrutinee_var.index, core_branches))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::{SingleThreadedExecutor, SolverEnvironment, SolverState};
    use hwml_core::check::TCEnvironment;
    use hwml_core::val::{Environment, GlobalEnv};

    fn setup_test_context<'db, 'g>(
        db: &'db dyn salsa::Database,
        global: &'g GlobalEnv<'db>,
    ) -> ElaborationContext<'db, 'g> {
        let executor = SingleThreadedExecutor::new();
        let tc_env = TCEnvironment {
            db,
            values: Environment::new(global),
            types: Vec::new(),
        };
        let solver = SolverEnvironment::new(tc_env, executor.spawner());
        ElaborationContext::new(db, None, solver)
    }

    #[test]
    fn test_context_scope() {
        // Test basic scope operations
        let db = salsa::DatabaseImpl::default();
        let global = GlobalEnv::new();
        let mut ctx = setup_test_context(&db, &global);

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
        let global = GlobalEnv::new();
        let ctx = setup_test_context(&db, &global);

        let ty = Rc::new(Value::universe(UniverseLevel::new(0)));
        let loc = Location::UNKNOWN;
        let meta = ctx.fresh_meta(loc, ty.clone());

        // Should be a metavariable
        assert!(matches!(&meta.data, SyntaxData::Metavariable(_)));
    }

    #[test]
    fn test_fresh_poisoned_meta() {
        let db = salsa::DatabaseImpl::default();
        let global = GlobalEnv::new();
        let ctx = setup_test_context(&db, &global);

        let ty = Rc::new(Value::universe(UniverseLevel::new(0)));
        let loc = Location::UNKNOWN;
        let meta = ctx.fresh_poisoned_meta(loc, ty.clone());

        // Should be a metavariable
        assert!(
            matches!(&meta.data, SyntaxData::Metavariable(m) if ctx.solver.state.borrow().is_poisoned(m.id))
        );
    }

    #[test]
    fn test_location_tracking() {
        let db = salsa::DatabaseImpl::default();
        let global = GlobalEnv::new();
        let _ctx = setup_test_context(&db, &global);

        // Test that we can create physical locations
        let _source = SourceFile::new(&db, "test.hwml".to_string(), "fun x => x".to_string());
        let loc = Location::UNKNOWN;

        // For now, just verify we can create locations
        // TODO: Add proper location tracking tests once Location API is finalized
        assert_eq!(loc, Location::UNKNOWN);
    }

    #[test]
    fn test_diagnostic_collection() {
        let db = salsa::DatabaseImpl::default();
        let global = GlobalEnv::new();
        let mut ctx = setup_test_context(&db, &global);

        // Initially no diagnostics
        assert_eq!(ctx.diagnostics.len(), 0);

        // Report an error
        let ty = Rc::new(Value::universe(UniverseLevel::new(0)));
        let loc = Location::UNKNOWN;
        let _error_term = ctx.error(loc, "Test error".to_string(), ty.clone());

        // Should have one diagnostic
        assert_eq!(ctx.diagnostics.len(), 1);
        assert_eq!(ctx.diagnostics[0].message, "Test error");

        // Report another error
        let _error_term2 = ctx.error(loc, "Another error".to_string(), ty);

        // Should have two diagnostics
        assert_eq!(ctx.diagnostics.len(), 2);
        assert_eq!(ctx.diagnostics[1].message, "Another error");
    }

    #[test]
    fn test_synth_num_zero() {
        // Test that numeric literal 0 elaborates to Zero : Bit
        let db = salsa::DatabaseImpl::default();
        let global = GlobalEnv::new();
        let mut executor = SingleThreadedExecutor::new();

        let tc_env = TCEnvironment {
            db: &db,
            values: Environment::new(&global),
            types: Vec::new(),
        };
        let solver = SolverEnvironment::new(tc_env, executor.spawner());
        let mut ctx = ElaborationContext::new(&db, None, solver.clone());

        let num = surface::Num {
            loc: 0..1,
            value: b"0".to_vec().into_boxed_slice(),
        };

        // Spawn the async test as a task
        executor.spawn(async move {
            let (term, ty) = synth_num(&mut ctx, &num).await;

            // Check that the term is Zero
            match &term.data {
                hwml_core::syn::SyntaxData::Zero(_) => {}
                _ => panic!("Expected Zero, got {:?}", term.data),
            }

            // Check that the type is Bit
            match ty.as_ref() {
                Value::Bit(_) => {}
                _ => panic!("Expected Bit type, got {:?}", ty),
            }
            Ok(())
        });

        // Run the executor
        let tc_env2 = TCEnvironment {
            db: &db,
            values: Environment::new(&global),
            types: Vec::new(),
        };
        let solver2 = SolverEnvironment::new(tc_env2, executor.spawner());
        executor.run(&solver2).expect("test should succeed");
    }

    #[test]
    fn test_synth_num_one() {
        // Test that numeric literal 1 elaborates to One : Bit
        let db = salsa::DatabaseImpl::default();
        let global = GlobalEnv::new();
        let mut executor = SingleThreadedExecutor::new();

        let tc_env = TCEnvironment {
            db: &db,
            values: Environment::new(&global),
            types: Vec::new(),
        };
        let solver = SolverEnvironment::new(tc_env, executor.spawner());
        let mut ctx = ElaborationContext::new(&db, None, solver.clone());

        let num = surface::Num {
            loc: 0..1,
            value: b"1".to_vec().into_boxed_slice(),
        };

        // Spawn the async test as a task
        executor.spawn(async move {
            let (term, ty) = synth_num(&mut ctx, &num).await;

            // Check that the term is One
            match &term.data {
                hwml_core::syn::SyntaxData::One(_) => {}
                _ => panic!("Expected One, got {:?}", term.data),
            }

            // Check that the type is Bit
            match ty.as_ref() {
                Value::Bit(_) => {}
                _ => panic!("Expected Bit type, got {:?}", ty),
            }
            Ok(())
        });

        // Run the executor
        let tc_env2 = TCEnvironment {
            db: &db,
            values: Environment::new(&global),
            types: Vec::new(),
        };
        let solver2 = SolverEnvironment::new(tc_env2, executor.spawner());
        executor.run(&solver2).expect("test should succeed");
    }

    #[test]
    fn test_synth_num_invalid() {
        // Test that invalid numeric literals produce errors
        let db = salsa::DatabaseImpl::default();
        let global = GlobalEnv::new();
        let mut executor = SingleThreadedExecutor::new();

        let tc_env = TCEnvironment {
            db: &db,
            values: Environment::new(&global),
            types: Vec::new(),
        };
        let solver = SolverEnvironment::new(tc_env, executor.spawner());
        let mut ctx = ElaborationContext::new(&db, None, solver.clone());

        let num = surface::Num {
            loc: 0..2,
            value: b"42".to_vec().into_boxed_slice(),
        };

        // Spawn the async test as a task
        executor.spawn(async move {
            let (_term, _ty) = synth_num(&mut ctx, &num).await;

            // Should have reported an error
            assert_eq!(ctx.diagnostics.len(), 1);
            assert!(ctx.diagnostics[0]
                .message
                .contains("Invalid numeric literal"));
            Ok(())
        });

        // Run the executor
        let tc_env2 = TCEnvironment {
            db: &db,
            values: Environment::new(&global),
            types: Vec::new(),
        };
        let solver2 = SolverEnvironment::new(tc_env2, executor.spawner());
        executor.run(&solver2).expect("test should succeed");
    }

    #[test]
    fn test_parse_pattern_variable() {
        // Test parsing a variable pattern
        let db = salsa::DatabaseImpl::default();
        let global = GlobalEnv::new();
        let ctx = setup_test_context(&db, &global);

        let var_expr = surface::Expression::Id(surface::Id {
            loc: 0..1,
            value: b"x".to_vec().into_boxed_slice(),
        });

        let pattern = ctx.parse_pattern(&var_expr).expect("should parse");
        match pattern {
            Pat::Var(name) => assert_eq!(name, "x"),
            _ => panic!("Expected variable pattern, got {:?}", pattern),
        }
    }

    #[test]
    fn test_parse_pattern_wildcard() {
        // Test parsing a wildcard pattern
        let db = salsa::DatabaseImpl::default();
        let global = GlobalEnv::new();
        let ctx = setup_test_context(&db, &global);

        let wildcard_expr = surface::Expression::Underscore(surface::Underscore { loc: 0..1 });

        let pattern = ctx.parse_pattern(&wildcard_expr).expect("should parse");
        match pattern {
            Pat::Wildcard => {}
            _ => panic!("Expected wildcard pattern, got {:?}", pattern),
        }
    }

    #[test]
    fn test_parse_pattern_constructor() {
        // Test parsing a constructor pattern with no arguments
        let db = salsa::DatabaseImpl::default();
        let global = GlobalEnv::new();
        let ctx = setup_test_context(&db, &global);

        let ctor_expr = surface::Expression::Id(surface::Id {
            loc: 0..5,
            value: b"@True".to_vec().into_boxed_slice(),
        });

        let pattern = ctx.parse_pattern(&ctor_expr).expect("should parse");
        match pattern {
            Pat::Constructor(ctor_id, args) => {
                assert_eq!(ctor_id.name(&db), "True");
                assert_eq!(args.len(), 0);
            }
            _ => panic!("Expected constructor pattern, got {:?}", pattern),
        }
    }

    #[test]
    fn test_parse_pattern_constructor_with_args() {
        // Test parsing a constructor pattern with arguments: @Some x
        let db = salsa::DatabaseImpl::default();
        let global = GlobalEnv::new();
        let ctx = setup_test_context(&db, &global);

        let ctor_expr = surface::Expression::Id(surface::Id {
            loc: 0..5,
            value: b"@Some".to_vec().into_boxed_slice(),
        });

        let var_expr = surface::Expression::Id(surface::Id {
            loc: 6..7,
            value: b"x".to_vec().into_boxed_slice(),
        });

        let app_expr = surface::Expression::App(surface::App {
            loc: 0..7,
            elements: vec![Box::new(ctor_expr), Box::new(var_expr)],
        });

        let pattern = ctx.parse_pattern(&app_expr).expect("should parse");
        match pattern {
            Pat::Constructor(ctor_id, args) => {
                assert_eq!(ctor_id.name(&db), "Some");
                assert_eq!(args.len(), 1);
                match &args[0] {
                    Pat::Var(name) => assert_eq!(name, "x"),
                    _ => panic!("Expected variable in constructor args"),
                }
            }
            _ => panic!("Expected constructor pattern, got {:?}", pattern),
        }
    }

    #[test]
    fn test_parse_pattern_nested() {
        // Test parsing nested constructor patterns: @Some (@Some x)
        let db = salsa::DatabaseImpl::default();
        let global = GlobalEnv::new();
        let ctx = setup_test_context(&db, &global);

        let outer_ctor = surface::Expression::Id(surface::Id {
            loc: 0..5,
            value: b"@Some".to_vec().into_boxed_slice(),
        });

        let inner_ctor = surface::Expression::Id(surface::Id {
            loc: 7..12,
            value: b"@Some".to_vec().into_boxed_slice(),
        });

        let var_expr = surface::Expression::Id(surface::Id {
            loc: 13..14,
            value: b"x".to_vec().into_boxed_slice(),
        });

        let inner_app = surface::Expression::App(surface::App {
            loc: 7..14,
            elements: vec![Box::new(inner_ctor), Box::new(var_expr)],
        });

        let outer_app = surface::Expression::App(surface::App {
            loc: 0..15,
            elements: vec![Box::new(outer_ctor), Box::new(inner_app)],
        });

        let pattern = ctx.parse_pattern(&outer_app).expect("should parse");
        match pattern {
            Pat::Constructor(outer_id, outer_args) => {
                assert_eq!(outer_id.name(&db), "Some");
                assert_eq!(outer_args.len(), 1);
                match &outer_args[0] {
                    Pat::Constructor(inner_id, inner_args) => {
                        assert_eq!(inner_id.name(&db), "Some");
                        assert_eq!(inner_args.len(), 1);
                        match &inner_args[0] {
                            Pat::Var(name) => assert_eq!(name, "x"),
                            _ => panic!("Expected variable in nested pattern"),
                        }
                    }
                    _ => panic!("Expected nested constructor pattern"),
                }
            }
            _ => panic!("Expected constructor pattern, got {:?}", pattern),
        }
    }

    // ========================================================================
    // Snapshot Tests (FileCheck-style)
    // ========================================================================
    //
    // These tests use insta for snapshot testing, providing a workflow similar
    // to LLVM's FileCheck/lit tests. The snapshots capture the input surface
    // syntax and the output core syntax + type.
    //
    // To review snapshots: cargo insta review
    // To accept all: cargo insta accept

    #[test]
    fn snapshot_synth_num_zero() {
        use crate::test_utils::*;
        let db = salsa::DatabaseImpl::default();
        let global = GlobalEnv::new();
        let mut ctx = make_test_context(&db, &global);

        let input = "0";
        let expr = parse_surface(input);
        let (term, ty) = elaborate_synth(&mut ctx, &expr);

        insta::assert_snapshot!(format_elab_snapshot(&db, input, &term, &ty), @r###"
        INPUT:
        0

        TERM:
        0

        TYPE:
        Bit
        "###);
    }

    #[test]
    fn snapshot_synth_num_one() {
        use crate::test_utils::*;
        let db = salsa::DatabaseImpl::default();
        let global = GlobalEnv::new();
        let mut ctx = make_test_context(&db, &global);

        let input = "1";
        let expr = parse_surface(input);
        let (term, ty) = elaborate_synth(&mut ctx, &expr);

        insta::assert_snapshot!(format_elab_snapshot(&db, input, &term, &ty), @r###"
        INPUT:
        1

        TERM:
        1

        TYPE:
        Bit
        "###);
    }

    #[test]
    fn snapshot_synth_universe() {
        use crate::test_utils::*;
        let db = salsa::DatabaseImpl::default();
        let global = GlobalEnv::new();
        let mut ctx = make_test_context(&db, &global);

        let input = "U0";
        let expr = parse_surface(input);
        let (term, ty) = elaborate_synth(&mut ctx, &expr);

        insta::assert_snapshot!(format_elab_snapshot(&db, input, &term, &ty), @r###"
        INPUT:
        U0

        TERM:
        ?[0]

        TYPE:
        𝒰0
        "###);
    }

    #[test]
    fn snapshot_synth_hardware_universe() {
        use crate::test_utils::*;
        let db = salsa::DatabaseImpl::default();
        let global = GlobalEnv::new();
        let mut ctx = make_test_context(&db, &global);

        let input = "$HW";
        let expr = parse_surface(input);
        let (term, ty) = elaborate_synth(&mut ctx, &expr);

        insta::assert_snapshot!(format_elab_snapshot(&db, input, &term, &ty), @r###"
        INPUT:
        $HW

        TERM:
        ?[0]

        TYPE:
        𝒰0
        "###);
    }

    #[test]
    fn snapshot_check_arrow() {
        use crate::test_utils::*;
        let db = salsa::DatabaseImpl::default();
        let global = GlobalEnv::new();
        let mut ctx = make_test_context(&db, &global);

        let input = "$Bit -> $Bit";
        let expr = parse_surface(input);
        let expected_ty = Rc::new(Value::universe(UniverseLevel::new(0)));
        let term = elaborate_check(&mut ctx, &expr, expected_ty.clone());

        let expected_ty_str = "U0";
        insta::assert_snapshot!(format_check_snapshot(&db, input, expected_ty_str, &term), @r###"
        INPUT:
        $Bit -> $Bit

        EXPECTED TYPE:
        U0

        TERM:
        ∀ (%0 : ?[0]) → ?[1]
        "###);
    }

    #[test]
    fn snapshot_check_fat_arrow() {
        use crate::test_utils::*;
        let db = salsa::DatabaseImpl::default();
        let global = GlobalEnv::new();
        let mut ctx = make_test_context(&db, &global);

        let input = "$Bit => $Bit";
        let expr = parse_surface(input);
        let expected_ty = Rc::new(Value::hardware_universe());
        let term = elaborate_check(&mut ctx, &expr, expected_ty.clone());

        let expected_ty_str = "$HW";
        insta::assert_snapshot!(format_check_snapshot(&db, input, expected_ty_str, &term), @r###"
        INPUT:
        $Bit => $Bit

        EXPECTED TYPE:
        $HW

        TERM:
        ?[1] → ?[3]
        "###);
    }

    // TODO: Add more snapshot tests:
    // - snapshot_implicit_lift_basic (test Lift insertion)
    // - snapshot_implicit_slift (test SLift insertion)
    // - snapshot_implicit_mlift (test MLift insertion)
    // - snapshot_check_match_bool (full pattern matching)
    // - snapshot_check_match_option (parametric pattern matching)
    // - snapshot_synth_variable
    // - snapshot_check_lambda
    // - snapshot_synth_application
    // - snapshot_check_pi
}
