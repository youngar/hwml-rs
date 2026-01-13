use futures::join;
use hwml_core::common::{Level, MetaVariableId};
use hwml_core::equal::is_type_convertible;
use hwml_core::eval::{self, run_application, run_closure, run_spine};
use hwml_core::val::{Eliminator, Value};
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

// Import the SolverEnvironment from async_solver
use crate::async_solver::SolverEnvironment;

/// Unification error type for the async unifier.
#[derive(Debug, Clone)]
pub enum UnificationError<'db> {
    /// Evaluation error during unification
    Eval(eval::Error),
    /// Type mismatch between two values
    Mismatch(Rc<Value<'db>>, Rc<Value<'db>>),
    /// Eliminator mismatch
    MismatchEliminator(Eliminator<'db>, Eliminator<'db>),
    /// Spine mismatch (general case)
    MismatchSpine(hwml_core::val::Spine<'db>, hwml_core::val::Spine<'db>),
    /// Type constructor mismatch
    TypeConstructorMismatch(String, String),
    /// Data constructor mismatch
    DataConstructorMismatch(String, String),
    /// Argument count mismatch
    ArgumentCountMismatch(usize, usize),
    /// Rigid head mismatch
    RigidHeadMismatch(String, String),
    /// Spine length mismatch
    SpineLengthMismatch(usize, usize),
    /// Non-linear pattern in spine (same variable appears twice)
    NonLinearApplication(Eliminator<'db>),
    /// Blocked solution (spine contains non-variable term)
    BlockedSolution(Eliminator<'db>),
    /// Occurs check failure (metavariable occurs in its own solution)
    OccursCheck(MetaVariableId),
    /// Scoping error (solution references out-of-scope variables)
    ScopingError(Rc<Value<'db>>),
    /// Quotation error
    Quote(String),
}

impl<'db> fmt::Display for UnificationError<'db> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnificationError::Eval(e) => write!(f, "Evaluation error: {:?}", e),
            UnificationError::Mismatch(lhs, rhs) => {
                write!(f, "Cannot unify {:?} with {:?}", lhs, rhs)
            }
            UnificationError::MismatchEliminator(lhs, rhs) => {
                write!(f, "Eliminator mismatch: {:?} vs {:?}", lhs, rhs)
            }
            UnificationError::MismatchSpine(s1, s2) => {
                write!(f, "Spine mismatch: length {} vs {}", s1.len(), s2.len())
            }
            UnificationError::TypeConstructorMismatch(tc1, tc2) => {
                write!(f, "Type constructor mismatch: {} vs {}", tc1, tc2)
            }
            UnificationError::DataConstructorMismatch(dc1, dc2) => {
                write!(f, "Data constructor mismatch: {} vs {}", dc1, dc2)
            }
            UnificationError::ArgumentCountMismatch(count1, count2) => {
                write!(f, "Argument count mismatch: {} vs {}", count1, count2)
            }
            UnificationError::RigidHeadMismatch(head1, head2) => {
                write!(f, "Rigid head mismatch: {} vs {}", head1, head2)
            }
            UnificationError::SpineLengthMismatch(len1, len2) => {
                write!(f, "Spine length mismatch: {} vs {}", len1, len2)
            }
            UnificationError::NonLinearApplication(elim) => {
                write!(
                    f,
                    "Non-linear pattern: variable appears multiple times in spine: {:?}",
                    elim
                )
            }
            UnificationError::BlockedSolution(elim) => {
                write!(
                    f,
                    "Blocked solution: spine contains non-variable term: {:?}",
                    elim
                )
            }
            UnificationError::OccursCheck(meta) => {
                write!(
                    f,
                    "Occurs check failed: metavariable {} occurs in its own solution",
                    meta
                )
            }
            UnificationError::ScopingError(value) => {
                write!(
                    f,
                    "Scoping error: solution references out-of-scope variables: {:?}",
                    value
                )
            }
            UnificationError::Quote(msg) => {
                write!(f, "Quotation error: {}", msg)
            }
        }
    }
}

impl<'db> From<eval::Error> for UnificationError<'db> {
    fn from(e: eval::Error) -> Self {
        UnificationError::Eval(e)
    }
}

/// Force the substitution of a metavariable with its solution, if available.
///
/// This implements the "propagate metas" functionality: when a metavariable has been
/// solved, we substitute its solution into the value. Forcing only computes until
/// it hits the next head constructor which cannot be further unblocked - it does
/// not recurse into values.
///
/// This is essential for the async solver because metavariables may be solved
/// concurrently by other tasks, and we need to pick up those solutions.
fn force<'gb, 'g>(
    ctx: &SolverEnvironment<'gb, 'g>,
    mut value: Rc<Value<'db>>,
) -> Result<Rc<Value<'db>>, UnificationError<'db>> {
    while let Value::Flex(flex) = &*value {
        match ctx.get_solution(flex.head.id) {
            Some(solution) => {
                println!("[Force] Substituting meta {} with solution", flex.head.id);
                // First, apply the solution to the local substitution.
                // With contextual metavariables, the solution is a value in the metavariable's
                // context. We apply the local environment to instantiate it in the current context.
                let mut result = solution.clone();
                for arg in flex.head.local.iter() {
                    result = run_application(ctx.tc_env.values.global, &result, arg.clone())?;
                }
                // Then apply the spine.
                value = run_spine(ctx.tc_env.values.global, result, &flex.spine)?;
            }
            None => break,
        }
    }
    Ok(value)
}

/// A partial renaming from context gamma (old context) to delta (new context).
///
/// This is used in pattern unification to track how variables in the solution
/// should be renamed to match the pattern spine.
#[derive(Clone, Debug)]
struct Renaming {
    /// Size of gamma (domain - the original context).
    dom_len: usize,
    /// Size of delta (codomain - the new context).
    cod_len: usize,
    /// Mapping from gamma vars to delta vars.
    map: HashMap<Level, Level>,
}

impl Renaming {
    /// Create a new empty renaming.
    fn new() -> Renaming {
        Renaming {
            dom_len: 0,
            cod_len: 0,
            map: HashMap::new(),
        }
    }

    /// Insert a mapping from a variable in gamma to the next variable in delta.
    fn insert(&mut self, from: Level) {
        self.map.insert(from, Level::new(self.cod_len));
        self.cod_len += 1;
    }

    /// Lift the renaming under a binder.
    /// This extends both contexts with a fresh variable.
    fn lift(&self) -> Renaming {
        let mut new_map = self.map.clone();
        new_map.insert(Level::new(self.dom_len), Level::new(self.cod_len));
        Renaming {
            dom_len: self.dom_len + 1,
            cod_len: self.cod_len + 1,
            map: new_map,
        }
    }

    /// Rename a level from gamma to delta.
    /// Returns None if the level is not in the renaming.
    fn rename(&self, level: Level) -> Option<Level> {
        self.map.get(&level).cloned()
    }
}

pub fn unification_of<'db, 'g>(ctx: SolverEnvironment<')
/// Async unification function.
/// Instead of returning a Blocker, this function uses .await to suspend when blocked.
/// This version works with Values (normalized terms) instead of Syntax.
pub async fn unify<'g: 'db, 'db>(
    ctx: SolverEnvironment<'gb, 'g>,
    lhs: Rc<Value<'db>>,
    rhs: Rc<Value<'db>>,
) -> Result<(), UnificationError<'db>> {
    println!("[Unify] Unifying {:?} == {:?}", lhs, rhs);

    // Force both sides to substitute any solved metavariables.
    let lhs = force(&ctx, lhs)?;
    let rhs = force(&ctx, rhs)?;

    // TODO: Check type convertibility of terms first.

    // Match on the structure of both values
    match (&*lhs, &*rhs) {
        // Handle Constant unification - constants must be identical
        (Value::Constant(c1), Value::Constant(c2)) => {
            if c1 == c2 {
                println!("[Unify] Constants are equal");
                Ok(())
            } else {
                Err(UnificationError::Mismatch(lhs, rhs))
            }
        }

        // Handle Universe unification - universe levels must match
        (Value::Universe(u1), Value::Universe(u2)) => {
            if u1.level == u2.level {
                println!("[Unify] Universes at same level");
                Ok(())
            } else {
                Err(UnificationError::Mismatch(lhs, rhs))
            }
        }

        // Handle Pi injectivity: Pi x y == Pi a b => x == a && y == b
        (Value::Pi(pi1), Value::Pi(pi2)) => {
            println!("[Unify] Pi injectivity");

            // Unify the domains.
            let dom_fut = Box::pin(unify(ctx.clone(), pi1.source.clone(), pi2.source.clone()));

            // Create a fresh metavariable for the anti-unifier's domain type. This will be solved once the domain unification completes.
            let dom_meta = ctx.fresh_meta();
            println!(
                "[Unify] Created domain anti-unifier metavariable {}",
                dom_meta
            );
            let dom_ty = Rc::new(Value::metavariable(
                dom_meta,
                ctx.tc_env.values.local.clone(),
            ));
            let dom_val = Rc::new(Value::variable(
                dom_ty.clone(),
                Level::new(ctx.tc_env.values.depth()),
            ));

            // Instantiate both closures with the fresh variable to get codomain values.
            let cod1 = run_closure(ctx.tc_env.values.global, &pi1.target, [dom_val.clone()])?;
            let cod2 = run_closure(ctx.tc_env.values.global, &pi2.target, [dom_val])?;

            // Unify the codomains concurrently with the domain
            println!("[Unify] Unifying Pi codomains: {:?} == {:?}", cod1, cod2);
            let cod_fut = Box::pin(unify(ctx.clone(), cod1, cod2));

            // Wait for both domain and codomain unification to complete concurrently.
            let (dom_result, cod_result): (
                Result<(), UnificationError<'db>>,
                Result<(), UnificationError<'db>>,
            ) = join!(
                async {
                    // If domain unification succeeded, solve the domain metavariable.
                    // The anti-unifier for the domain is just the domain itself (since they unified).
                    dom_fut.await?;
                    ctx.define_meta(dom_meta, pi1.source.clone());
                    Ok(())
                },
                cod_fut
            );

            // Propagate codomain errors first
            dom_result?;
            cod_result
        }

        // Handle Lambda injectivity
        // Similar pattern to Pi: instantiate closures with fresh variable and unify bodies
        (Value::Lambda(lam1), Value::Lambda(lam2)) => {
            println!("[Unify] Lambda injectivity");

            // Create a fresh variable to instantiate both lambda bodies
            // We use Universe(0) as a placeholder type since we don't have the domain type here
            let current_depth = ctx.tc_env.values.depth();
            let placeholder_ty = Rc::new(Value::universe(hwml_core::common::UniverseLevel::new(0)));
            let fresh_var = Rc::new(Value::variable(placeholder_ty, Level::new(current_depth)));

            // Instantiate both closures with the fresh variable
            let body1 = run_closure(ctx.tc_env.values.global, &lam1.body, [fresh_var.clone()])?;
            let body2 = run_closure(ctx.tc_env.values.global, &lam2.body, [fresh_var])?;

            // Unify the bodies
            println!("[Unify] Unifying Lambda bodies: {:?} == {:?}", body1, body2);
            Box::pin(unify(ctx, body1, body2)).await
        }

        // Eta-expansion: Lambda on left, non-lambda on right
        // Unify λx. body with t by unifying body with (t x)
        (Value::Lambda(lam), _) => {
            println!("[Unify] Eta-expansion: Lambda on left");

            // Create a fresh variable to instantiate the lambda
            let current_depth = ctx.tc_env.values.depth();
            let placeholder_ty = Rc::new(Value::universe(hwml_core::common::UniverseLevel::new(0)));
            let fresh_var = Rc::new(Value::variable(placeholder_ty, Level::new(current_depth)));

            // Instantiate the lambda body with the fresh variable
            let body = run_closure(ctx.tc_env.values.global, &lam.body, [fresh_var.clone()])?;

            // Apply the right side to the fresh variable
            let rhs_applied = run_application(ctx.tc_env.values.global, &rhs, fresh_var)?;

            // Unify the lambda body with the applied right side
            println!("[Unify] Unifying lambda body with applied term");
            Box::pin(unify(ctx, body, rhs_applied)).await
        }

        // Eta-expansion: non-lambda on left, Lambda on right
        // Unify t with λx. body by unifying (t x) with body
        (_, Value::Lambda(lam)) => {
            println!("[Unify] Eta-expansion: Lambda on right");

            // Create a fresh variable to instantiate the lambda
            let current_depth = ctx.tc_env.values.depth();
            let placeholder_ty = Rc::new(Value::universe(hwml_core::common::UniverseLevel::new(0)));
            let fresh_var = Rc::new(Value::variable(placeholder_ty, Level::new(current_depth)));

            // Apply the left side to the fresh variable
            let lhs_applied = run_application(ctx.tc_env.values.global, &lhs, fresh_var.clone())?;

            // Instantiate the lambda body with the fresh variable
            let body = run_closure(ctx.tc_env.values.global, &lam.body, [fresh_var])?;

            // Unify the applied left side with the lambda body
            println!("[Unify] Unifying applied term with lambda body");
            Box::pin(unify(ctx, lhs_applied, body)).await
        }

        // Handle TypeConstructor injectivity
        (Value::TypeConstructor(tc1), Value::TypeConstructor(tc2)) => {
            if tc1.constructor != tc2.constructor {
                return Err(UnificationError::TypeConstructorMismatch(
                    format!("{:?}", tc1.constructor),
                    format!("{:?}", tc2.constructor),
                ));
            }
            if tc1.arguments.len() != tc2.arguments.len() {
                return Err(UnificationError::ArgumentCountMismatch(
                    tc1.arguments.len(),
                    tc2.arguments.len(),
                ));
            }
            println!("[Unify] Type constructor injectivity");
            for (arg1, arg2) in tc1.arguments.iter().zip(tc2.arguments.iter()) {
                Box::pin(unify(ctx.clone(), arg1.clone(), arg2.clone())).await?;
            }
            Ok(())
        }

        // Handle DataConstructor injectivity
        (Value::DataConstructor(dc1), Value::DataConstructor(dc2)) => {
            if dc1.constructor != dc2.constructor {
                return Err(UnificationError::DataConstructorMismatch(
                    format!("{:?}", dc1.constructor),
                    format!("{:?}", dc2.constructor),
                ));
            }
            if dc1.arguments.len() != dc2.arguments.len() {
                return Err(UnificationError::ArgumentCountMismatch(
                    dc1.arguments.len(),
                    dc2.arguments.len(),
                ));
            }
            println!("[Unify] Data constructor injectivity");
            for (arg1, arg2) in dc1.arguments.iter().zip(dc2.arguments.iter()) {
                Box::pin(unify(ctx.clone(), arg1.clone(), arg2.clone())).await?;
            }
            Ok(())
        }

        // Handle Flex-Flex unification (both sides are metavariables)
        (Value::Flex(f1), Value::Flex(f2)) => {
            println!("[Unify] Flex-Flex: {} vs {}", f1.head.id, f2.head.id);

            // Check if they're the same metavariable
            if f1.head.id == f2.head.id {
                println!("[Unify] Same metavariable, unifying spines");
                // Same metavariable: unify the spines
                Box::pin(unify_spine(ctx, &f1.spine, &f2.spine)).await
            } else {
                println!("[Unify] Different metavariables, solving first with second");
                // Different metavariables: solve the first one with the second using pattern unification
                let depth = ctx.tc_env.values.depth();
                Box::pin(solve(ctx, depth, &f1.head, &f1.spine, rhs, f1.ty.clone())).await
            }
        }

        // Handle Flex (metavariable) on the left side
        (Value::Flex(flex), _) => {
            println!("[Unify] Left side is metavariable {}", flex.head.id);

            // Check if the meta is already solved
            let maybe_resolved = ctx.get_solution(flex.head.id);

            if let Some(resolved) = maybe_resolved {
                // Meta is already solved, unify the resolved value with the right side
                println!(
                    "[Unify] Meta {} already solved, unifying resolved value",
                    flex.head.id
                );
                return Box::pin(unify(ctx, resolved, rhs)).await;
            } else {
                // Meta is not solved, solve it with the right side using pattern unification
                println!("[Unify] Solving meta {} with right side", flex.head.id);
                let depth = ctx.tc_env.values.depth();
                return Box::pin(solve(
                    ctx,
                    depth,
                    &flex.head,
                    &flex.spine,
                    rhs,
                    flex.ty.clone(),
                ))
                .await;
            }
        }

        // Handle Flex (metavariable) on the right side
        (_, Value::Flex(flex)) => {
            println!("[Unify] Right side is metavariable {}", flex.head.id);

            // Check if the meta is already solved
            let maybe_resolved = ctx.get_solution(flex.head.id);

            if let Some(resolved) = maybe_resolved {
                // Meta is already solved, unify the left side with the resolved value
                println!(
                    "[Unify] Meta {} already solved, unifying with resolved value",
                    flex.head.id
                );
                return Box::pin(unify(ctx, lhs, resolved)).await;
            } else {
                // Meta is not solved, solve it with the left side using pattern unification
                println!("[Unify] Solving meta {} with left side", flex.head.id);
                let depth = ctx.tc_env.values.depth();
                return Box::pin(solve(
                    ctx,
                    depth,
                    &flex.head,
                    &flex.spine,
                    lhs,
                    flex.ty.clone(),
                ))
                .await;
            }
        }

        // Handle Rigid (variable) neutrals - they must have the same head and spine
        (Value::Rigid(r1), Value::Rigid(r2)) => {
            if r1.head != r2.head {
                return Err(UnificationError::RigidHeadMismatch(
                    format!("{:?}", r1.head),
                    format!("{:?}", r2.head),
                ));
            }
            println!("[Unify] Rigid neutrals with same head");
            // Unify the spines using the helper function
            Box::pin(unify_spine(ctx, &r1.spine, &r2.spine)).await
        }

        // If we get here, we couldn't unify
        _ => Err(UnificationError::Mismatch(lhs, rhs)),
    }
}

/// Unify two eliminators (applications, projections, etc.)
async fn unify_eliminator<'g: 'db, 'db>(
    ctx: SolverEnvironment<'gb, 'g>,
    lhs: &Eliminator<'db>,
    rhs: &Eliminator<'db>,
) -> Result<(), UnificationError<'db>> {
    match (lhs, rhs) {
        (Eliminator::Application(app1), Eliminator::Application(app2)) => {
            println!("[Unify] Application eliminator");
            Box::pin(unify(
                ctx,
                app1.argument.value.clone(),
                app2.argument.value.clone(),
            ))
            .await
        }
        (Eliminator::Case(_), Eliminator::Case(_)) => {
            // TODO: Implement case unification
            println!("[Unify] Warning: Case unification not implemented yet");
            Ok(())
        }
        _ => Err(UnificationError::MismatchEliminator(
            lhs.clone(),
            rhs.clone(),
        )),
    }
}

/// Unify two spines (sequences of eliminators).
/// This is a helper function used in Rigid-Rigid and Flex-Flex unification.
async fn unify_spine<'g: 'db, 'db>(
    ctx: SolverEnvironment<'gb, 'g>,
    spine1: &hwml_core::val::Spine<'db>,
    spine2: &hwml_core::val::Spine<'db>,
) -> Result<(), UnificationError<'db>> {
    if spine1.len() != spine2.len() {
        return Err(UnificationError::SpineLengthMismatch(
            spine1.len(),
            spine2.len(),
        ));
    }

    println!("[Unify] Unifying spines of length {}", spine1.len());
    for (e1, e2) in spine1.iter().zip(spine2.iter()) {
        Box::pin(unify_eliminator(ctx.clone(), e1, e2)).await?;
    }
    Ok(())
}

// ============================================================================
// PATTERN UNIFICATION
// ============================================================================

/// Invert a spine to check if it's a valid pattern and build a renaming.
///
/// A spine is a valid pattern if it consists only of distinct variables.
/// Returns a renaming that maps the variables in the spine to a fresh context.
fn invert<'gb, 'g>(
    ctx: &SolverEnvironment<'gb, 'g>,
    depth: usize,
    spine: &hwml_core::val::Spine<'db>,
) -> Result<Renaming, UnificationError<'db>> {
    let mut renaming = Renaming::new();
    renaming.cod_len = depth;

    for eliminator in spine.iter() {
        match eliminator {
            hwml_core::val::Eliminator::Application(a) => {
                // Force the argument to see if it's a variable
                let head = force(ctx, a.argument.value.clone())?;
                match &*head {
                    Value::Rigid(r) if r.spine.is_empty() => {
                        // Check for non-linearity (variable appears twice)
                        if renaming.map.contains_key(&r.head.level) {
                            return Err(UnificationError::NonLinearApplication(eliminator.clone()));
                        }
                        renaming.insert(r.head.level);
                    }
                    // Not a variable - blocked solution
                    _ => return Err(UnificationError::BlockedSolution(eliminator.clone())),
                }
            }
            // Case eliminators not supported yet
            _ => return Err(UnificationError::BlockedSolution(eliminator.clone())),
        }
    }

    Ok(renaming)
}

/// Rename an eliminator according to a renaming.
fn rename_eliminator<'gb, 'g>(
    ctx: &SolverEnvironment<'gb, 'g>,
    meta: &hwml_core::val::MetaVariable<'db>,
    renaming: &mut Renaming,
    eliminator: &hwml_core::val::Eliminator<'db>,
) -> Result<hwml_core::val::Eliminator<'db>, UnificationError<'db>> {
    match eliminator {
        hwml_core::val::Eliminator::Application(a) => {
            // Rename the argument type and value
            let arg_ty = rename(ctx, meta, renaming, &a.argument.ty)?;
            let arg_value = rename(ctx, meta, renaming, &a.argument.value)?;
            let arg_normal = hwml_core::val::Normal::new(arg_ty, arg_value);
            Ok(hwml_core::val::Eliminator::application(arg_normal))
        }
        hwml_core::val::Eliminator::Case(_) => {
            // Case renaming not yet supported
            Err(UnificationError::BlockedSolution(eliminator.clone()))
        }
    }
}

/// Rename a spine according to a renaming.
fn rename_spine<'gb, 'g>(
    ctx: &SolverEnvironment<'gb, 'g>,
    meta: &hwml_core::val::MetaVariable<'db>,
    renaming: &mut Renaming,
    spine: &hwml_core::val::Spine<'db>,
) -> Result<hwml_core::val::Spine<'db>, UnificationError<'db>> {
    let mut new_spine = vec![];
    for eliminator in spine.iter() {
        new_spine.push(rename_eliminator(ctx, meta, renaming, eliminator)?);
    }
    Ok(hwml_core::val::Spine::new(new_spine))
}

/// Rename a value according to a renaming.
///
/// This performs occurs check and scope check while renaming.
fn rename<'gb, 'g>(
    ctx: &SolverEnvironment<'gb, 'g>,
    meta: &hwml_core::val::MetaVariable<'db>,
    renaming: &mut Renaming,
    value: &Rc<Value<'db>>,
) -> Result<Rc<Value<'db>>, UnificationError<'db>> {
    let value = force(ctx, value.clone())?;

    match &*value {
        Value::Flex(flex) => {
            // Occurs check: if the metavariable we're solving appears in the solution,
            // we would create an infinite type
            if flex.head.id == meta.id {
                return Err(UnificationError::OccursCheck(meta.id));
            }
            // Rename the spine
            let spine = rename_spine(ctx, meta, renaming, &flex.spine)?;
            Ok(Rc::new(Value::flex(
                flex.head.clone(),
                spine,
                flex.ty.clone(),
            )))
        }
        Value::Rigid(r) => {
            // Scope check: remap the variable level
            let Some(variable) = renaming.rename(r.head.level) else {
                return Err(UnificationError::ScopingError(value.clone()));
            };
            let spine = rename_spine(ctx, meta, renaming, &r.spine)?;
            Ok(Rc::new(Value::rigid(
                hwml_core::val::Variable::new(variable),
                spine,
                r.ty.clone(),
            )))
        }
        Value::Lambda(lam) => {
            // Rename all free variables in the lambda closure
            let mut new_env = hwml_core::val::LocalEnv::new();
            for val in lam.body.local.iter() {
                new_env.push(rename(ctx, meta, renaming, val)?);
            }
            let clos = hwml_core::val::Closure::new(new_env, lam.body.term.clone());
            Ok(Rc::new(Value::lambda(clos)))
        }
        Value::Pi(pi) => {
            // Rename the source type
            let source = rename(ctx, meta, renaming, &pi.source)?;
            // Lift the renaming under the binder
            let mut lifted_renaming = renaming.lift();
            // Rename all free variables in the pi closure
            let mut new_env = hwml_core::val::LocalEnv::new();
            for val in pi.target.local.iter() {
                new_env.push(rename(ctx, meta, &mut lifted_renaming, val)?);
            }
            let clos = hwml_core::val::Closure::new(new_env, pi.target.term.clone());
            Ok(Rc::new(Value::pi(source, clos)))
        }
        Value::TypeConstructor(tc) => {
            // Rename all arguments
            let mut new_args = Vec::new();
            for arg in tc.arguments.iter() {
                new_args.push(rename(ctx, meta, renaming, arg)?);
            }
            Ok(Rc::new(Value::type_constructor(tc.constructor, new_args)))
        }
        Value::DataConstructor(dc) => {
            // Rename all arguments
            let mut new_args = Vec::new();
            for arg in dc.arguments.iter() {
                new_args.push(rename(ctx, meta, renaming, arg)?);
            }
            Ok(Rc::new(Value::data_constructor(dc.constructor, new_args)))
        }
        // Constants and universes don't contain variables, so no renaming needed
        _ => Ok(value.clone()),
    }
}

/// Solve a metavariable with pattern unification.
///
/// This is the main entry point for pattern unification. It:
/// 1. Inverts the spine to check if it's a valid pattern
/// 2. Renames the solution to match the pattern
/// 3. Stores the solution directly (no lambda wrapping needed with contextual metavariables)
///
/// With contextual metavariables, we don't need to wrap solutions in lambdas.
/// The metavariable carries its context via the `local` field, and when the solution
/// is looked up via `force()`, the local environment is applied to instantiate it.
async fn solve<'g: 'db, 'db>(
    ctx: SolverEnvironment<'gb, 'g>,
    depth: usize,
    meta_variable: &hwml_core::val::MetaVariable<'db>,
    spine: &hwml_core::val::Spine<'db>,
    solution: Rc<Value<'db>>,
    _ty: Rc<Value<'db>>,
) -> Result<(), UnificationError<'db>> {
    println!(
        "[Solve] Solving metavariable {} with pattern unification",
        meta_variable.id
    );

    // Create an initial renaming from the spine
    let mut renaming = invert(&ctx, depth, spine)?;

    // Rename the solution
    let rhs = rename(&ctx, meta_variable, &mut renaming, &solution)?;

    // With contextual metavariables, we don't need to wrap the solution in lambdas!
    // The solution is already in the right context (the metavariable's local environment).
    // When force() looks up this solution, it will apply the local environment to
    // instantiate it in the current context.
    //
    // The spine length tells us how many arguments the metavariable was applied to,
    // but we don't need to abstract over them because the solution is already
    // expressed in terms of the metavariable's context.

    println!(
        "[Solve] Solved metavariable {} := {:?}",
        meta_variable.id, rhs
    );

    // Store the renamed solution directly - no lambda wrapping needed!
    ctx.define_meta(meta_variable.id, rhs);

    println!(
        "[Solve] Successfully stored solution for metavariable {}",
        meta_variable.id
    );

    Ok(())
}
