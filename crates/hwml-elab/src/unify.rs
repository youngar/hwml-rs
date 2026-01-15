use futures::future::join_all;
use futures::join;
use futures::TryFutureExt;
use hwml_core::common::{Level, MetaVariableId};
use hwml_core::equal::is_type_convertible;
use hwml_core::eval::{self, run_application, run_closure, run_spine};
use hwml_core::val::Environment;
use hwml_core::val::LocalEnv;
use hwml_core::val::{Eliminator, Value};
use itertools::izip;
use std::collections::HashMap;
use std::fmt;
use std::future::Future;
use std::rc::Rc;

use crate::engine::SolverEnvironment;
use crate::*;

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
    /// Inversion error
    InversionError(renaming::InversionError<'db>),
    /// Generic error
    Generic(String),
}

impl<'db> fmt::Display for UnificationError<'db> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnificationError::Generic(msg) => {
                write!(f, "error: {}", msg)
            }
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
impl<'db> From<renaming::InversionError<'db>> for UnificationError<'db> {
    fn from(e: renaming::InversionError<'db>) -> Self {
        UnificationError::InversionError(e)
    }
}

async fn whnf<'db, 'g>(
    ctx: &SolverEnvironment<'db, 'g>,
    mut value: Rc<Value<'db>>,
) -> Result<Rc<Value<'db>>, UnificationError<'db>> {
    while let Value::Flex(flex) = &*value {
        let solution =
            WaitForResolved::new(ctx.clone(), flex.head.id, BlockReason::generic("whnf")).await;
        println!("[WHNF] Substituting meta {} with solution", flex.head.id);
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

type UnifyResult<'db> = Result<(), UnificationError<'db>>;
// type UnifyFuture<'db> = dyn Future<Output = UnifyResult<'db>>;

pub fn antiunify<'db, 'g>(
    ctx: SolverEnvironment<'db, 'g>,
    lhs: Rc<Value<'db>>,
    rhs: Rc<Value<'db>>,
    ty: Rc<Value<'db>>,
) -> (impl Future<Output = UnifyResult<'db>> + 'g, Rc<Value<'db>>) {
    // Clone values that need to be used multiple times
    let meta_id = ctx.fresh_meta_id(ty.clone());
    let local_env = ctx.tc_env.values.local.clone();
    let ty_clone = ty.clone();
    let lhs_clone = lhs.clone();
    let ctx_clone = ctx.clone();

    let future = async move {
        unify(ctx, lhs, rhs, ty).await?;
        ctx_clone.define_meta(meta_id, lhs_clone);
        Ok(())
    };

    (
        future,
        Rc::new(Value::metavariable(meta_id, local_env, ty_clone)),
    )
}

pub async fn unify<'db, 'g>(
    ctx: SolverEnvironment<'db, 'g>,
    lhs: Rc<Value<'db>>,
    rhs: Rc<Value<'db>>,
    ty: Rc<Value<'db>>,
) -> UnifyResult<'db> {
    println!("[Unify] Unifying {:?} == {:?}", lhs, rhs);

    // Force the current type, block if it's a metavariable.

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
            let dom_fut = Box::pin(unify(
                ctx.clone(),
                pi1.source.clone(),
                pi2.source.clone(),
                ty.clone(),
            ));

            // Create a fresh metavariable for the anti-unifier's domain type.
            // This will be solved once the domain unification completes.
            let dom_meta = ctx.fresh_meta_id(ty.clone());
            println!(
                "[Unify] Created domain anti-unifier metavariable {}",
                dom_meta
            );
            let dom_fut = async {
                // If domain unification succeeded, solve the domain metavariable.
                dom_fut.await?;
                ctx.define_meta(dom_meta, pi1.source.clone());
                Ok(())
            };

            // Instantiate both closures with the fresh variable to get codomain values.
            let dom_var_ty = Rc::new(Value::metavariable(
                dom_meta,
                ctx.tc_env.values.local.clone(),
                ty.clone(),
            ));
            let dom_var = ctx.tc_env.push_var(dom_var_ty.clone());
            let cod1 = run_closure(ctx.tc_env.values.global, &pi1.target, [dom_var.clone()])?;
            let cod2 = run_closure(ctx.tc_env.values.global, &pi2.target, [dom_var])?;

            // Unify the codomains concurrently with the domain
            println!("[Unify] Unifying Pi codomains: {:?} == {:?}", cod1, cod2);
            let cod_fut = Box::pin(unify(ctx, cod1, cod2, ty.clone()));

            // Wait for both domain and codomain unification to complete concurrently.
            let (dom_result, cod_result) = join!(dom_fut, cod_fut);

            // Propagate domain errors first, codomain errors second.
            dom_result?;
            cod_result
        }

        // Handle Lambda injectivity
        // Similar pattern to Pi: instantiate closures with fresh variable and unify bodies
        (Value::Lambda(lam1), Value::Lambda(lam2)) => {
            println!("[Unify] Lambda injectivity");
            let Value::Pi(pi) = &*ty else {
                return Err(UnificationError::Generic(
                    "Expected Pi type for lambda unification".to_string(),
                ));
            };

            // Create a fresh variable to instantiate both lambda bodies
            let var = ctx.tc_env.push_var(pi.source.clone());

            // Instantiate both closures with the fresh variable
            let body1 = run_closure(ctx.tc_env.values.global, &lam1.body, [var.clone()])?;
            let body2 = run_closure(ctx.tc_env.values.global, &lam2.body, [var.clone()])?;

            // Instantiate the codomain type with the fresh variable.
            let codomain = run_closure(ctx.tc_env.values.global, &pi.target, [var])?;

            // Unify the bodies
            println!("[Unify] Unifying Lambda bodies: {:?} == {:?}", body1, body2);
            Box::pin(unify(ctx, body1, body2, codomain)).await
        }

        // Eta-expansion: Lambda on left, non-lambda on right
        // Unify λx. body with t by unifying body with (t x)
        (Value::Lambda(lam), _) => {
            println!("[Unify] Eta-expansion: Lambda on left");
            let Value::Pi(pi) = &*ty else {
                return Err(UnificationError::Generic(
                    "Expected Pi type for lambda unification".to_string(),
                ));
            };

            // Create a fresh variable to instantiate the lambda.
            let var = ctx.tc_env.push_var(pi.source.clone());

            // Instantiate the lambda body with the fresh variable.
            let lhs_body = run_closure(ctx.tc_env.values.global, &lam.body, [var.clone()])?;

            // Apply the right side to the fresh variable
            let rhs_applied = run_application(ctx.tc_env.values.global, &rhs, var.clone())?;

            // Instantiate the codomain type with the fresh variable.
            let codomain = run_closure(ctx.tc_env.values.global, &pi.target, [var])?;

            // Unify the lambda body with the applied right side
            println!("[Unify] Unifying lambda body with applied term");
            Box::pin(unify(ctx, lhs_body, rhs_applied, codomain)).await
        }

        // Eta-expansion: non-lambda on left, Lambda on right
        // Unify t with λx. body by unifying (t x) with body
        (_, Value::Lambda(lam)) => {
            println!("[Unify] Eta-expansion: Lambda on right");
            let Value::Pi(pi) = &*ty else {
                return Err(UnificationError::Generic(
                    "Expected Pi type for lambda unification".to_string(),
                ));
            };

            // Create a fresh variable to instantiate the lambda.
            let var = ctx.tc_env.push_var(pi.source.clone());

            // Apply the right side to the fresh variable
            let lhs_applied = run_application(ctx.tc_env.values.global, &lhs, var.clone())?;

            // Instantiate the lambda body with the fresh variable.
            let rhs_body = run_closure(ctx.tc_env.values.global, &lam.body, [var.clone()])?;

            // Instantiate the codomain type with the fresh variable.
            let codomain = run_closure(ctx.tc_env.values.global, &pi.target, [var])?;

            // Unify the lambda body with the applied right side
            println!("[Unify] Unifying applied term with lambda body");
            Box::pin(unify(ctx, lhs_applied, rhs_body, codomain)).await
        }

        // Handle TypeConstructor injectivity
        (Value::TypeConstructor(tc1), Value::TypeConstructor(tc2)) => {
            // Check that the constructor is the same.
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

            // Look up the type info.
            let type_info = ctx
                .tc_env
                .values
                .global
                .type_constructor(tc1.constructor)
                .map_err(|e| UnificationError::Generic(format!("{:?}", e)))?
                .clone();

            // Create a new environment.
            let mut env = Environment {
                global: ctx.tc_env.values.global,
                local: LocalEnv::new(),
            };

            println!("[Unify] Type constructor injectivity");

            // Collect all futures into a vector
            let mut arg_futs = Vec::new();
            for (arg1, arg2, syn_ty) in izip!(
                tc1.arguments.iter(),
                tc2.arguments.iter(),
                type_info.arguments.iter()
            ) {
                // Evaluate the type of the current argument.
                let sem_ty = eval::eval(&mut env, &syn_ty)?;

                // Unify the arguments.
                let arg_fut = unify(ctx.clone(), arg1.clone(), arg2.clone(), sem_ty);
                arg_futs.push(arg_fut);

                // Push the semantic argument into the environment for the next iteration.
                env.push(arg1.clone())
            }

            // Await all futures concurrently, and check the results from left to right.
            let results = join_all(arg_futs).await;
            for result in results {
                result?;
            }
            Ok(())
        }

        // Handle DataConstructor injectivity
        (Value::DataConstructor(dc1), Value::DataConstructor(dc2)) => {
            // Check that the type is a type constructor.
            let Value::TypeConstructor(tc) = &*ty else {
                return Err(UnificationError::Generic(
                    "Expected type constructor type for data constructor unification".to_string(),
                ));
            };

            // Check that the constructor is the same.
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

            // Look up the type constructor info.
            let type_info = ctx
                .tc_env
                .values
                .global
                .type_constructor(tc.constructor)
                .map_err(|e| UnificationError::Generic(format!("{:?}", e)))?
                .clone();

            // Look up the data constructor info.
            let data_info = ctx
                .tc_env
                .values
                .global
                .data_constructor(dc1.constructor)
                .map_err(|e| UnificationError::Generic(format!("{:?}", e)))?
                .clone();

            // Find the number of parameters.
            let num_parameters = type_info.num_parameters();

            // Create an array of just the parameters, leaving out the indices.
            let parameters = tc.iter().take(num_parameters).cloned().collect();

            // Create an environment for evaluating the type of each argument, with
            // parameters in the context.
            let mut env = Environment {
                global: ctx.tc_env.values.global,
                local: LocalEnv::new(),
            };
            env.extend(parameters);

            println!("[Unify] Data constructor injectivity");
            let mut arg_futs = Vec::new();
            for (arg1, arg2, syn_ty) in izip!(
                dc1.arguments.iter(),
                dc2.arguments.iter(),
                data_info.arguments.iter()
            ) {
                // Evaluate the type of the current argument.
                let sem_ty = eval::eval(&mut env, &syn_ty)?;

                // Unify the arguments.
                let arg_fut = unify(ctx.clone(), arg1.clone(), arg2.clone(), sem_ty);
                arg_futs.push(arg_fut);

                // Push the semantic argument into the environment for the next iteration.
                env.push(arg1.clone())
            }

            // Await all futures concurrently, and check the results from left to right.
            let results = join_all(arg_futs).await;
            for result in results {
                result?;
            }
            Ok(())
        }

        // Handle Flex-Flex unification (both sides are metavariables)
        (Value::Flex(f1), Value::Flex(f2)) => {
            println!("[Unify] Flex-Flex: {} vs {}", f1.head.id, f2.head.id);

            // Check if they're the same metavariable.
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
            // Check that the head terms are the same.
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
    ctx: SolverEnvironment<'db, 'g>,
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
                app1.argument.ty.clone(),
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
    ctx: SolverEnvironment<'db, 'g>,
    spine1: &hwml_core::val::Spine<'db>,
    spine2: &hwml_core::val::Spine<'db>,
) -> Result<(), UnificationError<'db>> {
    // Check that the spines have the same length.
    if spine1.len() != spine2.len() {
        return Err(UnificationError::SpineLengthMismatch(
            spine1.len(),
            spine2.len(),
        ));
    }

    println!("[Unify] Unifying spines of length {}", spine1.len());

    let mut futures = Vec::new();
    for (e1, e2) in spine1.iter().zip(spine2.iter()) {
        let future = Box::pin(unify_eliminator(ctx.clone(), e1, e2));
        futures.push(future);
    }

    // Await all eliminator unifications concurrently
    let results = join_all(futures).await;
    for result in results {
        result?;
    }
    Ok(())
}

/// Perform lowering on a flexible term with a non-empty spine.
/// U : Pi A B |- U[S] => V : B |- U[S] <- \x. V[S, x]
///
///
/// Val::Lam(env, body: Syntax {
///   App(App(Meta(V), S), x)
/// })
///
/// Flex(U[S], [z])
/// (\x. V S.. x) [z]
/// VFlex[]
///
async fn lower_flex<'g: 'db, 'db>(
    ctx: SolverEnvironment<'db, 'g>,
    flex: hwml_core::val::Flex<'db>,
) -> Result<Rc<Value<'db>>, UnificationError<'db>> {
    let mut env = flex.head.local.clone();

    // Create the inner term of the lambda
    // Given, ?M[S] a b c, create ?N[S, a, b, c]
    for elim in flex.spine.iter() {
        match elim {
            hwml_core::val::Eliminator::Application(app) => {
                env.push(app.argument.value.clone());
            }
            _ => {
                todo!("Lowering for non-application eliminators not implemented yet");
            }
        }
    }

    // TODO: THIS DOES NOT WORK AT ALL
    // to wrap the metavariable up in lambdas, we need a closure for the body
    // this is a pair of environment and syntax
    // we need probably need to perform real renaming here...
    let mut term = Rc::new(Value::flex(
        flex.head,
        hwml_core::val::Spine::new(vec![]),
        flex.ty,
    ));

    // Wrap the term in constructors.
    // Given, ?M[S] a b c, create \a .(\b .(\c .?N[S, a, b, c, x]))
    for elim in flex.spine.iter().rev() {
        match elim {
            hwml_core::val::Eliminator::Application(app) => {
                let arg_value = app.argument.value.clone();
                term = run_application(ctx.tc_env.values.global, &term, arg_value)?;
            }
            _ => {
                todo!("Lowering for non-application eliminators not implemented yet");
            }
        }
    }

    Ok(term)
}

// ============================================================================
// PATTERN UNIFICATION
// ============================================================================

/// Rename an eliminator according to a renaming.
fn rename_eliminator<'db, 'g>(
    ctx: &SolverEnvironment<'db, 'g>,
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
fn rename_spine<'db, 'g>(
    ctx: &SolverEnvironment<'db, 'g>,
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
fn rename<'db, 'g>(
    ctx: &SolverEnvironment<'db, 'g>,
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
    ctx: SolverEnvironment<'db, 'g>,
    depth: usize,
    meta_variable: &hwml_core::val::MetaVariable<'db>,
    solution: Rc<Value<'db>>,
    _ty: Rc<Value<'db>>,
) -> Result<(), UnificationError<'db>> {
    println!(
        "[Solve] Solving metavariable {} with pattern unification",
        meta_variable.id
    );

    // Create an initial renaming from the spine
    let mut renaming = renaming::invert_substitution(&ctx, depth, &meta_variable.local)?;

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
