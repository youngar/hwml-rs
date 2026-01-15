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
    // Renaming Error.
    RenamingError(renaming::Error<'db>),
    /// Generic error
    Generic(String),
}

impl<'db> fmt::Display for UnificationError<'db> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Generic(msg) => {
                write!(f, "error: {}", msg)
            }
            Self::Eval(e) => write!(f, "Evaluation error: {:?}", e),
            Self::Mismatch(lhs, rhs) => {
                write!(f, "Cannot unify {:?} with {:?}", lhs, rhs)
            }
            Self::MismatchEliminator(lhs, rhs) => {
                write!(f, "Eliminator mismatch: {:?} vs {:?}", lhs, rhs)
            }
            Self::MismatchSpine(s1, s2) => {
                write!(f, "Spine mismatch: length {} vs {}", s1.len(), s2.len())
            }
            Self::TypeConstructorMismatch(tc1, tc2) => {
                write!(f, "Type constructor mismatch: {} vs {}", tc1, tc2)
            }
            Self::DataConstructorMismatch(dc1, dc2) => {
                write!(f, "Data constructor mismatch: {} vs {}", dc1, dc2)
            }
            Self::ArgumentCountMismatch(count1, count2) => {
                write!(f, "Argument count mismatch: {} vs {}", count1, count2)
            }
            Self::RigidHeadMismatch(head1, head2) => {
                write!(f, "Rigid head mismatch: {} vs {}", head1, head2)
            }
            Self::SpineLengthMismatch(len1, len2) => {
                write!(f, "Spine length mismatch: {} vs {}", len1, len2)
            }
            Self::NonLinearApplication(elim) => {
                write!(
                    f,
                    "Non-linear pattern: variable appears multiple times in spine: {:?}",
                    elim
                )
            }
            Self::BlockedSolution(elim) => {
                write!(
                    f,
                    "Blocked solution: spine contains non-variable term: {:?}",
                    elim
                )
            }
            Self::OccursCheck(meta) => {
                write!(
                    f,
                    "Occurs check failed: metavariable {} occurs in its own solution",
                    meta
                )
            }
            Self::ScopingError(value) => {
                write!(
                    f,
                    "Scoping error: solution references out-of-scope variables: {:?}",
                    value
                )
            }
            Self::Quote(msg) => {
                write!(f, "Quotation error: {}", msg)
            }
            Self::InversionError(e) => write!(f, "inversion error: {}", e),
            Self::RenamingError(_) => write!(f, "renaming error"),
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

impl<'db> From<renaming::Error<'db>> for UnificationError<'db> {
    fn from(e: renaming::Error<'db>) -> Self {
        Self::RenamingError(e)
    }
}

async fn whnf<'db, 'g>(
    ctx: &SolverEnvironment<'db, 'g>,
    mut value: Rc<Value<'db>>,
) -> Result<Rc<Value<'db>>, UnificationError<'db>> {
    let global = ctx.tc_env.values.global;
    while let Value::Flex(flex) = &*value {
        println!("[WHNF] Substituting meta {} with solution", flex.head.id);
        let syn_solution =
            WaitForResolved::new(ctx.clone(), flex.head.id, BlockReason::generic("whnf")).await;
        let sem_solution =
            eval::substitute(global, &syn_solution, flex.head.local.clone()).unwrap();
        value = run_spine(global, sem_solution, &flex.spine)?;
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

pub fn fresh_meta<'db, 'g>(ctx: SolverEnvironment<'db, 'g>, ty: Rc<Value<'db>>) -> Rc<Value<'db>> {
    let id = ctx.fresh_meta_id(ty.clone());
    let substitution = ctx.tc_env.values.local.clone();
    Rc::new(Value::metavariable(id, substitution, ty))
}

pub fn antiunify<'db, 'g>(
    db: &'db dyn salsa::Database,
    ctx: SolverEnvironment<'db, 'g>,
    lhs: Rc<Value<'db>>,
    rhs: Rc<Value<'db>>,
    ty: Rc<Value<'db>>,
) -> (impl Future<Output = UnifyResult<'db>> + 'g, Rc<Value<'db>>) {
    let anti_meta = fresh_meta(ctx.clone(), ty.clone());
    let anti_meta_clone = anti_meta.clone();
    let future = async move {
        Box::pin(unify(db, ctx.clone(), lhs.clone(), rhs, ty.clone())).await?;
        Box::pin(unify(db, ctx, anti_meta_clone, lhs, ty)).await?;
        Ok(())
    };
    (future, anti_meta)
}

pub async fn unify<'db, 'g>(
    db: &'db dyn salsa::Database,
    mut ctx: SolverEnvironment<'db, 'g>,
    lhs: Rc<Value<'db>>,
    rhs: Rc<Value<'db>>,
    ty: Rc<Value<'db>>,
) -> UnifyResult<'db> {
    println!("[Unify] Unifying {:?} == {:?}", lhs, rhs);
    let global = ctx.tc_env.values.global;
    let ty = whnf(&ctx, ty).await?;
    let lhs = force(&ctx, lhs)?;
    let rhs = force(&ctx, rhs)?;
    match (&*lhs, &*rhs) {
        (Value::Constant(c1), Value::Constant(c2)) => {
            if c1 == c2 {
                println!("[Unify] Constants are equal");
                Ok(())
            } else {
                Err(UnificationError::Mismatch(lhs, rhs))
            }
        }
        (Value::Universe(u1), Value::Universe(u2)) => {
            if u1.level == u2.level {
                println!("[Unify] Universes at same level");
                Ok(())
            } else {
                Err(UnificationError::Mismatch(lhs, rhs))
            }
        }
        (Value::Pi(pi1), Value::Pi(pi2)) => {
            println!("[Unify] Pi injectivity");
            let (source_fut, source) = antiunify(
                db,
                ctx.clone(),
                pi1.source.clone(),
                pi2.source.clone(),
                ty.clone(),
            );
            let var = ctx.tc_env.push_var(source);
            let lhs_target = run_closure(global, &pi1.target, [var.clone()])?;
            let rhs_target = run_closure(global, &pi2.target, [var])?;
            println!(
                "[Unify] Unifying Pi codomains: {:?} == {:?}",
                lhs_target, rhs_target
            );
            let target_fut = Box::pin(unify(db, ctx, lhs_target, rhs_target, ty.clone()));
            let (source_result, target_result) = join!(source_fut, target_fut);
            source_result?;
            target_result
        }
        (Value::Lambda(lam1), Value::Lambda(lam2)) => {
            println!("[Unify] Lambda injectivity");
            let Value::Pi(pi) = &*ty else {
                return Err(UnificationError::Generic(
                    "Expected Pi type for lambda unification".to_string(),
                ));
            };
            let var = ctx.tc_env.push_var(pi.source.clone());
            let body1 = run_closure(ctx.tc_env.values.global, &lam1.body, [var.clone()])?;
            let body2 = run_closure(ctx.tc_env.values.global, &lam2.body, [var.clone()])?;
            let target = run_closure(ctx.tc_env.values.global, &pi.target, [var])?;
            println!("[Unify] Unifying Lambda bodies: {:?} == {:?}", body1, body2);
            Box::pin(unify(db, ctx, body1, body2, target)).await
        }
        // Eta-expansion: Lambda on left, non-lambda on right
        // Unify λx. body with t by unifying body with (t x)
        // (Value::Lambda(lam), _) => {
        //     println!("[Unify] Eta-expansion: Lambda on left");
        //     let Value::Pi(pi) = &*ty else {
        //         return Err(UnificationError::Generic(
        //             "Expected Pi type for lambda unification".to_string(),
        //         ));
        //     };

        //     // Create a fresh variable to instantiate the lambda.
        //     let var = ctx.tc_env.push_var(pi.source.clone());

        //     // Instantiate the lambda body with the fresh variable.
        //     let lhs_body = run_closure(ctx.tc_env.values.global, &lam.body, [var.clone()])?;

        //     // Apply the right side to the fresh variable
        //     let rhs_applied = run_application(ctx.tc_env.values.global, &rhs, var.clone())?;

        //     // Instantiate the codomain type with the fresh variable.
        //     let codomain = run_closure(ctx.tc_env.values.global, &pi.target, [var])?;

        //     // Unify the lambda body with the applied right side
        //     println!("[Unify] Unifying lambda body with applied term");
        //     Box::pin(unify(ctx, lhs_body, rhs_applied, codomain)).await
        // }

        // Eta-expansion: non-lambda on left, Lambda on right
        // Unify t with λx. body by unifying (t x) with body
        // (_, Value::Lambda(lam)) => {
        //     println!("[Unify] Eta-expansion: Lambda on right");
        //     let Value::Pi(pi) = &*ty else {
        //         return Err(UnificationError::Generic(
        //             "Expected Pi type for lambda unification".to_string(),
        //         ));
        //     };

        //     // Create a fresh variable to instantiate the lambda.
        //     let var = ctx.tc_env.push_var(pi.source.clone());

        //     // Apply the right side to the fresh variable
        //     let lhs_applied = run_application(ctx.tc_env.values.global, &lhs, var.clone())?;

        //     // Instantiate the lambda body with the fresh variable.
        //     let rhs_body = run_closure(ctx.tc_env.values.global, &lam.body, [var.clone()])?;

        //     // Instantiate the codomain type with the fresh variable.
        //     let codomain = run_closure(ctx.tc_env.values.global, &pi.target, [var])?;

        //     // Unify the lambda body with the applied right side
        //     println!("[Unify] Unifying applied term with lambda body");
        //     Box::pin(unify(ctx, lhs_applied, rhs_body, codomain)).await
        // }

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
                let arg_fut = unify(db, ctx.clone(), arg1.clone(), arg2.clone(), sem_ty);
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
            let parameters = tc.iter().take(num_parameters).cloned();

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
                let arg_fut = unify(db, ctx.clone(), arg1.clone(), arg2.clone(), sem_ty);
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
        (Value::Flex(f1), Value::Flex(f2)) if f1.head.id == f2.head.id => {
            println!("[Unify] Same metavariable, unifying spines");
            Box::pin(unify_spine(db, ctx, &f1.spine, &f2.spine)).await
        }
        (Value::Flex(flex), _) => {
            println!("[Unify] Solving meta {} with right side", flex.head.id);
            let depth = ctx.tc_env.values.depth();
            Box::pin(try_solve(db, ctx, depth, &flex.head, rhs, &ty)).await
        }
        (_, Value::Flex(flex)) => {
            println!("[Unify] Solving meta {} with left side", flex.head.id);
            let depth = ctx.tc_env.values.depth();
            Box::pin(try_solve(db, ctx, depth, &flex.head, lhs, &ty)).await
        }
        (Value::Rigid(r1), Value::Rigid(r2)) => {
            // Check that the head terms are the same.
            if r1.head != r2.head {
                return Err(UnificationError::RigidHeadMismatch(
                    format!("{:?}", r1.head),
                    format!("{:?}", r2.head),
                ));
            }
            println!("[Unify] Rigid neutrals with same head");
            Box::pin(unify_spine(db, ctx, &r1.spine, &r2.spine)).await
        }
        _ => Err(UnificationError::Mismatch(lhs, rhs)),
    }
}

/// Unify two eliminators (applications, projections, etc.)
async fn unify_eliminator<'db, 'g>(
    db: &'db dyn salsa::Database,
    ctx: SolverEnvironment<'db, 'g>,
    lhs: &Eliminator<'db>,
    rhs: &Eliminator<'db>,
) -> Result<(), UnificationError<'db>> {
    match (lhs, rhs) {
        (Eliminator::Application(app1), Eliminator::Application(app2)) => {
            println!("[Unify] Application eliminator");
            Box::pin(unify(
                db,
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
async fn unify_spine<'db, 'g>(
    db: &'db dyn salsa::Database,
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
        let future = Box::pin(unify_eliminator(db, ctx.clone(), e1, e2));
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

async fn try_solve<'db, 'g>(
    db: &'db dyn salsa::Database,
    ctx: SolverEnvironment<'db, 'g>,
    depth: usize,
    meta_variable: &hwml_core::val::MetaVariable<'db>,
    sem_solution: Rc<Value<'db>>,
    ty: &Rc<Value<'db>>,
) -> Result<(), UnificationError<'db>> {
    println!(
        "[Solve] Solving metavariable {} with pattern unification",
        meta_variable.id
    );
    let mut renaming = renaming::invert_substitution(&ctx, depth, &meta_variable.local)?;
    let syn_solution = rename(
        db,
        ctx.tc_env.values.global,
        meta_variable.id,
        &mut renaming,
        ty,
        &sem_solution,
    )?;
    println!(
        "[Solve] Solved metavariable {} := {:?}",
        meta_variable.id, syn_solution
    );
    ctx.solve(meta_variable.id, syn_solution);
    Ok(())
}
