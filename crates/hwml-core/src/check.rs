use crate::binding::Binding;
use crate::common::{Level, UniverseLevel};
use crate::equal;
use crate::eval;
use crate::pattern_unify;
use crate::quote;
use crate::syn as stx;
use crate::syn;
use crate::syn::Syntax;
use crate::val;
use crate::val::{Environment, LocalEnv, Value};
use crate::RcValue;
use crate::*;
use salsa::Database;
use std::collections::HashSet;
use std::rc::Rc;

#[derive(Clone)]
pub struct TCEnvironment<'db, 'g> {
    pub db: &'db dyn Database,
    pub values: val::Environment<'db, 'g>,
    pub types: Vec<RcValue<'db>>,
}

impl<'db, 'g> TCEnvironment<'db, 'g> {
    fn global_env(&self) -> &'g val::GlobalEnv<'db> {
        self.values.global
    }

    fn local_env(&self) -> &val::LocalEnv<'db> {
        &self.values.local
    }

    fn context(&self) -> &Vec<RcValue<'db>> {
        &self.types
    }

    pub fn type_of(&self, level: Level) -> &RcValue<'db> {
        let index: usize = level.into();
        &self.types[index]
    }

    fn var_type(&self, var: &stx::Variable) -> &RcValue<'db> {
        let level = var.index.to_level(self.depth());
        self.type_of(level)
    }

    #[allow(dead_code)]
    fn value_of(&self, level: Level) -> RcValue<'db> {
        self.values.get(level)
    }

    #[allow(dead_code)]
    fn var_value(&self, var: &stx::Variable) -> RcValue<'db> {
        let level = var.index.to_level(self.depth());
        self.value_of(level)
    }

    fn push(&mut self, value: RcValue<'db>, ty: RcValue<'db>) {
        self.values.push(value);
        self.types.push(ty);
    }

    pub fn push_var(&mut self, ty: RcValue<'db>) -> RcValue<'db> {
        let var = Value::variable_rc(Level::new(self.depth()), ty.clone());
        self.push(var.clone(), ty);
        var
    }

    fn push_transparent(&mut self, ty: RcValue<'db>, value: RcValue<'db>) {
        self.values.push_transparent(ty.clone(), value);
        self.types.push(ty);
    }

    fn pop(&mut self) {
        self.values.pop();
        self.types.pop();
    }

    pub fn truncate(&mut self, depth: usize) {
        self.values.truncate(depth);
        self.types.truncate(depth);
    }

    pub fn depth(&self) -> usize {
        self.values.depth()
    }

    pub fn under_binder<F, R>(&mut self, ty: RcValue<'db>, f: F) -> Binding<R>
    where
        F: FnOnce(&mut Self) -> R,
    {
        let depth = self.depth();
        self.push_var(ty);
        let body = f(self);
        self.truncate(depth);
        Binding { body }
    }

    #[allow(dead_code)]
    fn extend_vars<T>(&mut self, types: T)
    where
        T: IntoIterator<Item = RcValue<'db>>,
    {
        for ty in types {
            self.values.push_var(ty.clone());
            self.types.push(ty);
        }
    }

    pub fn quote_at_depth(
        &self,
        tm: &RcValue<'db>,
        ty: &RcValue<'db>,
        depth: usize,
    ) -> RcSyntax<'db> {
        quote::quote(self.global_env(), depth, tm, ty).unwrap()
    }

    pub fn quote(&self, tm: &RcValue<'db>, ty: &RcValue<'db>) -> RcSyntax<'db> {
        self.quote_at_depth(tm, ty, self.depth())
    }

    pub fn quote_bound(&self, tm: Binding<&RcValue<'db>>, ty: &RcValue<'db>) -> RcSyntax<'db> {
        self.quote_at_depth(tm.body, ty, self.depth() + 1)
    }

    /// Build a syntactic substitution from this local environment.
    pub fn syn_substitution(&self) -> Vec<RcSyntax<'db>> {
        let mut substitution: Vec<RcSyntax<'db>> = Vec::new();
        for i in 0..self.depth() {
            let tm: &RcValue<'db> = self.local_env().get(Level(i));
            let ty: &RcValue<'db> = self.context().get(i).unwrap();
            let syn_tm: RcSyntax<'db> = self.quote(tm, ty);
        }
        for (tm, ty) in self.local_env().iter().zip(self.context()) {
            substitution.push(self.quote(tm, &ty));
        }
        substitution
    }

    /// Apply substitutions from pattern unification.
    /// Mutates variables to let-bindings and re-evaluates dependent types.
    pub fn apply_subst(&mut self, solutions: &[(Level, RcValue<'db>)]) -> Result<(), Error<'db>> {
        for (level, value) in solutions {
            self.values.set(*level, value.clone());
        }

        for k in 0..self.types.len() {
            let quoted_ty = quote::type_quote(self.values.global, k, &self.types[k])?;
            let mut historical_env = self.values.clone();
            historical_env.truncate(k);
            let new_ty = eval::eval(&mut historical_env, &quoted_ty)?;
            self.types[k] = new_ty;
        }

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub enum Error<'db> {
    /// Cannot synthesize a type.
    BadSynth {
        tm: RcSyntax<'db>,
    },
    /// Bad type.
    BadType {
        tm: RcSyntax<'db>,
    },
    /// Bad elimination.
    BadElim {
        tm: RcSyntax<'db>,
        ty_got: RcValue<'db>,
    },
    /// Bad constructor.
    BadCtor {
        tm: RcSyntax<'db>,
        ty_exp: RcValue<'db>,
    },
    /// Inferred a type that did not match the expected type.
    BadCheck {
        tm: RcSyntax<'db>,
        ty_exp: RcValue<'db>,
        ty_got: RcValue<'db>,
    },
    EvaluationFailure(eval::Error),
    LookupError(val::LookupError<'db>),
    MatchOnNonDatatype(RcValue<'db>),
    QuoteError(quote::Error<'db>),
    PatternUnifyError(pattern_unify::Error<'db>),
    PatternUnifyStuck {
        tm: RcSyntax<'db>,
        meta_id: crate::common::MetaVariableId,
    },
    NonExhaustiveMatch {
        tm: RcSyntax<'db>,
        missing: Vec<String>,
    },
}

impl<'db> From<eval::Error> for Error<'db> {
    fn from(e: eval::Error) -> Self {
        Error::EvaluationFailure(e)
    }
}

impl<'db> From<quote::Error<'db>> for Error<'db> {
    fn from(e: quote::Error<'db>) -> Self {
        Error::QuoteError(e)
    }
}

impl<'db> From<pattern_unify::Error<'db>> for Error<'db> {
    fn from(e: pattern_unify::Error<'db>) -> Self {
        Error::PatternUnifyError(e)
    }
}

impl<'db> std::fmt::Display for Error<'db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::BadSynth { tm } => {
                write!(f, "cannot infer type for term: {tm:?}")
            }
            Error::BadType { tm } => {
                write!(f, "expected a type, but got: {tm:?}")
            }
            Error::BadElim { tm, ty_got } => {
                write!(
                    f,
                    "bad elimination: cannot apply or match on term of type {ty_got:?}\n  in: {tm:?}"
                )
            }
            Error::BadCtor { tm, ty_exp } => {
                write!(
                    f,
                    "constructor does not match expected type {ty_exp:?}\n  in: {tm:?}"
                )
            }
            Error::BadCheck { tm, ty_exp, ty_got } => {
                write!(
                    f,
                    "type mismatch:\n  expected: {ty_exp:?}\n  got: {ty_got:?}\n  in: {tm:?}"
                )
            }
            Error::EvaluationFailure(e) => {
                write!(f, "evaluation failed: {e:?}")
            }
            Error::LookupError(e) => {
                write!(f, "lookup error: {e:?}")
            }
            Error::MatchOnNonDatatype(ty) => {
                write!(f, "cannot pattern match on non-datatype: {ty:?}")
            }
            Error::QuoteError(e) => {
                write!(f, "quotation error: {e:?}")
            }
            Error::PatternUnifyError(e) => {
                write!(f, "pattern unification failed: {e}")
            }
            Error::PatternUnifyStuck { tm, meta_id } => {
                write!(
                    f,
                    "pattern match blocked on unsolved metavariable ?{}\n\
                     help: add a type annotation to resolve the ambiguity",
                    meta_id.local_index
                )
            }
            Error::NonExhaustiveMatch { tm, missing } => {
                write!(f, "non-exhaustive pattern match\n  missing constructor")?;
                if missing.len() > 1 {
                    write!(f, "s")?;
                }
                write!(f, ": ")?;
                for (i, name) in missing.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "@{name}")?;
                }
                Ok(())
            }
        }
    }
}

impl<'db> std::error::Error for Error<'db> {}

use std::result::Result;

/// Evaluate a syntactic term to a semantic value.
fn eval<'db, 'g>(
    env: &TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    let mut sem_env = env.values.clone();
    eval::eval(&mut sem_env, term).map_err(Error::EvaluationFailure)
}

/// Adaptor for running a closure from the semantic domain.
fn run_closure<'db, 'g, T>(
    env: &TCEnvironment<'db, 'g>,
    closure: &val::Closure<'db>,
    args: T,
) -> Result<RcValue<'db>, Error<'db>>
where
    T: IntoIterator<Item = RcValue<'db>>,
{
    eval::run_closure(env.values.global, closure, args).map_err(Error::EvaluationFailure)
}

/// Synthesize (infer) types for variables and elimination forms.
pub fn type_synth<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    match term {
        Syntax::Variable(variable) => type_synth_variable(env, variable),
        Syntax::Constant(constant) => type_synth_constant(env, constant),
        Syntax::Prim(prim) => type_synth_prim(env, prim),
        Syntax::Check(check) => type_synth_check(env, check),
        Syntax::Let(let_expr) => type_synth_let(env, let_expr),
        Syntax::Application(application) => type_synth_application(env, application),
        Syntax::Metavariable(metavariable) => type_synth_metavariable(env, metavariable),

        // Universe: U_n : U_(n+1)
        // For simplicity, we use predicative universes where U_n : U_(n+1)
        Syntax::Universe(universe) => {
            let current_level: usize = universe.level.into();
            let next_level = crate::common::UniverseLevel::new(current_level + 1);
            Ok(Value::universe_rc(next_level))
        }

        // HardwareUniverse constructs - Lift is the only one that can be synthesized
        // Bit, HArrow, and Quote need to be checked against expected types
        Syntax::Lift(lift) => type_synth_lift(env, lift),

        // Eq type can synthesize: Eq A x y : U_i if A : U_i
        Syntax::Eq(eq) => type_synth_eq(env, eq),

        // Transport is an eliminator and synthesizes its type
        Syntax::Transport(transport) => type_synth_transport(env, transport),

        _ => Err(Error::BadSynth {
            tm: Rc::new(term.clone()),
        }),
    }
}

/// Synthesize a type for a variable.
pub fn type_synth_variable<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    variable: &syn::Variable<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    // Pull the type from the typing environment.
    Ok(env.var_type(variable).clone())
}

pub fn type_synth_constant<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    constant: &syn::Constant<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    let constant_info = env
        .values
        .global
        .constant(constant.name)
        .map_err(Error::LookupError)?;
    eval(env, &constant_info.ty)
}

/// Synthesize the type of a primitive by looking it up in the global environment.
/// Primitives have types but no definitions.
pub fn type_synth_prim<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    prim: &syn::Prim<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    // Look up the primitive in the global environment
    let prim_info = env
        .values
        .global
        .primitive(prim.name)
        .map_err(Error::LookupError)?;

    // Evaluate the type to get a Value
    eval(env, &prim_info.ty)
}

/// Synthesize the type of a term annotated with a type.
/// The type annotation must be a meta-level type (in Universe), not a hardware type.
pub fn type_synth_check<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    check: &syn::Check<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    // Check that the type is a valid meta-level type (not a hardware type)
    check_meta_type(env, &check.ty)?;
    let ty = eval(env, &check.ty)?;
    type_check(env, &check.term, &ty)?;
    Ok(ty)
}

pub fn type_synth_let<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    let_expr: &syn::Let<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    check_type(env, &let_expr.ty)?;
    let sem_ty = eval(env, &let_expr.ty)?;
    type_check(env, &let_expr.value, &sem_ty)?;
    let sem_value = eval(env, &let_expr.value)?;

    env.push_transparent(sem_ty, sem_value);
    let body_ty = type_synth(env, &let_expr.body.body)?;
    env.pop();

    Ok(body_ty)
}

/// Synthesize the type of a metavariable.
pub fn type_synth_metavariable<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    metavariable: &syn::Metavariable<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    // Lookup the metavariable info in the global environment.
    let meta_info = env
        .values
        .global
        .metavariable(metavariable.id)
        .map_err(|_| Error::BadSynth {
            tm: Syntax::metavariable_rc(metavariable.id, metavariable.substitution.clone()),
        })?;

    // The metavariable has a telescope of argument types.
    // We need to check that the substitution has the right number of arguments.
    if metavariable.substitution.len() != meta_info.arguments.len() {
        return Err(Error::BadSynth {
            tm: Syntax::metavariable_rc(metavariable.id, metavariable.substitution.clone()),
        });
    }

    // Check each argument against its expected type and build up the local environment.
    let mut local_env = LocalEnv::new();
    for (arg, arg_ty) in metavariable
        .substitution
        .iter()
        .zip(meta_info.arguments.iter())
    {
        // Evaluate the expected argument type in a temporary environment with the local_env.
        let mut temp_env = Environment {
            global: env.values.global,
            local: local_env.clone(),
            transparent: val::TransparentEnv::new(),
        };
        let expected_ty = eval::eval(&mut temp_env, arg_ty).map_err(|_| Error::BadSynth {
            tm: Syntax::metavariable_rc(metavariable.id, metavariable.substitution.clone()),
        })?;

        // Check the argument against the expected type.
        type_check(env, arg, &expected_ty)?;

        // Evaluate the argument and add it to the local environment.
        let arg_val = eval(env, arg)?;
        local_env.push(arg_val);
    }

    // Evaluate the final type in the extended local environment.
    let mut temp_env = Environment {
        global: env.values.global,
        local: local_env,
        transparent: val::TransparentEnv::new(),
    };
    let meta_ty = eval::eval(&mut temp_env, &meta_info.ty).map_err(|_| Error::BadSynth {
        tm: Syntax::metavariable_rc(metavariable.id, metavariable.substitution.clone()),
    })?;

    Ok(meta_ty)
}

/// Synthesize the type of a function application.
pub fn type_synth_application<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    application: &syn::Application<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    // First synthesize the type of the term being applied.
    let fun_ty = type_synth(env, &application.function)?;

    // Ensure that the applied term is a function `(x : src) -> tgt(x)`.
    let Value::Pi(pi) = &*fun_ty else {
        return Err(Error::BadElim {
            tm: Syntax::application_rc(application.function.clone(), application.argument.clone()),
            ty_got: fun_ty,
        });
    };

    // Check the argument against the source type of the function.
    type_check(env, &application.argument, &*pi.source)?;

    // The overall type is determined by substituting the argument into the target type.
    let arg = eval(env, &application.argument)?;
    run_closure(&env, &pi.target, [arg])
}

pub fn type_check_case<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    case: &syn::Case<'db>,
    expected_type: &Value<'db>,
) -> Result<(), Error<'db>> {
    let scrutinee_level = case.scrutinee.index.to_level(env.depth());
    let scrutinee_ty = env.type_of(scrutinee_level).clone();

    let Value::TypeConstructor(type_constructor) = &*scrutinee_ty else {
        return Err(Error::BadElim {
            tm: Syntax::case_rc(case.scrutinee.index, case.branches.clone()),
            ty_got: scrutinee_ty,
        });
    };

    let tcon_info = env
        .values
        .global
        .type_constructor(type_constructor.constructor)
        .map_err(Error::LookupError)?;

    let tcon_args: Vec<_> = type_constructor.arguments.iter().cloned().collect();
    let all_constructors = tcon_info.constructors().to_vec();
    let user_provided: HashSet<QualifiedName<'db>> =
        case.branches.iter().map(|b| b.constructor).collect();

    let base_depth = env.depth();
    let mut required_constructors: Vec<QualifiedName<'db>> = Vec::new();

    for &dcon_id in &all_constructors {
        let dcon_info = env
            .values
            .global
            .data_constructor(dcon_id)
            .map_err(Error::LookupError)?;

        let outcome = pattern_unify::unify_pattern(
            env.values.global,
            &env.values.transparent,
            &tcon_info,
            &tcon_args,
            dcon_id,
            &dcon_info,
            base_depth,
        )?;

        match outcome {
            pattern_unify::PatternUnifyOutcome::Success(_) => {
                required_constructors.push(dcon_id);
            }
            pattern_unify::PatternUnifyOutcome::Conflict => {}
            pattern_unify::PatternUnifyOutcome::Stuck(meta_id) => {
                return Err(Error::PatternUnifyStuck {
                    tm: Syntax::case_rc(case.scrutinee.index, case.branches.clone()),
                    meta_id,
                });
            }
        }
    }

    let missing: Vec<String> = required_constructors
        .iter()
        .filter(|c| !user_provided.contains(c))
        .map(|c| c.to_string(env.db))
        .collect();

    if !missing.is_empty() {
        return Err(Error::NonExhaustiveMatch {
            tm: Syntax::case_rc(case.scrutinee.index, case.branches.clone()),
            missing,
        });
    }
    for branch in &case.branches {
        let dcon_info = env
            .values
            .global
            .data_constructor(branch.constructor)
            .map_err(Error::LookupError)?;

        let branch_depth = env.depth();

        // Run pattern unification for this branch
        let outcome = pattern_unify::unify_pattern(
            env.values.global,
            &env.values.transparent,
            &tcon_info,
            &tcon_args,
            branch.constructor,
            &dcon_info,
            branch_depth,
        )?;

        match outcome {
            pattern_unify::PatternUnifyOutcome::Success(result) => {
                for binding in &result.new_bindings {
                    env.push_var(binding.ty.clone());
                }

                env.apply_subst(&result.solutions)?;

                let refined_expected_type = if result.solutions.is_empty() {
                    Rc::new(expected_type.clone())
                } else {
                    let quoted_expected =
                        quote::type_quote(env.values.global, branch_depth, expected_type)?;
                    let mut eval_env = env.values.clone();
                    eval::eval(&mut eval_env, &quoted_expected)?
                };

                type_check(env, &branch.body, &refined_expected_type)?;
                env.truncate(branch_depth);
            }

            pattern_unify::PatternUnifyOutcome::Conflict => {}

            pattern_unify::PatternUnifyOutcome::Stuck(meta_id) => {
                return Err(Error::PatternUnifyStuck {
                    tm: Syntax::case_rc(case.scrutinee.index, case.branches.clone()),
                    meta_id,
                });
            }
        }
    }

    Ok(())
}

/// Check types of terms against an expected type.
pub fn type_check<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
    ty: &Value<'db>,
) -> Result<(), Error<'db>> {
    match term {
        Syntax::Pi(pi) => type_check_pi(env, pi, ty),
        Syntax::Lambda(lam) => type_check_lambda(env, lam, ty),
        Syntax::Let(let_expr) => type_check_let(env, let_expr, ty),
        Syntax::TypeConstructor(tc) => type_check_type_constructor(env, tc, ty),
        Syntax::DataConstructor(dc) => type_check_data_constructor(env, dc, ty),
        Syntax::Case(case) => type_check_case(env, case, ty),

        // Signal types (Bit) live in SignalUniverse
        Syntax::Bit(_) => type_check_bit(env, ty),
        // Module types (HArrow) live in ModuleUniverse
        Syntax::HArrow(harrow) => type_check_harrow(env, harrow, ty),
        // Hardware types (SLift, MLift) live in HardwareUniverse
        Syntax::SLift(slift) => type_check_slift(env, slift, ty),
        Syntax::MLift(mlift) => type_check_mlift(env, mlift, ty),

        // Bit values (0 and 1) can be checked against ^(Sig Bit)
        Syntax::Zero(zero) => type_check_zero(env, zero, ty),
        Syntax::One(one) => type_check_one(env, one, ty),

        // Equality types and proofs
        Syntax::Eq(eq) => type_check_eq(env, eq, ty),
        Syntax::Refl(_) => type_check_refl(env, term, ty),
        // Transport is an eliminator - it synthesizes, so falls through to type_check_synth_term
        _ => type_check_synth_term(env, term, ty),
    }
}

fn type_check_pi<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    pi: &syn::Pi<'db>,
    ty: &Value<'db>,
) -> Result<(), Error<'db>> {
    let Value::Universe(expected_univ) = ty else {
        return Err(Error::BadCtor {
            tm: Syntax::pi_rc(pi.source.clone(), pi.target.clone()),
            ty_exp: Rc::new(ty.clone()),
        });
    };

    let source_ty = type_synth(env, &pi.source)?;
    let Value::Universe(source_univ) = &*source_ty else {
        return Err(Error::BadCtor {
            tm: Syntax::pi_rc(pi.source.clone(), pi.target.clone()),
            ty_exp: Rc::new(ty.clone()),
        });
    };

    let sem_source_ty = eval(env, &pi.source)?;

    env.push_var(sem_source_ty);
    let target_ty = type_synth(env, &pi.target)?;
    env.pop();

    let Value::Universe(target_univ) = &*target_ty else {
        return Err(Error::BadCtor {
            tm: Syntax::pi_rc(pi.source.clone(), pi.target.clone()),
            ty_exp: Rc::new(ty.clone()),
        });
    };

    // Pi type universe: max(source, target). Check cumulativity.
    let source_level: usize = source_univ.level.into();
    let target_level: usize = target_univ.level.into();
    let pi_level = source_level.max(target_level);
    let expected_level: usize = expected_univ.level.into();

    if pi_level > expected_level {
        return Err(Error::BadCtor {
            tm: Syntax::pi_rc(pi.source.clone(), pi.target.clone()),
            ty_exp: Rc::new(ty.clone()),
        });
    }

    Ok(())
}

fn type_check_lambda<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    lam: &syn::Lambda<'db>,
    ty: &Value<'db>,
) -> Result<(), Error<'db>> {
    match ty {
        Value::Pi(val::Pi {
            source,
            target: target_closure,
        }) => {
            let var = Value::variable_rc(Level::new(env.depth()), source.clone());
            let target = run_closure(env, target_closure, [var.clone()])?;
            env.push(var, source.clone());
            let r = type_check(env, &lam.body, &target);
            env.pop();
            r
        }
        _ => Err(Error::BadCtor {
            tm: Syntax::lambda_rc(lam.body.clone()),
            ty_exp: Rc::new(ty.clone()),
        }),
    }
}

fn type_check_let<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    let_expr: &syn::Let<'db>,
    expected_type: &Value<'db>,
) -> Result<(), Error<'db>> {
    check_type(env, &let_expr.ty)?;
    let sem_ty = eval(env, &let_expr.ty)?;
    type_check(env, &let_expr.value, &sem_ty)?;
    let sem_value = eval(env, &let_expr.value)?;

    env.push_transparent(sem_ty, sem_value);
    let result = type_check(env, &let_expr.body, expected_type);
    env.pop();

    result
}

fn type_check_type_constructor<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    tcon: &syn::TypeConstructor<'db>,
    ty: &Value<'db>,
) -> Result<(), Error<'db>> {
    match ty {
        Value::Universe(_u) => {
            // Lookup the type constructor info.
            let tcon_info = env
                .values
                .global
                .type_constructor(tcon.constructor)
                .map_err(Error::LookupError)?;

            // Check that the number of arguments matches the number of parameters.
            if tcon.arguments.len() != tcon_info.arguments.len() {
                return Err(Error::BadType {
                    tm: Syntax::type_constructor_rc(tcon.constructor, tcon.arguments.clone()),
                });
            }

            let mut ty_env = val::Environment {
                global: env.values.global,
                local: val::LocalEnv::new(),
                transparent: val::TransparentEnv::new(),
            };

            for (arg, arg_ty) in tcon.arguments.iter().zip(&tcon_info.arguments) {
                let sem_arg_ty = eval::eval(&mut ty_env, arg_ty)?;
                type_check(env, arg, &sem_arg_ty)?;
                let sem_arg = eval::eval(&mut env.values, arg)?;
                ty_env.push(sem_arg);
            }
            // TODO: we need to check that we are actually in the right universe.
            Ok(())
        }
        _ => Err(Error::BadCtor {
            tm: Syntax::type_constructor_rc(tcon.constructor, tcon.arguments.clone()),
            ty_exp: Rc::new(ty.clone()),
        }),
    }
}

fn type_check_data_constructor<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    dc: &syn::DataConstructor<'db>,
    ty_exp: &Value<'db>,
) -> Result<(), Error<'db>> {
    match ty_exp {
        Value::TypeConstructor(tc) => {
            let dc_info = env
                .values
                .global
                .data_constructor(dc.constructor)
                .map_err(Error::LookupError)?;
            let tc_info = env
                .values
                .global
                .type_constructor(tc.constructor)
                .map_err(Error::LookupError)?;

            let mut ty_env = val::Environment {
                global: env.values.global,
                local: val::LocalEnv::new(),
                transparent: val::TransparentEnv::new(),
            };

            let ps = tc.arguments[..tc_info.num_parameters].iter().cloned();
            ty_env.extend(ps);

            // TODO: check that we have the correct number of arguments.

            for (arg, arg_ty) in dc.arguments.iter().zip(&dc_info.arguments) {
                let sem_arg_ty = eval::eval(&mut ty_env, arg_ty)?;
                type_check(env, arg, &sem_arg_ty)?;
                let sem_arg = eval::eval(&mut env.values, arg)?;
                ty_env.push(sem_arg);
            }

            let ty_got = eval::eval(&mut ty_env, &dc_info.ty)?;
            match equal::type_equiv(
                env.values.global,
                &env.values.transparent,
                env.depth(),
                ty_exp,
                &ty_got,
            ) {
                Ok(_) => Ok(()),
                Err(_) => Err(Error::BadCheck {
                    tm: Syntax::data_constructor_rc(dc.constructor, dc.arguments.clone()),
                    ty_exp: Rc::new(ty_exp.clone()),
                    ty_got,
                }),
            }
        }
        _ => Err(Error::BadCtor {
            tm: Syntax::data_constructor_rc(dc.constructor, dc.arguments.clone()),
            ty_exp: Rc::new(ty_exp.clone()),
        }),
    }
}

// ============================================================================
// HardwareUniverse Type Checking
// ============================================================================

/// Synthesize the type of a lifted hardware type (^ht).
fn type_synth_lift<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    lift: &syn::Lift<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    // Check that the inner term is a valid hardware type
    check_hwtype(env, &lift.ty)?;

    // ^ht : Type (at universe level 0)
    Ok(Value::universe_rc(crate::common::UniverseLevel::new(0)))
}

fn type_check_bit<'db, 'g>(
    _env: &mut TCEnvironment<'db, 'g>,
    ty: &Value<'db>,
) -> Result<(), Error<'db>> {
    match ty {
        Value::SignalUniverse(_) => Ok(()),
        _ => Err(Error::BadCtor {
            tm: Syntax::bit_rc(),
            ty_exp: Rc::new(ty.clone()),
        }),
    }
}

fn type_check_harrow<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    harrow: &syn::HArrow<'db>,
    ty: &Value<'db>,
) -> Result<(), Error<'db>> {
    match ty {
        Value::ModuleUniverse(_) => {
            // Check that source and target are hardware types
            check_hwtype(env, &harrow.source)?;
            check_hwtype(env, &harrow.target)?;
            Ok(())
        }
        _ => Err(Error::BadCtor {
            tm: Syntax::harrow_rc(harrow.source.clone(), harrow.target.clone()),
            ty_exp: Rc::new(ty.clone()),
        }),
    }
}

/// Check that SLift (Sig) is valid against the expected type.
/// SLift wraps a signal type to make a hardware type: Sig s : HType where s : SType
fn type_check_slift<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    slift: &syn::SLift<'db>,
    ty: &Value<'db>,
) -> Result<(), Error<'db>> {
    match ty {
        Value::HardwareUniverse(_) => {
            // The inner type must be a valid signal type
            check_signal_type(env, &slift.ty)
        }
        _ => Err(Error::BadCtor {
            tm: Syntax::slift_rc(slift.ty.clone()),
            ty_exp: Rc::new(ty.clone()),
        }),
    }
}

/// Check that MLift (Mod) is valid against the expected type.
/// MLift wraps a module type to make a hardware type: Mod m : HType where m : MType
fn type_check_mlift<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    mlift: &syn::MLift<'db>,
    ty: &Value<'db>,
) -> Result<(), Error<'db>> {
    match ty {
        Value::HardwareUniverse(_) => {
            // The inner type must be a valid module type
            check_module_type(env, &mlift.ty)
        }
        _ => Err(Error::BadCtor {
            tm: Syntax::mlift_rc(mlift.ty.clone()),
            ty_exp: Rc::new(ty.clone()),
        }),
    }
}

/// Check that `0` (Zero) is valid against the expected type.
/// Zero values can be checked against ^(Sig Bit) (a Lift containing an SLift of Bit).
fn type_check_zero<'db, 'g>(
    _env: &mut TCEnvironment<'db, 'g>,
    _zero: &syn::Zero<'db>,
    ty: &Value<'db>,
) -> Result<(), Error<'db>> {
    // The expected type must be ^(Sig Bit), which is Lift(SLift(Bit))
    match ty {
        Value::Lift(lift) => match lift.ty.as_ref() {
            Value::SLift(slift) => match slift.ty.as_ref() {
                Value::Bit(_) => Ok(()),
                _ => Err(Error::BadCtor {
                    tm: Syntax::zero_rc(),
                    ty_exp: Rc::new(ty.clone()),
                }),
            },
            _ => Err(Error::BadCtor {
                tm: Syntax::zero_rc(),
                ty_exp: Rc::new(ty.clone()),
            }),
        },
        _ => Err(Error::BadCtor {
            tm: Syntax::zero_rc(),
            ty_exp: Rc::new(ty.clone()),
        }),
    }
}

/// Check that `1` (One) is valid against the expected type.
/// One values can be checked against ^(Sig Bit) (a Lift containing an SLift of Bit).
fn type_check_one<'db, 'g>(
    _env: &mut TCEnvironment<'db, 'g>,
    _one: &syn::One<'db>,
    ty: &Value<'db>,
) -> Result<(), Error<'db>> {
    // The expected type must be ^(Sig Bit), which is Lift(SLift(Bit))
    match ty {
        Value::Lift(lift) => match lift.ty.as_ref() {
            Value::SLift(slift) => match slift.ty.as_ref() {
                Value::Bit(_) => Ok(()),
                _ => Err(Error::BadCtor {
                    tm: Syntax::one_rc(),
                    ty_exp: Rc::new(ty.clone()),
                }),
            },
            _ => Err(Error::BadCtor {
                tm: Syntax::one_rc(),
                ty_exp: Rc::new(ty.clone()),
            }),
        },
        _ => Err(Error::BadCtor {
            tm: Syntax::one_rc(),
            ty_exp: Rc::new(ty.clone()),
        }),
    }
}

/// Check that a term is a valid hardware type (has type HType).
/// Hardware types are:
/// - SLift(s) where s : SType (signal types wrapped to hardware)
/// - MLift(m) where m : MType (module types wrapped to hardware)
/// - neutrals that have type HardwareUniverse
fn check_hwtype<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
) -> Result<(), Error<'db>> {
    match term {
        // SLift wraps a signal type to make a hardware type: Sig s : HType where s : SType
        Syntax::SLift(slift) => check_signal_type(env, &slift.ty),
        // MLift wraps a module type to make a hardware type: Mod m : HType where m : MType
        Syntax::MLift(mlift) => check_module_type(env, &mlift.ty),
        // Variables and other neutrals - synthesize and check for HardwareUniverse
        _ => {
            let ty = type_synth(env, term)?;
            match &*ty {
                Value::HardwareUniverse(_) => Ok(()),
                _ => Err(Error::BadType {
                    tm: Rc::new(term.clone()),
                }),
            }
        }
    }
}

/// Check that a term is a valid signal type (has type SType).
/// Signal types are: Bit, or neutrals that have type SignalUniverse.
fn check_signal_type<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
) -> Result<(), Error<'db>> {
    match term {
        Syntax::Bit(_) => Ok(()),
        _ => {
            let ty = type_synth(env, term)?;
            match &*ty {
                Value::SignalUniverse(_) => Ok(()),
                _ => Err(Error::BadType {
                    tm: Rc::new(term.clone()),
                }),
            }
        }
    }
}

/// Check that a term is a valid module type (has type MType).
/// Module types are: HArrow, or neutrals that have type ModuleUniverse.
fn check_module_type<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
) -> Result<(), Error<'db>> {
    match term {
        Syntax::HArrow(harrow) => {
            // HArrow components must be hardware types
            check_hwtype(env, &harrow.source)?;
            check_hwtype(env, &harrow.target)
        }
        _ => {
            let ty = type_synth(env, term)?;
            match &*ty {
                Value::ModuleUniverse(_) => Ok(()),
                _ => Err(Error::BadType {
                    tm: Rc::new(term.clone()),
                }),
            }
        }
    }
}

fn type_check_eq<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    eq: &syn::EqType<'db>,
    ty: &Value<'db>,
) -> Result<(), Error<'db>> {
    let Value::Universe(_) = ty else {
        return Err(Error::BadCtor {
            tm: Syntax::eq_rc(eq.ty.clone(), eq.lhs.clone(), eq.rhs.clone()),
            ty_exp: Rc::new(ty.clone()),
        });
    };

    check_type(env, &eq.ty)?;
    let sem_ty = eval(env, &eq.ty)?;
    type_check(env, &eq.lhs, &sem_ty)?;
    type_check(env, &eq.rhs, &sem_ty)?;

    Ok(())
}

fn type_synth_eq<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    eq: &syn::EqType<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    check_type(env, &eq.ty)?;
    let ty_ty = type_synth(env, &eq.ty)?;

    let Value::Universe(universe) = ty_ty.as_ref() else {
        return Err(Error::BadCtor {
            tm: Syntax::eq_rc(eq.ty.clone(), eq.lhs.clone(), eq.rhs.clone()),
            ty_exp: ty_ty,
        });
    };

    let sem_ty = eval(env, &eq.ty)?;
    type_check(env, &eq.lhs, &sem_ty)?;
    type_check(env, &eq.rhs, &sem_ty)?;

    Ok(Value::universe_rc(universe.level))
}

fn type_check_refl<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
    ty: &Value<'db>,
) -> Result<(), Error<'db>> {
    let Value::EqType(eq_ty) = ty else {
        return Err(Error::BadCtor {
            tm: Rc::new(term.clone()),
            ty_exp: Rc::new(ty.clone()),
        });
    };

    equal::equate(
        env.values.global,
        &env.values.transparent,
        env.depth(),
        &eq_ty.lhs,
        &eq_ty.rhs,
        &eq_ty.ty,
    )
    .map_err(|_| Error::BadCtor {
        tm: Rc::new(term.clone()),
        ty_exp: Rc::new(ty.clone()),
    })
}

fn type_synth_transport<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    transport: &syn::Transport<'db>,
) -> Result<RcValue<'db>, Error<'db>> {
    let proof_ty = type_synth(env, &transport.proof)?;
    let Value::EqType(eq_ty) = &*proof_ty else {
        return Err(Error::BadSynth {
            tm: Syntax::transport_rc(
                transport.motive.clone(),
                transport.proof.clone(),
                transport.value.clone(),
            ),
        });
    };

    // The motive should be a function that takes a value of type eq_ty.ty and returns a type
    // Check: Γ ⊢ motive : A → Type
    //
    // According to the design notes, we need to:
    // 1. Check that M has type A → Type
    // 2. Compute M a (motive applied to lhs)
    // 3. Check that x : M a
    // 4. Return M b as the synthesized type
    //
    // To check M : A → Type, we need to construct the Pi type (A → Type).
    // The codomain should be Type (a universe), but which universe?
    // We need to infer it from the equality type's universe level.

    // Construct the expected type for the motive: A → Type
    // For now, we use U0 as the codomain. In a more sophisticated system,
    // we would infer the universe level from the type of A.
    // Since A : U_i for some i, the motive should have type A → U_i.
    // For simplicity, we use U0 here.
    let universe_syntax = Syntax::universe_rc(UniverseLevel::new(0));
    let constant_closure = val::Closure::new(LocalEnv::new(), universe_syntax);
    let motive_expected_ty = Value::pi_rc(eq_ty.ty.clone(), constant_closure);

    // Check the motive against this type
    type_check(env, &transport.motive, &motive_expected_ty)?;

    // Evaluate the motive to get a closure we can apply
    let motive_val = eval(env, &transport.motive)?;
    let Value::Lambda(lambda) = &*motive_val else {
        return Err(Error::BadSynth {
            tm: transport.motive.clone(),
        });
    };

    // Apply the motive to the lhs to get the type of the value
    let p_of_x = run_closure(env, &lambda.body, [eq_ty.lhs.clone()])?;

    type_check(env, &transport.value, &p_of_x)?;

    // Apply the motive to the rhs to get the result type
    let p_of_y = run_closure(env, &lambda.body, [eq_ty.rhs.clone()])?;

    Ok(p_of_y)
}

// The syn::Closure type has been removed. This function is no longer needed.
// Arity is now stored directly in DynBinding structures.

// Synthesize a type for the term, then check for equality against the expected type.
pub fn type_check_synth_term<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
    ty1: &Value<'db>,
) -> Result<(), Error<'db>> {
    let ty2 = type_synth(env, term)?;
    match crate::equal::type_equiv(
        env.values.global,
        &env.values.transparent,
        env.depth(),
        ty1,
        &ty2,
    ) {
        Ok(()) => Ok(()),
        Err(_) => Err(Error::BadCheck {
            tm: Rc::new(term.clone()),
            ty_got: ty2,
            ty_exp: Rc::new(ty1.clone()),
        }),
    }
}

/// Check that the given term is a valid meta-level type (in Universe, not the
/// hardware universe Type).
/// This is used for Check nodes where hardware types like $Bit are not allowed.
/// Use check_type for contexts where hardware types are also valid.
fn check_meta_type<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
) -> Result<(), Error<'db>> {
    // HardwareUniverse types (Bit, HArrow, HardwareUniverse) are NOT valid meta-level types
    if matches!(
        term,
        Syntax::Bit(_) | Syntax::HArrow(_) | Syntax::HardwareUniverse(_)
    ) {
        return Err(Error::BadType {
            tm: Rc::new(term.clone()),
        });
    }

    // Pi types are valid if source and target are valid meta-level types
    if let Syntax::Pi(pi) = term {
        return check_meta_pi_type(env, pi);
    }

    if let Syntax::TypeConstructor(tc) = term {
        return check_type_constructor_type(env, tc);
    }

    // Lifted hardware types are valid meta-level types (^$Bit is in Universe)
    if let Syntax::Lift(lift) = term {
        return check_hwtype(env, &lift.ty);
    }

    // Otherwise, synthesize a type for the term, which must be a Universe (not Type)
    let ty = type_synth(env, term)?;
    if let Value::Universe(_) = &*ty {
        return Ok(());
    }

    // Type means this is a hardware type, not a meta-level type
    if let Value::HardwareUniverse(_) = &*ty {
        return Err(Error::BadType {
            tm: Rc::new(term.clone()),
        });
    }

    // Otherwise return failure: this is not a type.
    Err(Error::BadType {
        tm: Rc::new(term.clone()),
    })
}

/// Check that a pi is a valid meta-level type.
fn check_meta_pi_type<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    pi: &stx::Pi<'db>,
) -> Result<(), Error<'db>> {
    // First check that the source-type of the pi is a valid meta-level type.
    check_meta_type(env, &pi.source)?;

    // Evaluate the source-type.
    let ty = eval(env, &pi.source)?;

    // Check the codomain under an environment extended with one additional
    // variable, of the domain type, representing the pi binder.
    env.push_var(ty);
    let result = check_meta_type(env, &pi.target);
    env.pop();
    result
}

/// Check that the given term is a valid type.
/// This includes both meta-level types (in Universe) and hardware types (in Type).
pub fn check_type<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
) -> Result<(), Error<'db>> {
    // If the term is a pi, then we just check that it is valid.
    if let Syntax::Pi(pi) = term {
        return check_pi_type(env, pi);
    }

    if let Syntax::TypeConstructor(tc) = term {
        return check_type_constructor_type(env, tc);
    }

    // Lifted hardware types are valid types
    if let Syntax::Lift(lift) = term {
        return check_hwtype(env, &lift.ty);
    }

    // The hardware universe HardwareUniverse (whose semantic value is `Type`) is a
    // valid type for classifying hardware types.
    if let Syntax::HardwareUniverse(_) = term {
        return Ok(());
    }

    // Signal types (Bit) are valid types - they live in SType
    if let Syntax::Bit(_) = term {
        return check_signal_type(env, term);
    }

    // Module types (HArrow) are valid types - they live in MType
    if let Syntax::HArrow(harrow) = term {
        return check_module_type(env, term);
    }

    // SLift/MLift (hardware types) are valid types - they live in HType
    if matches!(term, Syntax::SLift(_) | Syntax::MLift(_)) {
        return check_hwtype(env, term);
    }

    // Equality types are valid types - they live in universes
    if let Syntax::Eq(eq) = term {
        return check_eq_type(env, eq);
    }

    // Otherwise, synthesize a type for the term, which must be a universe.
    let ty = type_synth(env, term)?;
    if let Value::Universe(_) = &*ty {
        return Ok(());
    }

    // Otherwise return failure: this is not a type.
    Err(Error::BadType {
        tm: Rc::new(term.clone()),
    })
}

fn check_eq_type<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    eq: &stx::EqType<'db>,
) -> Result<(), Error<'db>> {
    check_type(env, &eq.ty)?;
    let sem_ty = eval(env, &eq.ty)?;
    type_check(env, &eq.lhs, &sem_ty)?;
    type_check(env, &eq.rhs, &sem_ty)?;
    Ok(())
}

/// Check that a pi is a valid type.
fn check_pi_type<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    pi: &stx::Pi<'db>,
) -> Result<(), Error<'db>> {
    // First check that the source-type of the pi is a type.
    check_type(env, &pi.source)?;

    // Evaluate the source-type.
    let ty = eval(env, &pi.source)?;

    // Check the codomain under an environment extended with one additional
    // variable, of the domain type, representing the pi binder.
    env.push_var(ty);
    let result = check_type(env, &pi.target);
    env.pop();
    result
}

fn check_type_constructor_type<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    tcon: &stx::TypeConstructor<'db>,
) -> Result<(), Error<'db>> {
    // Lookup the type constructor info.
    let tcon_info = env
        .values
        .global
        .type_constructor(tcon.constructor)
        .map_err(Error::LookupError)?;

    // Check that the number of arguments matches the number of parameters.
    if tcon.arguments.len() != tcon_info.arguments.len() {
        return Err(Error::BadType {
            tm: Syntax::type_constructor_rc(tcon.constructor, tcon.arguments.clone()),
        });
    }

    let mut ty_env = val::Environment {
        global: env.values.global,
        local: val::LocalEnv::new(),
        transparent: val::TransparentEnv::new(),
    };

    for (arg, arg_ty) in tcon.arguments.iter().zip(&tcon_info.arguments) {
        let sem_arg_ty = eval::eval(&mut ty_env, arg_ty)?;
        type_check(env, arg, &sem_arg_ty)?;
        let sem_arg = eval::eval(&mut env.values, arg)?;
        ty_env.push(sem_arg);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{Index, UniverseLevel};
    use crate::syn::parse::parse_syntax;
    use crate::syn::RcSyntax;

    use crate::val::Closure;
    use crate::Database;
    use crate::QualifiedName;
    use hwml_support::{FromWithDb, IntoWithDb};

    // ========== Prelude definitions ==========

    use crate::test_utils::{eval_str, load_prelude, NAT_PRELUDE, VEC_PRELUDE};

    /// Create a GlobalEnv with Nat type defined.
    fn make_nat_global<'db>(db: &'db Database) -> val::GlobalEnv<'db> {
        load_prelude(db, NAT_PRELUDE)
    }

    /// Create a GlobalEnv with Nat and Vec types defined.
    fn make_vec_global<'db>(db: &'db Database) -> val::GlobalEnv<'db> {
        load_prelude(db, VEC_PRELUDE)
    }

    /// Helper to create a TCEnvironment with a GlobalEnv
    fn make_env<'db, 'g>(
        db: &'db dyn salsa::Database,
        global: &'g val::GlobalEnv<'db>,
    ) -> TCEnvironment<'db, 'g> {
        TCEnvironment {
            db,
            values: val::Environment::new(global),
            types: Vec::new(),
        }
    }

    /// Parse helper - panics with message on failure
    fn parse<'db>(db: &'db Database, input: &'db str) -> RcSyntax<'db> {
        parse_syntax(db, input).unwrap_or_else(|e| panic!("Failed to parse '{}': {:?}", input, e))
    }

    // ========== check_meta_type tests ==========

    /// Test that Lift types are valid meta-level types.
    #[test]
    fn test_lift_is_valid_meta_type() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // ^(^s Bit) - a lifted hardware type (Lift containing SLift containing Bit)
        let lift_bit = parse(&db, "^(^s Bit)");
        assert!(check_meta_type(&mut env, &lift_bit).is_ok());
    }

    /// Test that hardware types (Bit) are NOT valid meta-level types.
    #[test]
    fn test_hwtype_is_not_valid_meta_type() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // Bit - a hardware type
        let bit = parse(&db, "Bit");
        assert!(check_meta_type(&mut env, &bit).is_err());
    }

    /// Test that Universe is a valid meta-level type.
    #[test]
    fn test_universe_is_valid_meta_type() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // 𝒰0 should be accepted
        let u0 = parse(&db, "U0");
        assert!(check_meta_type(&mut env, &u0).is_ok());
    }

    /// Test that Pi types with valid meta-level source/target are valid.
    #[test]
    fn test_pi_is_valid_meta_type() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // ∀ (%x : 𝒰0) → 𝒰0
        let pi = parse(&db, "forall (%x : U0) -> U0");
        assert!(check_meta_type(&mut env, &pi).is_ok());
    }

    // ========== check_type tests ==========

    /// Test that check_type accepts Universe.
    #[test]
    fn test_check_type_accepts_universe() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        let u0 = parse(&db, "U0");
        assert!(check_type(&mut env, &u0).is_ok());
    }

    /// Test that check_type accepts Pi types.
    #[test]
    fn test_check_type_accepts_pi() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        let pi = parse(&db, "forall (%x : U0) -> U0");
        assert!(check_type(&mut env, &pi).is_ok());
    }

    /// Test that check_type accepts Bit (signal type - lives in SignalUniverse).
    #[test]
    fn test_check_type_accepts_bit() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // Bit is a signal type (SType), so it's a valid type
        let bit = parse(&db, "Bit");
        assert!(check_type(&mut env, &bit).is_ok());
    }

    /// Test that check_type accepts HArrow (module type).
    #[test]
    fn test_check_type_accepts_harrow() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // ^s Bit -> ^s Bit : MType (module type with hardware type components)
        let harrow = parse(&db, "^s Bit -> ^s Bit");
        assert!(check_type(&mut env, &harrow).is_ok());
    }

    /// Test that check_type accepts Lift types.
    #[test]
    fn test_check_type_accepts_lift() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // ^(^s Bit) : Type (lifted hardware type)
        let lift = parse(&db, "^(^s Bit)");
        assert!(check_type(&mut env, &lift).is_ok());
    }

    // ========== type_synth tests ==========

    /// Test that Universe synthesizes to a higher universe.
    #[test]
    fn test_synth_universe() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        let u0 = parse(&db, "U0");
        let ty = type_synth(&mut env, &u0).expect("should synthesize");

        // 𝒰0 : 𝒰1
        match &*ty {
            Value::Universe(u) => assert_eq!(u.level, UniverseLevel::new(1)),
            _ => panic!("Expected Universe, got {:?}", ty),
        }
    }

    /// Test that Lift synthesizes to Universe(0).
    #[test]
    fn test_synth_lift() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // ^(^s Bit) : 𝒰0 - Lift of SLift of Bit
        let lift = parse(&db, "^(^s Bit)");
        let ty = type_synth(&mut env, &lift).expect("should synthesize");

        match &*ty {
            Value::Universe(u) => assert_eq!(u.level, UniverseLevel::new(0)),
            _ => panic!("Expected Universe, got {:?}", ty),
        }
    }

    /// Test that variables get their type from the environment.
    #[test]
    fn test_synth_variable() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // Push a variable of type 𝒰0
        let u0_val = Value::universe_rc(UniverseLevel::new(0));
        env.push_var(u0_val.clone());

        // Variable %0 should have type 𝒰0
        // Parse at depth 1 since we have one variable in scope
        let var = crate::syn::parse::parse_syntax_at_depth(&db, "%0", 1).expect("should parse");
        let ty = type_synth(&mut env, &var).expect("should synthesize");

        match &*ty {
            Value::Universe(u) => assert_eq!(u.level, UniverseLevel::new(0)),
            _ => panic!("Expected Universe, got {:?}", ty),
        }
    }

    /// Test that constants get their type from the global environment.
    #[test]
    fn test_synth_constant() {
        let db = Database::new();
        let mut global = val::GlobalEnv::new();

        let cid = |s: &str| QualifiedName::from_with_db(&db, s);

        // Add constant @myConst : 𝒰0 = 𝒰0
        global.add_constant(
            cid("myConst"),
            val::ConstantInfo::new(parse(&db, "U0"), parse(&db, "U0")),
        );

        let mut env = make_env(&db, &global);

        // @myConst should have type 𝒰0
        let const_syn = parse(&db, "@myConst");
        let ty = type_synth(&mut env, &const_syn).expect("should synthesize");

        match &*ty {
            Value::Universe(u) => assert_eq!(u.level, UniverseLevel::new(0)),
            _ => panic!("Expected Universe, got {:?}", ty),
        }
    }

    /// Test that primitives get their type from the global environment.
    #[test]
    fn test_synth_primitive() {
        let db = Database::new();
        let mut global = val::GlobalEnv::new();

        let cid = |s: &str| QualifiedName::from_with_db(&db, s);

        // Add primitive $Nat : 𝒰0
        global.add_primitive(cid("Nat"), val::PrimitiveInfo::new(parse(&db, "U0")));

        let mut env = make_env(&db, &global);

        // $Nat should have type 𝒰0
        let prim_syn = parse(&db, "$Nat");
        let ty = type_synth(&mut env, &prim_syn).expect("should synthesize");

        match &*ty {
            Value::Universe(u) => assert_eq!(u.level, UniverseLevel::new(0)),
            _ => panic!("Expected Universe, got {:?}", ty),
        }
    }

    // ========== type_check tests ==========

    /// Test that Pi types check against Universe.
    #[test]
    fn test_check_pi_against_universe() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // ∀ (%x : 𝒰0) → 𝒰0 has type 𝒰1 (not 𝒰0)
        let pi = parse(&db, "forall (%x : U0) -> U0");

        let u1_val = Value::universe(UniverseLevel::new(1));
        assert!(type_check(&mut env, &pi, &u1_val).is_ok());
    }

    /// Test that Lambda checks against Pi type.
    #[test]
    fn test_check_lambda_against_pi() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // λ %x → %x : ∀ (%x : 𝒰0) → 𝒰0
        let lam = parse(&db, "λ %x -> %x");

        // Create the Pi type as a Value
        let u0_val = Value::universe_rc(UniverseLevel::new(0));
        let u0_syn = parse(&db, "U0");
        let pi_val = Value::Pi(val::Pi {
            source: u0_val.clone(),
            target: Closure::new(val::LocalEnv::new(), u0_syn),
        });

        assert!(type_check(&mut env, &lam, &pi_val).is_ok());
    }

    /// Test that Bit checks against SignalUniverse.
    #[test]
    fn test_check_bit_against_signal_universe() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        let bit = parse(&db, "Bit");
        let signal_universe = Value::SignalUniverse(val::SignalUniverse::new());

        assert!(type_check(&mut env, &bit, &signal_universe).is_ok());
    }

    /// Test that HArrow checks against ModuleUniverse.
    #[test]
    fn test_check_harrow_against_module_universe() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // ^s Bit -> ^s Bit : MType (HArrow with hardware type components)
        let harrow = parse(&db, "^s Bit -> ^s Bit");
        let module_universe = Value::ModuleUniverse(val::ModuleUniverse::new());

        assert!(type_check(&mut env, &harrow, &module_universe).is_ok());
    }

    // ========== Application synthesis tests ==========

    /// Test that function application synthesizes the correct type.
    #[test]
    fn test_synth_application() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // Set up: we need a variable of Pi type
        // Create a function f : ∀ (%x : 𝒰0) → 𝒰0
        let u0_val = Value::universe_rc(UniverseLevel::new(0));
        let u0_syn = parse(&db, "U0");
        let pi_val = Value::pi_rc(u0_val.clone(), Closure::new(val::LocalEnv::new(), u0_syn));

        // Push f into the environment
        env.push_var(pi_val);

        // Now apply f to (^(^s Bit)) which has type 𝒰0
        // Parse at depth 1 since we have one variable (f) in scope
        let app =
            crate::syn::parse::parse_syntax_at_depth(&db, "%0 ^(^s Bit)", 1).expect("should parse");

        let ty = type_synth(&mut env, &app).expect("should synthesize");

        // The result should be 𝒰0
        match &*ty {
            Value::Universe(u) => assert_eq!(u.level, UniverseLevel::new(0)),
            _ => panic!("Expected Universe, got {:?}", ty),
        }
    }

    // ========== Metavariable type synthesis tests ==========

    /// Test that metavariables without arguments synthesize to their declared type.
    #[test]
    fn test_synth_metavariable_no_args() {
        use crate::common::MetaVariableId;

        let db = Database::default();
        let mut global = val::GlobalEnv::new();

        // Declare ?[0] : U0
        let meta_id = MetaVariableId::new(0);
        global.add_metavariable(meta_id, vec![], Syntax::universe_rc(UniverseLevel::new(0)));

        let mut env = make_env(&db, &global);

        // ?[0] should synthesize to U0
        let meta_stx = Syntax::metavariable(meta_id, vec![]);
        let ty = type_synth(&mut env, &meta_stx).expect("should synthesize");

        match &*ty {
            Value::Universe(u) => assert_eq!(u.level, UniverseLevel::new(0)),
            _ => panic!("Expected Universe, got {:?}", ty),
        }
    }

    /// Test that metavariables with arguments synthesize with substitution applied.
    #[test]
    fn test_synth_metavariable_with_args() {
        use crate::common::MetaVariableId;

        let db = Database::default();
        let mut global = val::GlobalEnv::new();

        // Declare ?[0] (%x : U0) : U0
        let meta_id = MetaVariableId::new(0);
        global.add_metavariable(
            meta_id,
            vec![Syntax::universe_rc(UniverseLevel::new(0))],
            Syntax::universe_rc(UniverseLevel::new(0)),
        );

        let mut env = make_env(&db, &global);

        // ?[0 ^(^s Bit)] should synthesize to U0
        let lift_bit = parse(&db, "^(^s Bit)");
        let meta_stx = Syntax::metavariable(meta_id, vec![lift_bit]);
        let ty = type_synth(&mut env, &meta_stx).expect("should synthesize");

        match &*ty {
            Value::Universe(u) => assert_eq!(u.level, UniverseLevel::new(0)),
            _ => panic!("Expected Universe, got {:?}", ty),
        }
    }

    /// Test that metavariable with wrong number of arguments fails.
    #[test]
    fn test_synth_metavariable_wrong_arg_count() {
        use crate::common::MetaVariableId;

        let db = Database::default();
        let mut global = val::GlobalEnv::new();

        // Declare ?[0] (%x : U0) : U0 (expects 1 argument)
        let meta_id = MetaVariableId::new(0);
        global.add_metavariable(
            meta_id,
            vec![Syntax::universe_rc(UniverseLevel::new(0))],
            Syntax::universe_rc(UniverseLevel::new(0)),
        );

        let mut env = make_env(&db, &global);

        // ?[0] with no arguments should fail
        let meta_stx = Syntax::metavariable(meta_id, vec![]);
        assert!(type_synth(&mut env, &meta_stx).is_err());
    }

    /// Test that metavariable with wrong argument type fails.
    #[test]
    fn test_synth_metavariable_wrong_arg_type() {
        use crate::common::MetaVariableId;

        let db = Database::default();
        let mut global = val::GlobalEnv::new();

        // Declare ?[0] (%x : ^Bit) : U0 (expects lifted bit type)
        let meta_id = MetaVariableId::new(0);
        global.add_metavariable(
            meta_id,
            vec![Syntax::lift_rc(Syntax::bit_rc())],
            Syntax::universe_rc(UniverseLevel::new(0)),
        );

        let mut env = make_env(&db, &global);

        // ?[0 U0] with universe instead of ^Bit should fail
        let u0 = parse(&db, "U0");
        let meta_stx = Syntax::metavariable(meta_id, vec![u0]);
        assert!(type_synth(&mut env, &meta_stx).is_err());
    }

    /// Test that dependent metavariables synthesize correctly.
    #[test]
    fn test_synth_metavariable_dependent() {
        use crate::common::MetaVariableId;

        let db = Database::default();
        let mut global = val::GlobalEnv::new();

        // Declare ?[0] (%A : U0) (%x : %A) : U0
        // The second argument type depends on the first argument
        let meta_id = MetaVariableId::new(0);
        global.add_metavariable(
            meta_id,
            vec![
                Syntax::universe_rc(UniverseLevel::new(0)), // %A : U0
                Syntax::variable_rc(Index(0)),              // %x : %A (references %A)
            ],
            Syntax::universe_rc(UniverseLevel::new(0)),
        );

        let mut env = make_env(&db, &global);

        // ?[0 ^(^s Bit) (0 : ^(^s Bit))] - provide ^(^s Bit) for A, and a bit value 0 for x
        let lift_bit = parse(&db, "^(^s Bit)");
        let zero = Syntax::check_rc(lift_bit.clone(), Syntax::zero_rc());
        let meta_stx = Syntax::metavariable(meta_id, vec![lift_bit, zero]);
        let ty = type_synth(&mut env, &meta_stx).expect("should synthesize");

        match &*ty {
            Value::Universe(u) => assert_eq!(u.level, UniverseLevel::new(0)),
            _ => panic!("Expected Universe, got {:?}", ty),
        }
    }

    // ========== apply_subst tests ==========

    /// Test that apply_subst correctly turns a variable into a transparent let-binding.
    /// Context: [n : Nat]
    /// Substitution: n ~ @Zero
    /// Expected: values.local[0] becomes @Zero
    #[test]
    fn test_apply_subst_simple() {
        let db = Database::default();
        let global = make_nat_global(&db);

        let mut env = make_env(&db, &global);

        // Push n : Nat
        let nat = Value::type_constructor("Nat".into_with_db(&db), vec![]);
        env.push_var(Rc::new(nat));

        // Now values.local[0] is a Rigid (variable n)
        assert!(matches!(
            env.values.get(Level::new(0)).as_ref(),
            Value::Rigid(_)
        ));

        // Apply substitution: n ~ @Zero
        let zero = Value::data_constructor_rc("Zero".into_with_db(&db), vec![]);
        let solutions = vec![(Level::new(0), zero.clone())];
        env.apply_subst(&solutions)
            .expect("apply_subst should succeed");

        // Now values.local[0] should be @Zero (transparent let-binding)
        match env.values.get(Level::new(0)).as_ref() {
            Value::DataConstructor(dcon) => {
                assert_eq!(dcon.constructor.name(&db).to_string(&db), "Zero");
            }
            other => panic!("Expected DataConstructor(@Zero), got {:?}", other),
        }
    }

    /// Test that apply_subst correctly re-evaluates dependent types.
    /// Context: [n : Nat, v : Vec Bit n]
    /// Substitution: n ~ @Zero
    /// Expected: types[1] (the type of v) becomes Vec Bit @Zero
    #[test]
    fn test_apply_subst_dependent_type() {
        let db = Database::default();
        let global = make_vec_global(&db);

        let mut env = make_env(&db, &global);

        // Push n : Nat at level 0
        let nat_ty = Value::type_constructor_rc("Nat".into_with_db(&db), vec![]);
        let n = env.push_var(nat_ty);

        // Push v : Vec Bit n at level 1
        // Vec Bit n = #[@Vec Bit n]
        let bit_ty = Value::bit_rc();
        let vec_bit_n =
            Value::type_constructor_rc("Vec".into_with_db(&db), vec![bit_ty.clone(), n.clone()]);
        env.push_var(vec_bit_n);

        // Verify initial state: types[1] contains Vec Bit n (with Rigid at index 0)
        match env.types[1].as_ref() {
            Value::TypeConstructor(tcon) => {
                assert_eq!(tcon.constructor.name(&db).to_string(&db), "Vec");
                assert_eq!(tcon.arguments.len(), 2);
                // Second argument should be a Rigid (variable n at level 0)
                match tcon.arguments[1].as_ref() {
                    Value::Rigid(r) => assert_eq!(r.head.level, Level::new(0)),
                    other => panic!("Expected Rigid, got {:?}", other),
                }
            }
            other => panic!("Expected TypeConstructor(Vec), got {:?}", other),
        }

        // Apply substitution: n ~ @Zero
        let zero = Value::data_constructor_rc("Zero".into_with_db(&db), vec![]);
        let solutions = vec![(Level::new(0), zero.clone())];
        env.apply_subst(&solutions)
            .expect("apply_subst should succeed");

        // Now types[1] should be Vec Bit @Zero
        match env.types[1].as_ref() {
            Value::TypeConstructor(tcon) => {
                assert_eq!(tcon.constructor.name(&db).to_string(&db), "Vec");
                assert_eq!(tcon.arguments.len(), 2);
                // Second argument should now be @Zero
                match tcon.arguments[1].as_ref() {
                    Value::DataConstructor(dcon) => {
                        assert_eq!(dcon.constructor.name(&db).to_string(&db), "Zero");
                    }
                    other => panic!("Expected DataConstructor(@Zero), got {:?}", other),
                }
            }
            other => panic!("Expected TypeConstructor(Vec), got {:?}", other),
        }
    }

    /// Test that apply_subst handles multiple solutions correctly.
    /// Context: [n : Nat, m : Nat, v : Vec Bit n, w : Vec Bit m]
    /// Substitution: n ~ @Zero, m ~ @Succ @Zero
    /// Expected: types[2] becomes Vec Bit @Zero, types[3] becomes Vec Bit (@Succ @Zero)
    #[test]
    fn test_apply_subst_multiple_solutions() {
        let db = Database::default();
        let global = make_vec_global(&db);

        let mut env = make_env(&db, &global);
        let bit_ty = Value::bit_rc();

        // Push n : Nat at level 0
        let nat_ty = Value::type_constructor_rc("Nat".into_with_db(&db), vec![]);
        let n = env.push_var(nat_ty.clone());

        // Push m : Nat at level 1
        let m = env.push_var(nat_ty);

        // Push v : Vec Bit n at level 2
        let vec_bit_n =
            Value::type_constructor_rc("Vec".into_with_db(&db), vec![bit_ty.clone(), n.clone()]);
        env.push_var(vec_bit_n);

        // Push w : Vec Bit m at level 3
        let vec_bit_m =
            Value::type_constructor_rc("Vec".into_with_db(&db), vec![bit_ty.clone(), m.clone()]);
        env.push_var(vec_bit_m);

        // Apply substitutions: n ~ @Zero, m ~ @Succ @Zero
        let zero = Value::data_constructor_rc("Zero".into_with_db(&db), vec![]);
        let succ_zero = Value::data_constructor_rc("Succ".into_with_db(&db), vec![zero.clone()]);
        let solutions = vec![
            (Level::new(0), zero.clone()),
            (Level::new(1), succ_zero.clone()),
        ];
        env.apply_subst(&solutions)
            .expect("apply_subst should succeed");

        // Check types[2]: Vec Bit @Zero
        match env.types[2].as_ref() {
            Value::TypeConstructor(tcon) => match tcon.arguments[1].as_ref() {
                Value::DataConstructor(dcon) => {
                    assert_eq!(dcon.constructor.name(&db).to_string(&db), "Zero");
                }
                other => panic!("Expected @Zero, got {:?}", other),
            },
            other => panic!("Expected Vec, got {:?}", other),
        }

        // Check types[3]: Vec Bit (@Succ @Zero)
        match env.types[3].as_ref() {
            Value::TypeConstructor(tcon) => match tcon.arguments[1].as_ref() {
                Value::DataConstructor(dcon) => {
                    assert_eq!(dcon.constructor.name(&db).to_string(&db), "Succ");
                    assert_eq!(dcon.arguments.len(), 1);
                    match dcon.arguments[0].as_ref() {
                        Value::DataConstructor(inner) => {
                            assert_eq!(inner.constructor.name(&db).to_string(&db), "Zero");
                        }
                        other => panic!("Expected @Zero, got {:?}", other),
                    }
                }
                other => panic!("Expected @Succ, got {:?}", other),
            },
            other => panic!("Expected Vec, got {:?}", other),
        }
    }

    /// Test the "Quote Depth" fix for deeply nested dependent types.
    /// This test verifies that each type is quoted at its historical depth.
    ///
    /// Context: [n : Nat, m : Nat, p : Nat, v : Vec Bit n, w : Vec Bit m, x : Vec Bit p]
    /// Where each Vec depends on a different preceding Nat.
    ///
    /// Substitution: n ~ @Zero, m ~ @Succ @Zero, p ~ @Succ (@Succ @Zero)
    ///
    /// After substitution:
    /// - types[3] (Vec Bit n) should become Vec Bit @Zero
    /// - types[4] (Vec Bit m) should become Vec Bit (@Succ @Zero)
    /// - types[5] (Vec Bit p) should become Vec Bit (@Succ (@Succ @Zero))
    ///
    /// The bug we're testing for: if we quote all types at depth 6 (the final env size),
    /// the De Bruijn indices would be wrong because the type at level 3 was originally
    /// checked when only levels 0-2 were in scope.
    #[test]
    fn test_apply_subst_quote_depth_correctness() {
        let db = Database::default();
        let global = make_vec_global(&db);

        let mut env = make_env(&db, &global);
        let bit_ty = Value::bit_rc();
        let nat_ty = Value::type_constructor_rc("Nat".into_with_db(&db), vec![]);

        // Push n : Nat at level 0
        let n = env.push_var(nat_ty.clone());
        // Push m : Nat at level 1
        let m = env.push_var(nat_ty.clone());
        // Push p : Nat at level 2
        let p = env.push_var(nat_ty);

        // Push v : Vec Bit n at level 3
        let vec_bit_n =
            Value::type_constructor_rc("Vec".into_with_db(&db), vec![bit_ty.clone(), n.clone()]);
        env.push_var(vec_bit_n);

        // Push w : Vec Bit m at level 4
        let vec_bit_m =
            Value::type_constructor_rc("Vec".into_with_db(&db), vec![bit_ty.clone(), m.clone()]);
        env.push_var(vec_bit_m);

        // Push x : Vec Bit p at level 5
        let vec_bit_p =
            Value::type_constructor_rc("Vec".into_with_db(&db), vec![bit_ty.clone(), p.clone()]);
        env.push_var(vec_bit_p);

        // Apply substitutions
        let zero = Value::data_constructor_rc("Zero".into_with_db(&db), vec![]);
        let one = Value::data_constructor_rc("Succ".into_with_db(&db), vec![zero.clone()]);
        let two = Value::data_constructor_rc("Succ".into_with_db(&db), vec![one.clone()]);
        let solutions = vec![
            (Level::new(0), zero.clone()),
            (Level::new(1), one.clone()),
            (Level::new(2), two.clone()),
        ];
        env.apply_subst(&solutions)
            .expect("apply_subst should succeed");

        // Verify types[3]: Vec Bit @Zero
        match env.types[3].as_ref() {
            Value::TypeConstructor(tcon) => {
                assert_eq!(tcon.constructor.name(&db).to_string(&db), "Vec");
                match tcon.arguments[1].as_ref() {
                    Value::DataConstructor(dcon) => {
                        assert_eq!(dcon.constructor.name(&db).to_string(&db), "Zero");
                    }
                    other => panic!("types[3] index: Expected @Zero, got {:?}", other),
                }
            }
            other => panic!("types[3]: Expected Vec, got {:?}", other),
        }

        // Verify types[4]: Vec Bit (@Succ @Zero)
        match env.types[4].as_ref() {
            Value::TypeConstructor(tcon) => {
                assert_eq!(tcon.constructor.name(&db).to_string(&db), "Vec");
                match tcon.arguments[1].as_ref() {
                    Value::DataConstructor(dcon) => {
                        assert_eq!(dcon.constructor.name(&db).to_string(&db), "Succ");
                        match dcon.arguments[0].as_ref() {
                            Value::DataConstructor(inner) => {
                                assert_eq!(inner.constructor.name(&db).to_string(&db), "Zero");
                            }
                            other => panic!("types[4] inner: Expected @Zero, got {:?}", other),
                        }
                    }
                    other => panic!("types[4] index: Expected @Succ, got {:?}", other),
                }
            }
            other => panic!("types[4]: Expected Vec, got {:?}", other),
        }

        // Verify types[5]: Vec Bit (@Succ (@Succ @Zero))
        match env.types[5].as_ref() {
            Value::TypeConstructor(tcon) => {
                assert_eq!(tcon.constructor.name(&db).to_string(&db), "Vec");
                match tcon.arguments[1].as_ref() {
                    Value::DataConstructor(outer) => {
                        assert_eq!(outer.constructor.name(&db).to_string(&db), "Succ");
                        match outer.arguments[0].as_ref() {
                            Value::DataConstructor(middle) => {
                                assert_eq!(middle.constructor.name(&db).to_string(&db), "Succ");
                                match middle.arguments[0].as_ref() {
                                    Value::DataConstructor(inner) => {
                                        assert_eq!(
                                            inner.constructor.name(&db).to_string(&db),
                                            "Zero"
                                        );
                                    }
                                    other => {
                                        panic!("types[5] inner: Expected @Zero, got {:?}", other)
                                    }
                                }
                            }
                            other => panic!("types[5] middle: Expected @Succ, got {:?}", other),
                        }
                    }
                    other => panic!("types[5] index: Expected @Succ, got {:?}", other),
                }
            }
            other => panic!("types[5]: Expected Vec, got {:?}", other),
        }
    }

    // ========== Coverage Checking tests ==========

    /// Test that exhaustive pattern matching on Nat succeeds.
    /// n : Nat |- n case @Zero => @Zero, @Succ %m => @Zero : Nat
    #[test]
    fn test_exhaustive_nat_case() {
        let db = Database::default();
        let global = make_nat_global(&db);
        let mut env = make_env(&db, &global);

        // Push n : Nat
        let nat = Value::type_constructor_rc("Nat".into_with_db(&db), vec![]);
        env.push_var(nat.clone());

        // Parse case: !0 case { @Zero => [@Zero] | @Succ %m => [@Zero] }
        // !0 refers to the variable at index 0 (the most recent variable, n)
        let case_stx = parse(&db, "!0 case { @Zero => [@Zero] | @Succ %m => [@Zero] }");
        let Syntax::Case(case) = case_stx.as_ref() else {
            panic!("Expected Case syntax");
        };

        // Check the case against type Nat
        let result = type_check_case(&mut env, case, &nat);
        assert!(
            result.is_ok(),
            "Exhaustive case should succeed: {:?}",
            result
        );
    }

    /// Test that missing a constructor results in NonExhaustiveMatch error.
    /// n : Nat |- n case @Zero => @Zero : Nat  (missing @Succ)
    #[test]
    fn test_non_exhaustive_nat_case_missing_succ() {
        let db = Database::default();
        let global = make_nat_global(&db);
        let mut env = make_env(&db, &global);

        // Push n : Nat
        let nat = Value::type_constructor_rc("Nat".into_with_db(&db), vec![]);
        env.push_var(nat.clone());

        // Parse case: !0 case { @Zero => [@Zero] }  (missing @Succ)
        // !0 refers to the variable at index 0 (the most recent variable, n)
        let case_stx = parse(&db, "!0 case { @Zero => [@Zero] }");
        let Syntax::Case(case) = case_stx.as_ref() else {
            panic!("Expected Case syntax");
        };

        // Check should fail with NonExhaustiveMatch
        let result = type_check_case(&mut env, case, &nat);
        match result {
            Err(ref e @ Error::NonExhaustiveMatch { ref missing, .. }) => {
                // Verify human-readable output
                let display_output = format!("{}", e);
                println!("Display output: {}", display_output);
                assert!(
                    display_output.contains("@Succ"),
                    "Expected '@Succ' in display, got: {}",
                    display_output
                );
                assert_eq!(missing.len(), 1);
                assert_eq!(missing[0], "Succ");
            }
            other => panic!("Expected NonExhaustiveMatch, got {:?}", other),
        }
    }

    /// Test that a case on Vec at index @Zero only requires @VNil.
    /// a : Type, v : Vec a @Zero |- v case @VNil => @Zero : Nat
    /// (@VCons is impossible because the index is @Zero)
    #[test]
    fn test_vec_at_zero_only_requires_vnil() {
        let db = Database::default();
        let global = make_vec_global(&db);
        let mut env = make_env(&db, &global);

        // Push a : Type at level 0
        let universe = Value::universe_rc(UniverseLevel::new(0));
        env.push_var(universe.clone());
        let a = Value::variable_rc(Level::new(0), universe.clone());

        // Push v : Vec a @Zero at level 1
        let zero = Value::data_constructor_rc("Zero".into_with_db(&db), vec![]);
        let vec_a_zero =
            Value::type_constructor_rc("Vec".into_with_db(&db), vec![a.clone(), zero.clone()]);
        env.push_var(vec_a_zero.clone());

        // Parse case: !0 case { @VNil => [@Zero] }
        // !0 refers to the variable at index 0 (the most recent variable, v)
        // This should be exhaustive because @VCons is impossible at index @Zero
        let case_stx = parse(&db, "!0 case { @VNil => [@Zero] }");
        let Syntax::Case(case) = case_stx.as_ref() else {
            panic!("Expected Case syntax");
        };

        // Check should succeed - @VCons is unreachable, only @VNil is required
        let nat = Value::type_constructor_rc("Nat".into_with_db(&db), vec![]);
        let result = type_check_case(&mut env, case, &nat);
        assert!(
            result.is_ok(),
            "Vec@Zero case with only VNil should be exhaustive: {:?}",
            result
        );
    }

    /// Test that a case on Vec at variable index requires both @VNil and @VCons.
    /// a : Type, n : Nat, v : Vec a n |- v case @VNil => ... (missing @VCons)
    #[test]
    fn test_vec_at_variable_requires_both_constructors() {
        let db = Database::default();
        let global = make_vec_global(&db);
        let mut env = make_env(&db, &global);

        // Push a : Type at level 0
        let universe = Value::universe_rc(UniverseLevel::new(0));
        env.push_var(universe.clone());
        let a = Value::variable_rc(Level::new(0), universe.clone());

        // Push n : Nat at level 1
        let nat = Value::type_constructor_rc("Nat".into_with_db(&db), vec![]);
        env.push_var(nat.clone());
        let n = Value::variable_rc(Level::new(1), nat.clone());

        // Push v : Vec a n at level 2
        let vec_a_n =
            Value::type_constructor_rc("Vec".into_with_db(&db), vec![a.clone(), n.clone()]);
        env.push_var(vec_a_n.clone());

        // Parse case: !0 case { @VNil => [@Zero] }  (missing @VCons)
        // !0 refers to the variable at index 0 (the most recent variable, v)
        let case_stx = parse(&db, "!0 case { @VNil => [@Zero] }");
        let Syntax::Case(case) = case_stx.as_ref() else {
            panic!("Expected Case syntax");
        };

        // Check should fail - both @VNil and @VCons are required when index is a variable
        let result = type_check_case(&mut env, case, &nat);
        match result {
            Err(Error::NonExhaustiveMatch { missing, .. }) => {
                assert_eq!(missing.len(), 1);
                assert_eq!(missing[0], "VCons");
            }
            other => panic!("Expected NonExhaustiveMatch, got {:?}", other),
        }
    }

    // ========== Equality type checking tests ==========

    #[test]
    fn test_check_eq_type() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // Eq U0 U0 U0 : U1
        let eq = parse(&db, "Eq U1 U0 U0");
        let u1 = Value::universe(UniverseLevel::new(1));
        let result = type_check(&mut env, &eq, &u1);
        assert!(result.is_ok(), "type_check failed: {:?}", result.err());
    }

    #[test]
    fn test_check_refl() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // refl : Eq U0 U0 U0
        let refl = parse(&db, "refl");
        let eq_ty = eval_str(&db, &global, "Eq U0 U0 U0");
        let result = type_check(&mut env, &refl, &eq_ty);
        assert!(result.is_ok(), "type_check failed: {:?}", result.err());
    }

    #[test]
    fn test_check_refl_fails_on_different_endpoints() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // refl : Eq U0 U0 U1 should fail (endpoints don't match)
        let refl = parse(&db, "refl");
        let eq_ty = eval_str(&db, &global, "Eq U0 U0 U1");
        assert!(type_check(&mut env, &refl, &eq_ty).is_err());
    }

    #[test]
    fn test_check_transport() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // Test: transport along an equality of types
        // Context: [A : U0, B : U0, h : Eq U0 A B, x : A]
        // Term: transport [%0 -> %0] %h %x : B
        // The motive [%0 -> %0] is the identity function on types
        // This transports a value x : A to a value of type B

        let u0 = Value::universe_rc(UniverseLevel::new(0));

        // Push A : U0
        let a = env.push_var(u0.clone());

        // Push B : U0
        let b = env.push_var(u0.clone());

        // Push h : Eq U0 A B
        let eq_ty = Value::eq_rc(u0.clone(), a.clone(), b.clone());
        env.push_var(eq_ty);

        // Push x : A
        env.push_var(a.clone());

        // Construct: transport %0 to (λ %y → %y) by %1
        // Parse at depth 4 since we have 4 variables in scope (A, B, h, x)
        // %0 = x (index 0), %1 = h (index 1), %2 = B (index 2), %3 = A (index 3)
        // The motive (λ %y → %y) is the identity function on types
        let transport =
            crate::syn::parse::parse_syntax_at_depth(&db, "transport %0 to λ %y → %y by %1", 4)
                .expect("should parse");

        // Synthesize the type - should be B
        let result = type_synth(&mut env, &transport);
        assert!(result.is_ok(), "type_synth failed: {:?}", result.err());

        let synth_ty = result.unwrap();
        // The synthesized type should be equal to B
        assert!(
            equal::type_equiv(&global, &env.values.transparent, env.depth(), &synth_ty, &b).is_ok(),
            "Expected type B, got {:?}",
            synth_ty
        );
    }

    #[test]
    fn test_dependent_pattern_matching_with_equality() {
        // This test demonstrates how dependent pattern matching on equality proofs
        // enables type refinement using the transport primitive.
        //
        // Example: A function that takes a vector of length (n + n) and an equality
        // proof that (n + n) = m, and returns a vector of length m.
        //
        // In a real implementation with pattern matching, matching on the equality
        // proof (which must be `refl`) would allow the type checker to unify
        // (n + n) with m, enabling the type refinement.
        //
        // Since we don't have full pattern matching in the core, we demonstrate
        // the underlying mechanism: using transport to cast from Vec A (n + n)
        // to Vec A m given a proof that (n + n) = m.

        let db = Database::default();
        let mut global = val::GlobalEnv::new();

        // First, set up the type environment with Nat and Vec
        // For this test, we'll use primitives to represent these types

        // Register Nat : U0
        let nat_id = "Nat".into_with_db(&db);
        global.add_type_constructor(
            nat_id,
            val::TypeConstructorInfo::new(vec![], 0, UniverseLevel::new(0)),
        );

        // Register Vec : (A : U0) -> Nat -> U0
        // Vec has one parameter (A : U0) and one index (n : Nat)
        let vec_id = "Vec".into_with_db(&db);
        let u0_syn = Syntax::universe_rc(UniverseLevel::new(0));
        let nat_syn = Syntax::type_constructor_rc(nat_id, vec![]);
        global.add_type_constructor(
            vec_id,
            val::TypeConstructorInfo::new(
                vec![u0_syn.clone(), nat_syn.clone()],
                1, // One parameter (A), one index (n)
                UniverseLevel::new(0),
            ),
        );

        let mut env = make_env(&db, &global);
        let u0 = Value::universe_rc(UniverseLevel::new(0));
        let nat_val = Value::type_constructor_rc(nat_id, vec![]);

        // Context:
        // A : U0
        // n : Nat
        // m : Nat
        // eq_proof : Eq Nat n m
        // v : Vec A n

        // Push A : U0
        let a = env.push_var(u0.clone());

        // Push n : Nat
        let n = env.push_var(nat_val.clone());

        // Push m : Nat
        let m = env.push_var(nat_val.clone());

        // Push eq_proof : Eq Nat n m
        let eq_ty = Value::eq_rc(nat_val.clone(), n.clone(), m.clone());
        env.push_var(eq_ty);

        // Push v : Vec A n
        let vec_a_n = Value::type_constructor_rc(vec_id, vec![a.clone(), n.clone()]);
        env.push_var(vec_a_n.clone());

        // Now we want to construct a term of type Vec A m
        // We use transport with a motive that maps a Nat to Vec A (that Nat)
        //
        // transport v to (λ i → Vec A i) by eq_proof : Vec A m
        //
        // At depth 5: %0 = v, %1 = eq_proof, %2 = m, %3 = n, %4 = A

        let transport_term = crate::syn::parse::parse_syntax_at_depth(
            &db,
            "transport %0 to λ %i → #[@Vec %4 %i] by %1",
            5,
        )
        .expect("should parse");

        // Type check: should synthesize Vec A m
        let result = type_synth(&mut env, &transport_term);
        assert!(result.is_ok(), "type_synth failed: {:?}", result.err());

        let synth_ty = result.unwrap();

        // The synthesized type should be Vec A m
        let expected_ty = Value::type_constructor_rc(vec_id, vec![a.clone(), m.clone()]);

        assert!(
            equal::type_equiv(
                &global,
                &env.values.transparent,
                env.depth(),
                &synth_ty,
                &expected_ty
            )
            .is_ok(),
            "Expected type Vec A m, got {:?}",
            synth_ty
        );

        // This demonstrates that transport successfully performs the type refinement
        // that would occur when pattern matching on an equality proof!
    }

    // ========== Let expression tests ==========

    #[test]
    fn test_let_simple_synth() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // let %x : U0 = U0; %x
        // Should synthesize to U1 (since U0 : U1)
        let let_expr = parse(&db, "let %x : U1 = U0; %x");
        let result = type_synth(&mut env, &let_expr);
        assert!(result.is_ok(), "type_synth failed: {:?}", result.err());

        let synth_ty = result.unwrap();
        match synth_ty.as_ref() {
            Value::Universe(u) => assert_eq!(u.level, UniverseLevel::new(1)),
            other => panic!("Expected Universe(1), got {:?}", other),
        }
    }

    #[test]
    fn test_let_simple_check() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // let %x : U0 = U0; %x : U1
        let let_expr = parse(&db, "let %x : U1 = U0; %x");
        let u1 = Value::universe(UniverseLevel::new(1));
        let result = type_check(&mut env, &let_expr, &u1);
        assert!(result.is_ok(), "type_check failed: {:?}", result.err());
    }

    #[test]
    fn test_let_body_uses_binding() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // let %A : U1 = U0; %A
        // The body references the let-bound variable
        let let_expr = parse(&db, "let %A : U1 = U0; %A");
        let result = type_synth(&mut env, &let_expr);
        assert!(result.is_ok(), "type_synth failed: {:?}", result.err());

        let synth_ty = result.unwrap();
        match synth_ty.as_ref() {
            Value::Universe(u) => assert_eq!(u.level, UniverseLevel::new(1)),
            other => panic!("Expected Universe(1), got {:?}", other),
        }
    }

    #[test]
    fn test_let_nested() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // let %A : U1 = U0; let %B : U1 = %A; %B
        let let_expr = parse(&db, "let %A : U1 = U0; let %B : U1 = %A; %B");
        let result = type_synth(&mut env, &let_expr);
        assert!(result.is_ok(), "type_synth failed: {:?}", result.err());

        let synth_ty = result.unwrap();
        match synth_ty.as_ref() {
            Value::Universe(u) => assert_eq!(u.level, UniverseLevel::new(1)),
            other => panic!("Expected Universe(1), got {:?}", other),
        }
    }

    #[test]
    fn test_let_delta_reduction_in_equality() {
        // CRITICAL TEST: This is the test case from the design document
        // let y = U0; let h : Eq U1 U0 y = refl;
        // This tests that δ-reduction works correctly in conversion checking
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // let %y : U1 = U0; let %h : Eq U1 U0 %y = refl; %h
        // This should typecheck because y unfolds to U0 via δ-reduction
        let let_expr = parse(&db, "let %y : U1 = U0; let %h : Eq U1 U0 %y = refl; %h");
        let result = type_synth(&mut env, &let_expr);
        assert!(
            result.is_ok(),
            "δ-reduction test failed: {:?}",
            result.err()
        );

        // The type should be Eq U1 U0 U0 after δ-reduction
        let synth_ty = result.unwrap();
        match synth_ty.as_ref() {
            Value::EqType(_) => {
                // Success! The equality type was synthesized correctly
            }
            other => panic!("Expected EqType, got {:?}", other),
        }
    }

    #[test]
    fn test_let_with_universe_values() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // let %T : U1 = U0; let %x : U1 = %T; %x
        // Chain of let bindings with universe values
        let let_expr = parse(&db, "let %T : U1 = U0; let %x : U1 = %T; %x");
        let result = type_synth(&mut env, &let_expr);
        assert!(result.is_ok(), "type_synth failed: {:?}", result.err());

        let synth_ty = result.unwrap();
        match synth_ty.as_ref() {
            Value::Universe(u) => assert_eq!(u.level, UniverseLevel::new(1)),
            other => panic!("Expected Universe(1), got {:?}", other),
        }
    }

    #[test]
    fn test_let_type_annotation_checked() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // let %x : Bit = U0; %x
        // This should fail because U0 is not a Bit
        let let_expr = parse(&db, "let %x : Bit = U0; %x");
        let result = type_synth(&mut env, &let_expr);
        assert!(result.is_err(), "Expected type error, but got success");
    }

    #[test]
    fn test_let_in_lambda_with_pi_type() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // λ %A → let %B : U0 = %A; %B
        // Let can appear in lambda bodies, and we check against a Pi type
        let lam_expr = parse(&db, "λ %A → let %B : U0 = %A; %B");
        let u0 = Value::universe_rc(UniverseLevel::new(0));
        let u0_closure = val::Closure::new(
            val::LocalEnv::new(),
            Syntax::universe_rc(UniverseLevel::new(0)),
        );
        let pi_ty = Value::pi_rc(u0, u0_closure);
        let result = type_check(&mut env, &lam_expr, &pi_ty);
        assert!(result.is_ok(), "type_check failed: {:?}", result.err());
    }

    #[test]
    fn test_let_in_lambda_body() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // λ %x → let %y : U0 = %x; %y
        // Let can appear in lambda bodies
        let lam_expr = parse(&db, "λ %x → let %y : U0 = %x; %y");
        let u0 = Value::universe_rc(UniverseLevel::new(0));
        let u0_closure = val::Closure::new(
            val::LocalEnv::new(),
            Syntax::universe_rc(UniverseLevel::new(0)),
        );
        let pi_ty = Value::pi_rc(u0.clone(), u0_closure);
        let result = type_check(&mut env, &lam_expr, &pi_ty);
        assert!(result.is_ok(), "type_check failed: {:?}", result.err());
    }

    // ========== Universe Level Checking Tests ==========

    #[test]
    fn test_pi_universe_max_rule() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // ∀ (%x : U0) → U0 should have type U1 (max(0, 0) = 0, so Pi : U1)
        let pi_expr = Syntax::pi_rc(
            Syntax::universe_rc(UniverseLevel::new(0)),
            Binding::new(Syntax::universe_rc(UniverseLevel::new(0))),
        );
        let u1 = Value::universe_rc(UniverseLevel::new(1));
        let result = type_check(&mut env, &pi_expr, &u1);
        assert!(result.is_ok(), "Pi (U0 -> U0) should be in U1");

        // ∀ (%x : U0) → U1 should have type U2 (max(0, 1) = 1, so Pi : U2)
        let pi_expr = Syntax::pi_rc(
            Syntax::universe_rc(UniverseLevel::new(0)),
            Binding::new(Syntax::universe_rc(UniverseLevel::new(1))),
        );
        let u2 = Value::universe_rc(UniverseLevel::new(2));
        let result = type_check(&mut env, &pi_expr, &u2);
        assert!(result.is_ok(), "Pi (U0 -> U1) should be in U2");

        // ∀ (%x : U1) → U0 should have type U2 (max(1, 0) = 1, so Pi : U2)
        let pi_expr = Syntax::pi_rc(
            Syntax::universe_rc(UniverseLevel::new(1)),
            Binding::new(Syntax::universe_rc(UniverseLevel::new(0))),
        );
        let u2 = Value::universe_rc(UniverseLevel::new(2));
        let result = type_check(&mut env, &pi_expr, &u2);
        assert!(result.is_ok(), "Pi (U1 -> U0) should be in U2");
    }

    #[test]
    fn test_pi_universe_cumulativity() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // ∀ (%x : U0) → U0 can be checked against U2 (cumulativity: U1 <= U2)
        let pi_expr = Syntax::pi_rc(
            Syntax::universe_rc(UniverseLevel::new(0)),
            Binding::new(Syntax::universe_rc(UniverseLevel::new(0))),
        );
        let u2 = Value::universe_rc(UniverseLevel::new(2));
        let result = type_check(&mut env, &pi_expr, &u2);
        assert!(
            result.is_ok(),
            "Pi (U0 -> U0) should be checkable against U2 (cumulativity)"
        );
    }

    #[test]
    fn test_pi_universe_level_too_low_fails() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // ∀ (%x : U0) → U1 should NOT be checkable against U1
        // (max(0, 1) = 1, so Pi : U2, but we're checking against U1)
        let pi_expr = Syntax::pi_rc(
            Syntax::universe_rc(UniverseLevel::new(0)),
            Binding::new(Syntax::universe_rc(UniverseLevel::new(1))),
        );
        let u1 = Value::universe_rc(UniverseLevel::new(1));
        let result = type_check(&mut env, &pi_expr, &u1);
        assert!(
            result.is_err(),
            "Pi (U0 -> U1) should NOT be in U1 (needs U2)"
        );
    }

    #[test]
    fn test_universe_synthesis_increments() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&db, &global);

        // U0 : U1
        let u0 = Syntax::universe_rc(UniverseLevel::new(0));
        let ty = type_synth(&mut env, &u0).expect("should synthesize");
        match &*ty {
            Value::Universe(u) => assert_eq!(u.level, UniverseLevel::new(1)),
            _ => panic!("Expected Universe, got {:?}", ty),
        }

        // U5 : U6
        let u5 = Syntax::universe_rc(UniverseLevel::new(5));
        let ty = type_synth(&mut env, &u5).expect("should synthesize");
        match &*ty {
            Value::Universe(u) => assert_eq!(u.level, UniverseLevel::new(6)),
            _ => panic!("Expected Universe, got {:?}", ty),
        }
    }
}
