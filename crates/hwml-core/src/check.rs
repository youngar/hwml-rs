use crate::equal;
use crate::eval;
use crate::pattern_unify;
use crate::quote;
use crate::syn as stx;
use crate::syn;
use crate::val;
use val::{Environment, LocalEnv};
use crate::Binding;
use crate::Level;
use crate::Syntax;
use crate::*;
use crate::{RcValue, Value};
use salsa::Database;
use std::collections::HashSet;
use std::rc::Rc;

#[derive(Clone)]
pub struct TCEnvironment<'db, 'g> {
    pub db: &'db dyn Database,
    pub values: val::Environment<'db, 'g>,
    /// Type classifiers for bound variables in the context.
    pub types: Vec<val::RcTy<'db>>,
}

impl<'db, 'g> TCEnvironment<'db, 'g> {
    fn global_env(&self) -> &'g val::GlobalEnv<'db> {
        self.values.global
    }

    fn local_env(&self) -> &val::LocalEnv<'db> {
        &self.values.local
    }

    fn context(&self) -> &Vec<val::RcTy<'db>> {
        &self.types
    }

    pub fn type_of(&self, level: Level) -> &val::RcTy<'db> {
        let index: usize = level.into();
        &self.types[index]
    }

    fn var_type(&self, var: &stx::Variable) -> &val::RcTy<'db> {
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

    fn push(&mut self, value: RcValue<'db>, ty: val::RcTy<'db>) {
        self.values.push(value);
        self.types.push(ty);
    }

    pub fn push_var(&mut self, ty: val::RcTy<'db>) -> RcValue<'db> {
        let var = Value::variable_rc(Level::new(self.depth()), ty.clone());
        self.push(var.clone(), ty);
        var
    }

    fn push_transparent(&mut self, ty: val::RcTy<'db>, value: RcValue<'db>) {
        self.values.push_transparent(ty.clone(), value);
        self.types.push(ty);
    }

    pub fn pop(&mut self) {
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

    pub fn under_binder<F, R>(&mut self, ty: val::RcTy<'db>, f: F) -> Binding<'db, R>
    where
        F: FnOnce(&mut Self) -> R,
    {
        let depth = self.depth();
        self.push_var(ty);
        let body = f(self);
        self.truncate(depth);
        Binding::new(Name::anonymous(self.db), body)
    }

    #[allow(dead_code)]
    fn extend_vars<T>(&mut self, types: T)
    where
        T: IntoIterator<Item = val::RcTy<'db>>,
    {
        for ty in types {
            self.push_var(ty);
        }
    }

    pub fn quote_at_depth(
        &self,
        tm: &RcValue<'db>,
        ty: &RcValue<'db>,
        depth: usize,
    ) -> RcSyntax<'db> {
        quote::quote(self.db, self.global_env(), depth, tm, ty).unwrap()
    }

    pub fn quote(&self, tm: &RcValue<'db>, ty: &RcValue<'db>) -> RcSyntax<'db> {
        self.quote_at_depth(tm, ty, self.depth())
    }

    pub fn quote_bound(&self, bound: Binding<&RcValue<'db>>, ty: &RcValue<'db>) -> RcSyntax<'db> {
        self.quote_at_depth(bound.term(), ty, self.depth() + 1)
    }

    /// Build a syntactic substitution from this local environment.
    pub fn syn_substitution(&self) -> Vec<RcSyntax<'db>> {
        let mut substitution: Vec<RcSyntax<'db>> = Vec::new();
        for (tm, ty) in self.local_env().iter().zip(self.context()) {
            // We need to convert val::Ty to Value for quoting
            // **PHASE 9**: After deleting Ty::El, encode types back to codes
            let ty_code = match crate::quote::encode_type(self.db, self.values.global, self.depth(), ty) {
                Ok(code) => code,
                Err(_) => Rc::new(Value::UniverseCode(0)), // Fallback for quote errors
            };
            substitution.push(self.quote(tm, &ty_code));
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
            // Quote the semantic type back to syntax
            let quoted_ty_syn = quote::quote_ty(self.db, self.values.global, k, &self.types[k])?;
            let mut historical_env = self.values.clone();
            historical_env.truncate(k);
            // Re-evaluate the type syntax to get updated semantic type
            let new_ty = crate::eval::eval_ty(&mut historical_env, &quoted_ty_syn)?;
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
        ty_got: val::RcTy<'db>,
    },
    /// Bad constructor.
    BadCtor {
        tm: RcSyntax<'db>,
        ty_exp: val::RcTy<'db>,
    },
    /// Inferred a type that did not match the expected type.
    BadCheck {
        tm: RcSyntax<'db>,
        ty_exp: val::RcTy<'db>,
        ty_got: val::RcTy<'db>,
    },
    EvaluationFailure(eval::Error<'db>),
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

impl<'db> From<eval::Error<'db>> for Error<'db> {
    fn from(e: eval::Error<'db>) -> Self {
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
            Error::PatternUnifyStuck { tm: _, meta_id } => {
                write!(
                    f,
                    "pattern match blocked on unsolved metavariable ?{}\n\
                     help: add a type annotation to resolve the ambiguity",
                    meta_id.local_index
                )
            }
            Error::NonExhaustiveMatch { tm: _, missing } => {
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
/// Synthesize the type of a term.
pub fn type_synth<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
) -> Result<val::RcTy<'db>, Error<'db>> {
    match term {
        Syntax::Variable(variable) => type_synth_variable(env, variable),
        Syntax::Constant(constant) => type_synth_constant(env, constant),
        Syntax::Prim(prim) => type_synth_prim(env, prim),
        Syntax::Check(check) => type_synth_check(env, check),
        Syntax::Let(let_expr) => type_synth_let(env, let_expr),
        Syntax::Application(application) => type_synth_application(env, application),
        Syntax::Metavariable(metavariable) => type_synth_metavariable(env, metavariable),

        // Eq type can synthesize: Eq A x y : U_i if A : U_i
        Syntax::Eq(eq) => type_synth_eq(env, eq),

        // Transport is an eliminator and synthesizes its type
        Syntax::Transport(transport) => type_synth_transport(env, transport),

        // ========== STRICT TARSKI: TYPE CODES ARE CHECK-ONLY ==========
        // Type codes (UniverseCode, PiCode, BitCode) can ONLY be checked against
        // a universe classifier. They cannot synthesize types.
        // This enforces the dogmatic separation: codes are terms, types are classifiers.
        Syntax::UniverseCode(_) | Syntax::PiCode(_, _, _) | Syntax::BitCode => {
            Err(Error::BadSynth {
                tm: Rc::new(term.clone()),
            })
        }

        _ => Err(Error::BadSynth {
            tm: Rc::new(term.clone()),
        }),
    }
}

/// Synthesize a type for a variable.
pub fn type_synth_variable<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    variable: &syn::Variable<'db>,
) -> Result<val::RcTy<'db>, Error<'db>> {
    // Pull the type from the typing environment.
    Ok(env.var_type(variable).clone())
}

pub fn type_synth_constant<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    constant: &syn::Constant<'db>,
) -> Result<val::RcTy<'db>, Error<'db>> {
    let constant_info = env
        .values
        .global
        .constant(constant.name)
        .map_err(Error::LookupError)?;
    // Evaluate and decode the type
    let type_code = eval(env, &constant_info.ty)?;
    crate::eval::decode_type_code(env.values.global, &type_code).map_err(Error::EvaluationFailure)
}

/// Synthesize the type of a primitive by looking it up in the global environment.
/// Primitives have types but no definitions.
pub fn type_synth_prim<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    prim: &syn::Prim<'db>,
) -> Result<val::RcTy<'db>, Error<'db>> {
    // Look up the primitive in the global environment
    let prim_info = env
        .values
        .global
        .primitive(prim.name)
        .map_err(Error::LookupError)?;

    // Evaluate and decode the type
    let type_code = eval(env, &prim_info.ty)?;
    crate::eval::decode_type_code(env.values.global, &type_code).map_err(Error::EvaluationFailure)
}

/// Validate that a syntactic type is well-formed.
///
/// This function ensures that a `syn::Ty` represents a valid type by checking:
/// - Universe types are always valid
/// - Pi types have well-formed domains and codomains
/// - HArrow types have well-formed source and target
/// - El nodes cross the Tarski bridge: the code must have type UniverseType
/// - SignalEl nodes: the code must have type SignalUniverseType
/// - ModuleEl nodes: the code must have type ModuleUniverseType
pub fn check_ty<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    ty: &syn::Ty<'db>,
) -> Result<(), Error<'db>> {
    use syn::Ty;
    match ty {
        // Universe types are always valid
        Ty::UniverseType | Ty::SignalUniverseType | Ty::ModuleUniverseType => Ok(()),

        // Pi type: check domain is well-formed, extend context, check codomain
        Ty::Pi(source, target) => {
            check_ty(env, source)?;
            let source_val_ty = crate::eval::eval_ty(&mut env.values, source)?;
            env.push_var(source_val_ty);
            let result = check_ty(env, target.term());
            env.pop();
            result
        }

        // HArrow: check both sides are well-formed
        Ty::HArrow(source, target) => {
            check_ty(env, source)?;
            check_ty(env, target)
        }

        // TyConstructorTy: check all type arguments are well-formed
        // **Phase 0**: For now, just check each argument is a valid type
        // Full checking against the type constructor's telescope comes in Phase 2
        Ty::TyConstructorTy(_name, args) => {
            for arg in args {
                check_ty(env, arg)?;
            }
            Ok(())
        }

        // El: Cross the Tarski bridge - check that code has type UniverseType or El(UniverseCode(_))
        Ty::El(code) => {
            // The code should be a term that has a type El(UniverseCode(_)) or UniverseType
            // With check-only type codes, codes like Check(UniverseCode(0), UniverseType) synthesize UniverseType
            let code_ty = type_synth(env, code)?;
            match code_ty.as_ref() {
                // Accept UniverseType (from Check nodes like (U0 : UniverseType))
                val::Ty::UniverseType => Ok(()),
                // **PHASE 9**: After Strong Tarski, expect decoded Universe types
                val::Ty::Universe(_) => Ok(()),
                _ => Err(Error::BadType { tm: code.clone() }),
            }
        }

        // SignalEl: Check that code has type SignalUniverseType
        Ty::SignalEl(code) => {
            let code_ty = type_synth(env, code)?;
            match code_ty.as_ref() {
                val::Ty::SignalUniverseType => Ok(()),
                _ => Err(Error::BadType { tm: code.clone() }),
            }
        }

        // ModuleEl: Check that code has type ModuleUniverseType
        Ty::ModuleEl(code) => {
            let code_ty = type_synth(env, code)?;
            match code_ty.as_ref() {
                val::Ty::ModuleUniverseType => Ok(()),
                _ => Err(Error::BadType { tm: code.clone() }),
            }
        }
    }
}

/// Synthesize the type of a term annotated with a type.
/// This is the clean Tarski implementation - no hacks!
pub fn type_synth_check<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    check: &syn::Check<'db>,
) -> Result<val::RcTy<'db>, Error<'db>> {
    // 1. Validate the type annotation is well-formed
    check_ty(env, &check.ty)?;

    // 2. Evaluate the syntactic type into a semantic type
    let expected_ty = crate::eval::eval_ty(&mut env.values, &check.ty)?;

    // 3. Check the term against the semantic type
    type_check(env, &check.term, &expected_ty)?;

    // 4. Return the semantic type
    Ok(expected_ty)
}

pub fn type_synth_let<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    let_expr: &syn::Let<'db>,
) -> Result<val::RcTy<'db>, Error<'db>> {
    // The type annotation is now a syntactic TYPE (syn::RcTy), not a term!
    // This enforces the Tarski separation.

    // 1. Validate the type annotation is well-formed
    check_ty(env, &let_expr.ty)?;

    // 2. Evaluate the syntactic type into a semantic type
    let sem_ty = crate::eval::eval_ty(&mut env.values, &let_expr.ty)?;

    // 3. Check the value against the type
    type_check(env, &let_expr.value, &sem_ty)?;

    // Evaluate the value
    let sem_value = eval(env, &let_expr.value)?;

    // Push as transparent binding and synthesize body type
    env.push_transparent(sem_ty, sem_value);
    let body_ty = type_synth(env, &let_expr.body.term())?;
    env.pop();

    Ok(body_ty)
}

/// Synthesize the type of a metavariable.
pub fn type_synth_metavariable<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    metavariable: &syn::Metavariable<'db>,
) -> Result<val::RcTy<'db>, Error<'db>> {
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
    for (arg, arg_ty_binder) in metavariable
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
        let expected_ty_code =
            eval::eval(&mut temp_env, &arg_ty_binder.ty).map_err(|_| Error::BadSynth {
                tm: Syntax::metavariable_rc(metavariable.id, metavariable.substitution.clone()),
            })?;
        let expected_ty = crate::eval::decode_type_code(env.values.global, &expected_ty_code)
            .map_err(|_| Error::BadSynth {
                tm: Syntax::metavariable_rc(metavariable.id, metavariable.substitution.clone()),
            })?;

        // Check the argument against the expected type.
        type_check(env, arg, &expected_ty)?;

        // Evaluate the argument and add it to the local environment.
        let arg_val = eval(env, arg)?;
        local_env.push(arg_val);
    }

    // Evaluate the final type code in the extended local environment.
    let mut temp_env = Environment {
        global: env.values.global,
        local: local_env,
        transparent: val::TransparentEnv::new(),
    };
    let meta_ty_code = eval::eval(&mut temp_env, &meta_info.ty).map_err(|_| Error::BadSynth {
        tm: Syntax::metavariable_rc(metavariable.id, metavariable.substitution.clone()),
    })?;

    // Decode to get a semantic type
    crate::eval::decode_type_code(env.values.global, &meta_ty_code).map_err(|_| Error::BadSynth {
        tm: Syntax::metavariable_rc(metavariable.id, metavariable.substitution.clone()),
    })
}

/// Synthesize the type of a function application.
pub fn type_synth_application<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    application: &syn::Application<'db>,
) -> Result<val::RcTy<'db>, Error<'db>> {
    // First synthesize the type of the term being applied.
    let fun_ty = type_synth(env, &application.function)?;

    // Ensure that the applied term has a Pi type (semantic type, not code!)
    let val::Ty::Pi(source, _icit, target) = &*fun_ty else {
        return Err(Error::BadElim {
            tm: Syntax::application_rc(
                application.function.clone(),
                application.argument.clone(),
                application.icit,
            ),
            ty_got: fun_ty,
        });
    };

    // Check the argument against the source type of the function.
    type_check(env, &application.argument, source)?;

    // The overall type is determined by running the type closure with the argument.
    let arg = eval(env, &application.argument)?;
    val::run_ty_closure(&env.values.global, target, [arg]).map_err(Error::EvaluationFailure)
}

pub fn type_check_case<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    case: &syn::Case<'db>,
    expected_type: &val::Ty<'db>,
) -> Result<(), Error<'db>> {
    let scrutinee_level = case.scrutinee.index.to_level(env.depth());
    let scrutinee_ty = env.type_of(scrutinee_level).clone();

    // **PHASE 9**: In Strong Tarski, type constructors are decoded to Ty::TyConstructor
    let val::Ty::TyConstructor(tcon_name, tcon_args) = &*scrutinee_ty else {
        return Err(Error::BadElim {
            tm: Syntax::case_rc(case.scrutinee.index, case.branches.clone()),
            ty_got: scrutinee_ty,
        });
    };

    let tcon_info = env
        .values
        .global
        .type_constructor(*tcon_name)
        .map_err(Error::LookupError)?;

    let tcon_args_vec: Vec<_> = tcon_args.iter().cloned().collect();
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
            &tcon_args_vec,
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
        .map(|c| c.name(env.db).to_string(env.db))
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
                    // Pattern bindings already have semantic types (RcTy)
                    env.push_var(binding.ty.clone());
                }

                env.apply_subst(&result.solutions)?;

                let refined_expected_type = if result.solutions.is_empty() {
                    Rc::new(expected_type.clone())
                } else {
                    // Quote the semantic type and re-evaluate with substitutions applied
                    let quoted_expected =
                        quote::quote_ty(env.db, env.values.global, branch_depth, expected_type)?;
                    let mut eval_env = env.values.clone();
                    crate::eval::eval_ty(&mut eval_env, &quoted_expected)?
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

/// Check a term against an expected type.
pub fn type_check<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
    expected_ty: &val::Ty<'db>,
) -> Result<(), Error<'db>> {
    match term {
        Syntax::Lambda(lam) => type_check_lambda(env, lam, expected_ty),
        Syntax::Let(let_expr) => type_check_let(env, let_expr, expected_ty),
        Syntax::TypeConstructor(tc) => type_check_type_constructor(env, tc, expected_ty),
        Syntax::DataConstructor(dc) => type_check_data_constructor(env, dc, expected_ty),
        Syntax::Case(case) => type_check_case(env, case, expected_ty),

        // ========== DOGMATIC TYPE CODES (CHECK-ONLY) ==========
        // Type codes can ONLY be checked against a Universe classifier.
        // This is the strict Tarski separation: codes are terms, not types.
        Syntax::BitCode => type_check_bit_code(env, expected_ty),
        Syntax::UniverseCode(level) => type_check_universe_code(env, *level, expected_ty),
        Syntax::PiCode(source, icit, target) => {
            type_check_pi_code(env, source, *icit, target, expected_ty)
        }

        // Signal types (Bit) live in SignalUniverse
        Syntax::Bit(_) => type_check_bit(env, expected_ty),
        // Module types (HArrow) live in ModuleUniverse
        Syntax::HArrow(harrow) => type_check_harrow(env, harrow, expected_ty),
        // Hardware types (SLift, MLift) live in HardwareUniverse
        Syntax::SLift(slift) => type_check_slift(env, slift, expected_ty),
        Syntax::MLift(mlift) => type_check_mlift(env, mlift, expected_ty),

        // Bit values (0 and 1) can be checked against ^(Sig Bit)
        Syntax::Zero(zero) => type_check_zero(env, zero, expected_ty),
        Syntax::One(one) => type_check_one(env, one, expected_ty),

        // Equality types and proofs
        Syntax::Eq(eq) => type_check_eq(env, eq, expected_ty),
        Syntax::Refl(_) => type_check_refl(env, term, expected_ty),
        // Transport is an eliminator - it synthesizes, so falls through to type_check_synth_term
        _ => type_check_synth_term(env, term, expected_ty),
    }
}

// REMOVED: type_check_pi - legacy function for checking Pi syntax
// Lambda checking: Match against Pi types (semantic, not codes!)

fn type_check_lambda<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    lam: &syn::Lambda<'db>,
    ty: &val::Ty<'db>,
) -> Result<(), Error<'db>> {
    match ty {
        // Check lambda against Pi type (semantic type, not code!)
        val::Ty::Pi(source, _icit, target_closure) => {
            // **PHASE 9**: After Strong Tarski, all types are decoded.
            // No need to extract type codes - just use the decoded type directly.
            let var = env.push_var(source.clone());
            let target_ty = val::run_ty_closure(&env.values.global, target_closure, [var])
                .map_err(Error::EvaluationFailure)?;
            let r = type_check(env, &lam.body, &target_ty);
            env.pop();
            r
        }
        _ => Err(Error::BadCtor {
            tm: Syntax::lambda_rc(lam.icit, lam.body.clone()),
            ty_exp: Rc::new(ty.clone()),
        }),
    }
}

fn type_check_let<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    let_expr: &syn::Let<'db>,
    expected_type: &val::Ty<'db>,
) -> Result<(), Error<'db>> {
    // The type annotation is now a syntactic TYPE (syn::RcTy), not a term!
    // This enforces the Tarski separation.

    // 1. Validate the type annotation is well-formed
    check_ty(env, &let_expr.ty)?;

    // 2. Evaluate the syntactic type into a semantic type
    let sem_ty = crate::eval::eval_ty(&mut env.values, &let_expr.ty)?;

    // 3. Check and evaluate the value
    type_check(env, &let_expr.value, &sem_ty)?;
    let sem_value = eval(env, &let_expr.value)?;

    // 4. Push transparent binding and check body
    env.push_transparent(sem_ty, sem_value);
    let result = type_check(env, &let_expr.body, expected_type);
    env.pop();

    result
}

fn type_check_type_constructor<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    tcon: &syn::TypeConstructor<'db>,
    ty: &val::Ty<'db>,
) -> Result<(), Error<'db>> {
    match ty {
        // **PHASE 9**: Type constructors must be checked against Universe
        val::Ty::Universe(_level) => {
            // Type constructors are well-formed in any universe

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

            for (arg, arg_ty_binder) in tcon.arguments.iter().zip(&tcon_info.arguments) {
                let sem_arg_ty_code = eval::eval(&mut ty_env, &arg_ty_binder.ty)?;
                let sem_arg_ty = crate::eval::decode_type_code(env.values.global, &sem_arg_ty_code)?;
                type_check(env, arg, &sem_arg_ty)?;
                let sem_arg = eval::eval(&mut env.values, arg)?;
                ty_env.push(sem_arg);
            }

            // Check that the type constructor's universe level is compatible with
            // the expected universe. We implement universe cumulativity: a type
            // constructor in U_n can be used where U_m is expected if n ≤ m.
            match ty {
                // If checking against the native top-level UniverseType, any type constructor is valid
                // This handles meta-level functions like `foo : UniverseType -> Bit`
                val::Ty::UniverseType => {
                    // All type constructors belong to UniverseType
                }
                // **PHASE 9**: In Strong Tarski, expect Universe(level) instead of El(UniverseCode)
                val::Ty::Universe(expected_level) => {
                    // Compare universe levels - enforce cumulativity
                    let tcon_level: usize = tcon_info.level.into();
                    if tcon_level > *expected_level {
                        return Err(Error::BadType {
                            tm: Syntax::type_constructor_rc(
                                tcon.constructor,
                                tcon.arguments.clone(),
                            ),
                        });
                    }
                }
                _ => {
                    // Expected type is something else - this is an error caught elsewhere
                }
            }

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
    ty_exp: &val::Ty<'db>,
) -> Result<(), Error<'db>> {
    // **PHASE 9**: Data constructors must be checked against TyConstructor
    let val::Ty::TyConstructor(tc_name, tc_args) = ty_exp else {
        return Err(Error::BadCtor {
            tm: Syntax::data_constructor_rc(dc.constructor, dc.arguments.clone()),
            ty_exp: Rc::new(ty_exp.clone()),
        });
    };

    let dc_info = env
        .values
        .global
        .data_constructor(dc.constructor)
        .map_err(Error::LookupError)?;
    let tc_info = env
        .values
        .global
        .type_constructor(*tc_name)
        .map_err(Error::LookupError)?;

    let mut ty_env = val::Environment {
        global: env.values.global,
        local: val::LocalEnv::new(),
        transparent: val::TransparentEnv::new(),
    };

    let ps = tc_args[..tc_info.num_parameters].iter().cloned();
    ty_env.extend(ps);

    // Check that the data constructor has the correct number of arguments
    if dc.arguments.len() != dc_info.arguments.len() {
        return Err(Error::BadCtor {
            tm: Syntax::data_constructor_rc(dc.constructor, dc.arguments.clone()),
            ty_exp: Rc::new(ty_exp.clone()),
        });
    }

    for (arg, arg_ty_binder) in dc.arguments.iter().zip(&dc_info.arguments) {
        let sem_arg_ty_code = eval::eval(&mut ty_env, &arg_ty_binder.ty)?;
        let sem_arg_ty = crate::eval::decode_type_code(env.values.global, &sem_arg_ty_code)?;
        type_check(env, arg, &sem_arg_ty)?;
        let sem_arg = eval::eval(&mut env.values, arg)?;
        ty_env.push(sem_arg);
    }

    let ty_got_code = eval::eval(&mut ty_env, &dc_info.ty)?;
    let ty_got = crate::eval::decode_type_code(env.values.global, &ty_got_code)?;

    // Check if the synthesized type matches the expected type
    if equal::types_equal(
        env.values.global,
        &env.values.transparent,
        env.depth(),
        ty_exp,
        &ty_got,
    ) {
        Ok(())
    } else {
        Err(Error::BadCheck {
            tm: Syntax::data_constructor_rc(dc.constructor, dc.arguments.clone()),
            ty_exp: Rc::new(ty_exp.clone()),
            ty_got,
        })
    }
}

// ============================================================================
// HardwareUniverse Type Checking
// ============================================================================

// REMOVED: type_synth_lift - legacy function for synthesizing Lift types
// Lift is no longer a syntax variant; hardware types use SLift/MLift instead

fn type_check_bit<'db, 'g>(
    _env: &mut TCEnvironment<'db, 'g>,
    ty: &val::Ty<'db>,
) -> Result<(), Error<'db>> {
    match ty {
        val::Ty::SignalUniverseType => Ok(()),
        _ => Err(Error::BadCtor {
            tm: Syntax::bit_rc(),
            ty_exp: Rc::new(ty.clone()),
        }),
    }
}

fn type_check_harrow<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    harrow: &syn::HArrow<'db>,
    ty: &val::Ty<'db>,
) -> Result<(), Error<'db>> {
    match ty {
        val::Ty::ModuleUniverseType => {
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
    ty: &val::Ty<'db>,
) -> Result<(), Error<'db>> {
    // **PHASE 9**: SLift should be checked against ModuleEl(HardwareUniverse)
    // Hardware universes are in the Module domain
    match ty {
        val::Ty::ModuleEl(code) => {
            match code.as_ref() {
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
    ty: &val::Ty<'db>,
) -> Result<(), Error<'db>> {
    // **PHASE 9**: MLift should be checked against ModuleEl(HardwareUniverse)
    // Hardware universes are in the Module domain
    match ty {
        val::Ty::ModuleEl(code) => {
            match code.as_ref() {
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
        _ => Err(Error::BadCtor {
            tm: Syntax::mlift_rc(mlift.ty.clone()),
            ty_exp: Rc::new(ty.clone()),
        }),
    }
}

/// Check that `0` (Zero) is valid against the expected type.
/// Zero values have type El(BitCode).
fn type_check_zero<'db, 'g>(
    _env: &mut TCEnvironment<'db, 'g>,
    _zero: &syn::Zero<'db>,
    ty: &val::Ty<'db>,
) -> Result<(), Error<'db>> {
    // **PHASE 9**: The expected type must be BitType (decoded)
    match ty {
        val::Ty::BitType => Ok(()),
        _ => Err(Error::BadCtor {
            tm: Syntax::zero_rc(),
            ty_exp: Rc::new(ty.clone()),
        }),
    }
}

/// Check that `1` (One) is valid against the expected type.
/// One values have type El(BitCode).
fn type_check_one<'db, 'g>(
    _env: &mut TCEnvironment<'db, 'g>,
    _one: &syn::One<'db>,
    ty: &val::Ty<'db>,
) -> Result<(), Error<'db>> {
    // **PHASE 9**: The expected type must be BitType (decoded)
    match ty {
        val::Ty::BitType => Ok(()),
        _ => Err(Error::BadCtor {
            tm: Syntax::one_rc(),
            ty_exp: Rc::new(ty.clone()),
        }),
    }
}

// ========== DOGMATIC TYPE CODE CHECKING ==========
// Type codes are CHECK-ONLY. They cannot synthesize types.
// This enforces strict Tarski separation.

/// Check BitCode against a universe classifier.
/// BitCode fits in ANY universe (U_n for any n).
fn type_check_bit_code<'db, 'g>(
    _env: &mut TCEnvironment<'db, 'g>,
    expected_ty: &val::Ty<'db>,
) -> Result<(), Error<'db>> {
    match expected_ty {
        // BitCode : UniverseType (the meta-level classifier)
        val::Ty::UniverseType => Ok(()),

        // **PHASE 9**: BitCode : Universe(n) for any n
        val::Ty::Universe(_) => Ok(()),

        _ => Err(Error::BadType {
            tm: Rc::new(Syntax::BitCode),
        }),
    }
}

/// Check UniverseCode(n) against a universe classifier.
/// UniverseCode(n) : Universe(m) only if n < m (strict stratification).
/// UniverseCode(n) : UniverseType always (the meta-level classifier accepts all).
fn type_check_universe_code<'db, 'g>(
    _env: &mut TCEnvironment<'db, 'g>,
    level: usize,
    expected_ty: &val::Ty<'db>,
) -> Result<(), Error<'db>> {
    match expected_ty {
        // UniverseCode(n) : UniverseType (the meta-level classifier)
        val::Ty::UniverseType => Ok(()),

        // **PHASE 9**: UniverseCode(n) : Universe(m) only if n < m
        val::Ty::Universe(m) => {
            if level < *m {
                Ok(())
            } else {
                Err(Error::BadType {
                    tm: Rc::new(Syntax::UniverseCode(level)),
                })
            }
        }

        _ => Err(Error::BadType {
            tm: Rc::new(Syntax::UniverseCode(level)),
        }),
    }
}

/// Check PiCode (A, icit, B) against a universe classifier.
/// PiCode fits in a universe if both A and B fit in that universe.
/// This is the key win of check-only: no max() calculation needed!
/// The expected universe is pushed down into both components.
fn type_check_pi_code<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    source: &RcSyntax<'db>,
    _icit: crate::common::Icit,
    target: &BindingSyntax<'db>,
    expected_ty: &val::Ty<'db>,
) -> Result<(), Error<'db>> {
    // Validate that the expected type is actually a universe
    match expected_ty {
        val::Ty::UniverseType => {}
        // **PHASE 9**: Expect Universe(n) instead of El(UniverseCode(n))
        val::Ty::Universe(_) => {}
        _ => {
            return Err(Error::BadType {
                tm: Rc::new(Syntax::PiCode(source.clone(), _icit, target.clone())),
            })
        }
    }

    // Push the expected universe down into the source
    type_check(env, source, expected_ty)?;

    // Evaluate source so we can bind it in the context for the target
    let sem_source = eval(env, source)?;

    // Push the bound variable and check the target against the same universe
    let sem_source_ty = crate::eval::decode_type_code(env.values.global, &sem_source)?;
    env.push_var(sem_source_ty);
    let result = type_check(env, &target.body, expected_ty);
    env.pop();

    result
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
            // **PHASE 9**: HardwareUniverse is wrapped in ModuleEl
            match ty.as_ref() {
                val::Ty::ModuleEl(code) => match code.as_ref() {
                    Value::HardwareUniverse(_) => Ok(()),
                    _ => Err(Error::BadType {
                        tm: Rc::new(term.clone()),
                    }),
                },
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
            // SignalUniverse is the type of signal types
            match ty.as_ref() {
                val::Ty::SignalUniverseType => Ok(()),
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
            // ModuleUniverse is the type of module types
            match ty.as_ref() {
                val::Ty::ModuleUniverseType => Ok(()),
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
    ty: &val::Ty<'db>,
) -> Result<(), Error<'db>> {
    // **PHASE 9**: Eq types must be checked against Universe
    match ty {
        val::Ty::Universe(_level) => {
            // eq.ty is RcSyntax, need to synthesize and check it's a universe
            let _ty_of_ty = type_synth(env, &eq.ty)?;
            let sem_ty_code = eval(env, &eq.ty)?;
            let sem_ty = crate::eval::decode_type_code(env.values.global, &sem_ty_code)
                .map_err(Error::EvaluationFailure)?;
            type_check(env, &eq.lhs, &sem_ty)?;
            type_check(env, &eq.rhs, &sem_ty)?;

            Ok(())
        }
        _ => Err(Error::BadCtor {
            tm: Syntax::eq_rc(eq.ty.clone(), eq.lhs.clone(), eq.rhs.clone()),
            ty_exp: Rc::new(ty.clone()),
        }),
    }
}

fn type_synth_eq<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    eq: &syn::EqType<'db>,
) -> Result<val::RcTy<'db>, Error<'db>> {
    // eq.ty is RcSyntax, need to synthesize its type
    let ty_ty = type_synth(env, &eq.ty)?;

    // **PHASE 9**: The type of eq.ty must be Universe(level)
    let val::Ty::Universe(level) = ty_ty.as_ref() else {
        return Err(Error::BadCtor {
            tm: Syntax::eq_rc(eq.ty.clone(), eq.lhs.clone(), eq.rhs.clone()),
            ty_exp: ty_ty,
        });
    };

    // Evaluate the type and check the lhs and rhs against it
    let sem_ty_code = eval(env, &eq.ty)?;
    let sem_ty = crate::eval::decode_type_code(env.values.global, &sem_ty_code)
        .map_err(Error::EvaluationFailure)?;
    type_check(env, &eq.lhs, &sem_ty)?;
    type_check(env, &eq.rhs, &sem_ty)?;

    // Eq A x y : Universe(level)
    Ok(val::Ty::universe_rc(*level))
}

fn type_check_refl<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
    ty: &val::Ty<'db>,
) -> Result<(), Error<'db>> {
    // **PHASE 9**: refl must be checked against SignalEl(EqType) or ModuleEl(EqType)
    // Eq types are wrapped values, not decoded types
    let code = match ty {
        val::Ty::SignalEl(code) | val::Ty::ModuleEl(code) => code,
        _ => {
            return Err(Error::BadCtor {
                tm: Rc::new(term.clone()),
                ty_exp: Rc::new(ty.clone()),
            });
        }
    };

    let Value::EqType(eq_ty) = code.as_ref() else {
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
) -> Result<val::RcTy<'db>, Error<'db>> {
    // Synthesize the type of the proof
    let proof_ty = type_synth(env, &transport.proof)?;

    // **PHASE 9**: The proof must have an equality type (wrapped in SignalEl or ModuleEl)
    let proof_code = match &*proof_ty {
        val::Ty::SignalEl(code) | val::Ty::ModuleEl(code) => code,
        _ => {
            return Err(Error::BadSynth {
                tm: Syntax::transport_rc(
                    transport.motive.clone(),
                    transport.proof.clone(),
                    transport.value.clone(),
                ),
            });
        }
    };
    let Value::EqType(eq_ty) = &**proof_code else {
        return Err(Error::BadSynth {
            tm: Syntax::transport_rc(
                transport.motive.clone(),
                transport.proof.clone(),
                transport.value.clone(),
            ),
        });
    };

    // The motive should have type: (decoded eq_ty.ty) → UniverseType
    // Decode the equality type
    let eq_inner_ty = crate::eval::decode_type_code(env.values.global, &eq_ty.ty)
        .map_err(Error::EvaluationFailure)?;
    let motive_expected_ty = val::Ty::pi_rc(
        eq_inner_ty,
        crate::Icit::Explicit,
        val::TyClosure::new(env.values.local.clone(), Rc::new(syn::Ty::UniverseType)),
    );

    // Check the motive against this type
    type_check(env, &transport.motive, &motive_expected_ty)?;

    // Evaluate the motive to get a value we can apply
    let motive_val = eval(env, &transport.motive)?;
    let Value::Lambda(lambda) = &*motive_val else {
        return Err(Error::BadSynth {
            tm: transport.motive.clone(),
        });
    };

    // Apply the motive to the lhs to get the type code of the value
    let p_of_x_code = run_closure(env, &lambda.body, [eq_ty.lhs.clone()])?;
    let p_of_x_ty = crate::eval::decode_type_code(env.values.global, &p_of_x_code)
        .map_err(Error::EvaluationFailure)?;

    type_check(env, &transport.value, &p_of_x_ty)?;

    // Apply the motive to the rhs to get the result type code
    let p_of_y_code = run_closure(env, &lambda.body, [eq_ty.rhs.clone()])?;

    // **PHASE 9**: Decode the result type code to get the semantic type
    crate::eval::decode_type_code(env.values.global, &p_of_y_code)
        .map_err(Error::EvaluationFailure)
}

// The syn::Closure type has been removed. This function is no longer needed.
// Arity is now stored directly in DynBinding structures.

// REMOVED: Old is_subtype that worked on Value
// Now using equal::is_subtype which works on val::Ty

// Synthesize a type for the term, then check for equality against the expected type.
// NEW: Now uses subsumption instead of strict equality!
pub fn type_check_synth_term<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
    ty1: &val::Ty<'db>,
) -> Result<(), Error<'db>> {
    let ty2 = type_synth(env, term)?;

    // NEW: Use subsumption instead of strict equality
    // This allows cumulativity: if term has type A and A <: B, then term has type B
    if equal::is_subtype(
        env.values.global,
        &env.values.transparent,
        env.depth(),
        &ty2,
        ty1,
    ) {
        Ok(())
    } else {
        Err(Error::BadCheck {
            tm: Rc::new(term.clone()),
            ty_got: ty2,
            ty_exp: Rc::new(ty1.clone()),
        })
    }
}

/// Check that the given term is a valid type.
/// This includes both meta-level types (in Universe) and hardware types (in Type).
pub fn check_type<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
) -> Result<(), Error<'db>> {
    // NEW: Check nodes with universe classifiers are valid types!
    // This handles type codes wrapped in explicit annotations like (U0 : UniverseType)
    if let Syntax::Check(check) = term {
        let ty = crate::check::type_synth_check(env, check)?;
        // **PHASE 9**: The check node must have a universe classifier type
        match ty.as_ref() {
            val::Ty::UniverseType | val::Ty::SignalUniverseType | val::Ty::ModuleUniverseType => {
                return Ok(())
            }
            val::Ty::ModuleEl(code) => match code.as_ref() {
                Value::HardwareUniverse(_) => return Ok(()),
                _ => {}
            },
            _ => {}
        }
    }

    // NEW: If the term is a PiCode, then we just check that it is valid.
    if let Syntax::PiCode(source, _icit, target) = term {
        check_type(env, source)?;
        let ty_code = eval(env, source)?;
        let ty = crate::eval::decode_type_code(env.values.global, &ty_code)
            .map_err(Error::EvaluationFailure)?;
        env.push_var(ty);
        let result = check_type(env, &target.body);
        env.pop();
        return result;
    }

    if let Syntax::TypeConstructor(tc) = term {
        return check_type_constructor_type(env, tc);
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
    if let Syntax::HArrow(_harrow) = term {
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

    // Otherwise, synthesize a type for the term, which must be Universe(_).
    // **PHASE 9**: After Strong Tarski, we expect decoded Universe, not El(UniverseCode).
    let ty = type_synth(env, term)?;
    match ty.as_ref() {
        val::Ty::Universe(_) => Ok(()),
        _ => Err(Error::BadType {
            tm: Rc::new(term.clone()),
        }),
    }
}

fn check_eq_type<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    eq: &stx::EqType<'db>,
) -> Result<(), Error<'db>> {
    check_type(env, &eq.ty)?;
    let sem_ty_code = eval(env, &eq.ty)?;
    // **PHASE 9**: Decode the type code instead of wrapping in El
    let sem_ty = crate::eval::decode_type_code(env.values.global, &sem_ty_code)?;
    type_check(env, &eq.lhs, &sem_ty)?;
    type_check(env, &eq.rhs, &sem_ty)?;
    Ok(())
}

// REMOVED: check_pi_type - legacy function for checking Pi syntax
// PiCode checking is now inlined in check_type

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

    for (arg, arg_ty_binder) in tcon.arguments.iter().zip(&tcon_info.arguments) {
        let sem_arg_ty_code = eval::eval(&mut ty_env, &arg_ty_binder.ty)?;
        let sem_arg_ty = crate::eval::decode_type_code(env.values.global, &sem_arg_ty_code)
            .map_err(Error::EvaluationFailure)?;
        type_check(env, arg, &sem_arg_ty)?;
        let sem_arg = eval::eval(&mut env.values, arg)?;
        ty_env.push(sem_arg);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    use syn::parse::parse_syntax;
    use syn::{RcSyntax, Telescope};
    

    
    use crate::QualifiedName;
    use crate::TestDatabase;
    use hwml_support::{FromWithDb, IntoWithDb};

    // ========== Prelude definitions ==========

    use crate::test_utils::{eval_str, load_prelude, NAT_PRELUDE, VEC_PRELUDE};

    /// Create a GlobalEnv with Nat type defined.
    fn make_nat_global<'db>(db: &'db TestDatabase) -> val::GlobalEnv<'db> {
        load_prelude(db, NAT_PRELUDE)
    }

    /// Create a GlobalEnv with Nat and Vec types defined.
    fn make_vec_global<'db>(db: &'db TestDatabase) -> val::GlobalEnv<'db> {
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
    fn parse<'db>(db: &'db TestDatabase, input: &'db str) -> RcSyntax<'db> {
        parse_syntax(db, input).unwrap_or_else(|e| panic!("Failed to parse '{}': {:?}", input, e))
    }

    // ========== check_type tests ==========

    /// Test that check_type accepts Universe (with check-only type codes, they need annotations).
    #[test]
    fn test_check_type_accepts_universe() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // With check-only type codes, U0 needs an annotation
        let u0 = parse(&db, "U0 : UniverseType");
        assert!(check_type(&mut env, &u0).is_ok());
    }

    /// Test that check_type accepts Pi types (with check-only type codes).
    #[test]
    fn test_check_type_accepts_pi() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // With check-only type codes, we construct a Pi directly
        // Build: (∀(x : (U0 : UniverseType)) → (U0 : UniverseType)) : UniverseType
        let u0_checked: RcSyntax = Syntax::check_rc(
            syn::Ty::universe_type_rc(),
            Rc::new(Syntax::UniverseCode(0)),
        );
        let pi = Syntax::check_rc(
            syn::Ty::universe_type_rc(),
            Rc::new(Syntax::PiCode(
                u0_checked.clone(),
                Icit::Explicit,
                Binding::new(Name::anonymous(&db), u0_checked),
            )),
        );
        assert!(check_type(&mut env, &pi).is_ok());
    }

    /// Test that check_type accepts Bit (signal type - with check-only type codes).
    #[test]
    fn test_check_type_accepts_bit() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // With check-only type codes, Bit needs an annotation
        let bit = parse(&db, "Bit : SignalUniverseType");
        assert!(check_type(&mut env, &bit).is_ok());
    }

    /// Test that check_type accepts HArrow (module type).
    #[test]
    fn test_check_type_accepts_harrow() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // ^s Bit -> ^s Bit : MType (module type with hardware type components)
        let harrow = parse(&db, "^s Bit -> ^s Bit");
        assert!(check_type(&mut env, &harrow).is_ok());
    }

    // ========== type_synth tests ==========

    /// Test that Universe type codes are check-only.
    /// With strict Tarski separation, U0 cannot synthesize a type - it must be checked.
    #[test]
    fn test_synth_universe() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // NEW: U0 alone cannot synthesize - it's check-only
        // We need to provide an explicit type annotation
        let u0_annotated = parse(&db, "U0 : UniverseType");
        let ty = type_synth(&mut env, &u0_annotated).expect("should synthesize");

        // The annotated universe code has type UniverseType
        match ty.as_ref() {
            val::Ty::UniverseType => {} // Correct!
            _ => panic!("Expected UniverseType, got {:?}", ty),
        }
    }

    /// Test that variables get their type from the environment.
    #[test]
    fn test_synth_variable() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // **PHASE 9**: Push a variable of type Universe(0) (decoded)
        let u0_ty = val::Ty::universe_rc(0);
        env.push_var(u0_ty.clone());

        // Variable %0 should have type Universe(0)
        // Parse at depth 1 since we have one variable in scope
        let var = syn::parse::parse_syntax_at_depth(&db, "%0", 1).expect("should parse");
        let ty = type_synth(&mut env, &var).expect("should synthesize");

        // **PHASE 9**: Type is Universe(0) (decoded)
        match ty.as_ref() {
            val::Ty::Universe(level) => assert_eq!(*level, 0),
            _ => panic!("Expected Universe(0), got {:?}", ty),
        }
    }

    /// Test that constants get their type from the global environment.
    #[test]
    fn test_synth_constant() {
        let db = TestDatabase::default();
        let mut global = val::GlobalEnv::new(&db);

        let cid = |s: &str| QualifiedName::from_with_db(&db, s);

        // Add constant @myConst : 𝒰0 = 𝒰0
        global.add_constant(
            cid("myConst"),
            val::ConstantInfo::new(parse(&db, "U0"), parse(&db, "U0")),
        );

        let mut env = make_env(&db, &global);

        // @myConst should have type El(𝒰0)
        let const_syn = parse(&db, "@myConst");
        let ty = type_synth(&mut env, &const_syn).expect("should synthesize");

        // **PHASE 9**: Type is Universe(0) (decoded)
        match ty.as_ref() {
            val::Ty::Universe(level) => assert_eq!(*level, 0),
            _ => panic!("Expected Universe(0), got {:?}", ty),
        }
    }

    /// Test that primitives get their type from the global environment.
    #[test]
    fn test_synth_primitive() {
        let db = TestDatabase::default();
        let mut global = val::GlobalEnv::new(&db);

        let cid = |s: &str| QualifiedName::from_with_db(&db, s);

        // Add primitive $Nat : 𝒰0
        global.add_primitive(cid("Nat"), val::PrimitiveInfo::new(parse(&db, "U0")));

        let mut env = make_env(&db, &global);

        // $Nat should have type El(𝒰0)
        let prim_syn = parse(&db, "$Nat");
        let ty = type_synth(&mut env, &prim_syn).expect("should synthesize");

        // Type is El(UniverseCode(0))
        // **PHASE 9**: Type is Universe(0) (decoded)
        match ty.as_ref() {
            val::Ty::Universe(level) => assert_eq!(*level, 0),
            _ => panic!("Expected Universe(0), got {:?}", ty),
        }
    }

    // ========== type_check tests ==========

    /// Test that Pi types check against Universe.
    #[test]
    fn test_check_pi_against_universe() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // PiCode(U0, U0) : Universe(1)
        // Build the PiCode directly to avoid parser's automatic Check wrapping
        let u0: RcSyntax = Syntax::UniverseCode(0).into();
        let pi = Syntax::PiCode(
            u0.clone(),
            Icit::Explicit,
            Binding::new(Name::anonymous(&db), u0),
        );

        // **PHASE 9**: PiCode(U0, U0) has type Universe(1)
        // because U0 : Universe(1) (level 0 < 1)
        let u1_ty = val::Ty::universe_rc(1);
        let result = type_check(&mut env, &pi.into(), &u1_ty);
        assert!(result.is_ok(), "type_check failed: {:?}", result.err());
    }

    /// Test that Lambda checks against Pi type.
    #[test]
    fn test_check_lambda_against_pi() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // λ %x → %x : Pi(x : Universe(0), Universe(0))
        let lam = parse(&db, "λ %x -> %x");

        // Create the semantic Pi type for ∀ (%x : Universe(0)) → Universe(0)
        // Domain: Universe(0) - the type of small types (Strong Tarski decoded form!)
        // Codomain: Universe(0) - the type of small types
        let domain_ty = val::Ty::universe_rc(0);
        // The codomain is non-dependent, so the syntactic body is just UniverseType
        // (which evaluates to Universe(0) via eval_ty)
        let codomain_syn = syn::Ty::el_rc(Rc::new(Syntax::UniverseCode(0)));
        let ty_closure = val::TyClosure::new(val::LocalEnv::new(), codomain_syn);
        let pi_ty = val::Ty::pi_rc(domain_ty, Icit::Explicit, ty_closure);

        let result = type_check(&mut env, &lam, &pi_ty);
        assert!(result.is_ok(), "type_check failed: {:?}", result.err());
    }

    /// Test that Bit checks against SignalUniverse.
    #[test]
    fn test_check_bit_against_signal_universe() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        let bit = parse(&db, "Bit");
        // Bit has type SignalUniverseType (a native type, not El)
        let signal_universe_ty = val::Ty::signal_universe_type_rc();

        assert!(type_check(&mut env, &bit, &signal_universe_ty).is_ok());
    }

    /// Test that HArrow checks against ModuleUniverse.
    #[test]
    fn test_check_harrow_against_module_universe() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // ^s Bit -> ^s Bit : ModuleUniverseType (HArrow with hardware type components)
        let harrow = parse(&db, "^s Bit -> ^s Bit");
        let module_universe_ty = val::Ty::module_universe_type_rc();

        assert!(type_check(&mut env, &harrow, &module_universe_ty).is_ok());
    }

    // ========== Application synthesis tests ==========

    /// Test that function application synthesizes the correct type.
    #[test]
    fn test_synth_application() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // Set up: we need a variable of Pi type
        // Create a function f : Pi(x : El(U0), El(U0))
        // Domain: El(UniverseCode(0)) - the type of small types
        // **PHASE 9**: Domain: Universe(0) - the type of small types (decoded)
        let domain_ty = val::Ty::universe_rc(0);
        // The codomain is non-dependent, so the syntactic body is Universe(0)
        // Note: syn::Ty still has El for the Tarski bridge in syntax
        let codomain_syn = syn::Ty::el_rc(Rc::new(Syntax::UniverseCode(0)));
        let ty_closure = val::TyClosure::new(val::LocalEnv::new(), codomain_syn);
        let pi_ty = val::Ty::pi_rc(domain_ty, Icit::Explicit, ty_closure);

        // Push f into the environment
        env.push_var(pi_ty);

        // Now apply f to BitCode (the Bit type code) which has type El(U0)
        // Construct the application manually: %0 BitCode
        let var_f = syn::parse::parse_syntax_at_depth(&db, "%0", 1).expect("should parse");
        let app = Syntax::application_rc(var_f, Syntax::BitCode.into(), Icit::Explicit);

        let ty = type_synth(&mut env, &app).expect("should synthesize");

        // The result should be El(U0) (the type of small types)
        // **PHASE 9**: Type is Universe(0) (decoded)
        match ty.as_ref() {
            val::Ty::Universe(level) => assert_eq!(*level, 0),
            _ => panic!("Expected Universe(0), got {:?}", ty),
        }
    }

    // ========== Metavariable type synthesis tests ==========

    /// Test that metavariables without arguments synthesize to their declared type.
    #[test]
    fn test_synth_metavariable_no_args() {
        use crate::common::MetaVariableId;

        let db = TestDatabase::default();
        let mut global = val::GlobalEnv::new(&db);

        let meta_id = MetaVariableId::new(0);
        global.add_metavariable(meta_id, Telescope::from_pairs(vec![]), parse(&db, "U0"));

        let mut env = make_env(&db, &global);

        let meta_stx = Syntax::metavariable(meta_id, vec![]);
        let ty = type_synth(&mut env, &meta_stx).expect("should synthesize");

        // **PHASE 9**: Type is Universe(0) (decoded)
        match ty.as_ref() {
            val::Ty::Universe(level) => assert_eq!(*level, 0),
            _ => panic!("Expected Universe(0), got {:?}", ty),
        }
    }

    /// Test that metavariables with arguments synthesize with substitution applied.
    #[test]
    fn test_synth_metavariable_with_args() {
        use crate::common::MetaVariableId;
        use hwml_support::FromWithDb;

        let db = TestDatabase::default();
        let mut global = val::GlobalEnv::new(&db);

        let meta_id = MetaVariableId::new(0);
        global.add_metavariable(
            meta_id,
            Telescope::from_pairs(vec![(Name::from_with_db(&db, "0"), parse(&db, "U0"))]),
            parse(&db, "U0"),
        );

        let mut env = make_env(&db, &global);

        let bit_code: RcSyntax = Syntax::BitCode.into();
        let meta_stx = Syntax::metavariable(meta_id, vec![bit_code]);
        let ty = type_synth(&mut env, &meta_stx).expect("should synthesize");

        // **PHASE 9**: Type is Universe(0) (decoded)
        match ty.as_ref() {
            val::Ty::Universe(level) => assert_eq!(*level, 0),
            _ => panic!("Expected Universe(0), got {:?}", ty),
        }
    }

    /// Test that metavariable with wrong number of arguments fails.
    #[test]
    fn test_synth_metavariable_wrong_arg_count() {
        use crate::common::MetaVariableId;
        use hwml_support::FromWithDb;

        let db = TestDatabase::default();
        let mut global = val::GlobalEnv::new(&db);

        let meta_id = MetaVariableId::new(0);
        global.add_metavariable(
            meta_id,
            Telescope::from_pairs(vec![(Name::from_with_db(&db, "0"), parse(&db, "U0"))]),
            parse(&db, "U0"),
        );

        let mut env = make_env(&db, &global);

        let meta_stx = Syntax::metavariable(meta_id, vec![]);
        assert!(type_synth(&mut env, &meta_stx).is_err());
    }

    /// Test that metavariable with wrong argument type fails.
    #[test]
    fn test_synth_metavariable_wrong_arg_type() {
        use crate::common::MetaVariableId;
        use hwml_support::FromWithDb;

        let db = TestDatabase::default();
        let mut global = val::GlobalEnv::new(&db);

        let meta_id = MetaVariableId::new(0);
        global.add_metavariable(
            meta_id,
            Telescope::from_pairs(vec![(Name::from_with_db(&db, "0"), parse(&db, "$Bit"))]),
            parse(&db, "U0"),
        );

        let mut env = make_env(&db, &global);

        let u0 = parse(&db, "U0");
        let meta_stx = Syntax::metavariable(meta_id, vec![u0]);
        assert!(type_synth(&mut env, &meta_stx).is_err());
    }

    // ========== apply_subst tests ==========

    /// Test that apply_subst correctly turns a variable into a transparent let-binding.
    /// Context: [n : Nat]
    /// Substitution: n ~ @Zero
    /// Expected: values.local[0] becomes @Zero
    #[test]
    fn test_apply_subst_simple() {
        let db = TestDatabase::default();
        let global = make_nat_global(&db);

        let mut env = make_env(&db, &global);

        // **PHASE 9**: Push n : Nat (decoded as TyConstructor)
        let nat = Value::type_constructor_rc("Nat".into_with_db(&db), vec![]);
        // Decode the type constructor into semantic type
        let nat_ty = crate::eval::decode_type_code(&global, &nat).expect("should decode");
        env.push_var(nat_ty);

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
        let db = TestDatabase::default();
        let global = make_vec_global(&db);

        let mut env = make_env(&db, &global);

        // **PHASE 9**: Push n : Nat (decoded) at level 0
        let nat_code = Value::type_constructor_rc("Nat".into_with_db(&db), vec![]);
        let nat_ty = crate::eval::decode_type_code(&global, &nat_code).expect("should decode");
        let n = env.push_var(nat_ty);

        // Push v : Vec Bit n (decoded) at level 1
        let bit_code = Value::bit_rc();
        let vec_bit_n =
            Value::type_constructor_rc("Vec".into_with_db(&db), vec![bit_code.clone(), n.clone()]);
        let vec_ty = crate::eval::decode_type_code(&global, &vec_bit_n).expect("should decode");
        env.push_var(vec_ty);

        // **PHASE 9**: Verify initial state: types[1] is TyConstructor(Vec, [Bit, Rigid(n)])
        match env.types[1].as_ref() {
            val::Ty::TyConstructor(name, args) => {
                assert_eq!(name.name(&db).to_string(&db), "Vec");
                assert_eq!(args.len(), 2);
                // Second argument should be a Rigid (variable n at level 0)
                match args[1].as_ref() {
                    Value::Rigid(r) => assert_eq!(r.head.level, Level::new(0)),
                    other => panic!("Expected Rigid, got {:?}", other),
                }
            }
            other => panic!("Expected TyConstructor(Vec), got {:?}", other),
        }

        // Apply substitution: n ~ @Zero
        let zero = Value::data_constructor_rc("Zero".into_with_db(&db), vec![]);
        let solutions = vec![(Level::new(0), zero.clone())];
        env.apply_subst(&solutions)
            .expect("apply_subst should succeed");

        // **PHASE 9**: Now types[1] should be TyConstructor(Vec, [Bit, @Zero])
        match env.types[1].as_ref() {
            val::Ty::TyConstructor(name, args) => {
                assert_eq!(name.name(&db).to_string(&db), "Vec");
                assert_eq!(args.len(), 2);
                // Second argument should now be @Zero
                match args[1].as_ref() {
                    Value::DataConstructor(dcon) => {
                        assert_eq!(dcon.constructor.name(&db).to_string(&db), "Zero");
                    }
                    other => panic!("Expected DataConstructor(@Zero), got {:?}", other),
                }
            }
            other => panic!("Expected TyConstructor(Vec), got {:?}", other),
        }
    }

    /// Test that apply_subst handles multiple solutions correctly.
    /// Context: [n : Nat, m : Nat, v : Vec Bit n, w : Vec Bit m]
    /// Substitution: n ~ @Zero, m ~ @Succ @Zero
    /// Expected: types[2] becomes Vec Bit @Zero, types[3] becomes Vec Bit (@Succ @Zero)
    #[test]
    fn test_apply_subst_multiple_solutions() {
        let db = TestDatabase::default();
        let global = make_vec_global(&db);

        let mut env = make_env(&db, &global);
        let bit_code = Value::bit_rc();

        // **PHASE 9**: Push n : Nat (decoded) at level 0
        let nat_code = Value::type_constructor_rc("Nat".into_with_db(&db), vec![]);
        let nat_ty = crate::eval::decode_type_code(&global, &nat_code).expect("should decode");
        let n = env.push_var(nat_ty.clone());

        // Push m : Nat (decoded) at level 1
        let m = env.push_var(nat_ty);

        // Push v : Vec Bit n (decoded) at level 2
        let vec_bit_n =
            Value::type_constructor_rc("Vec".into_with_db(&db), vec![bit_code.clone(), n.clone()]);
        let vec_ty_n = crate::eval::decode_type_code(&global, &vec_bit_n).expect("should decode");
        env.push_var(vec_ty_n);

        // Push w : Vec Bit m (decoded) at level 3
        let vec_bit_m =
            Value::type_constructor_rc("Vec".into_with_db(&db), vec![bit_code.clone(), m.clone()]);
        let vec_ty_m = crate::eval::decode_type_code(&global, &vec_bit_m).expect("should decode");
        env.push_var(vec_ty_m);

        // Apply substitutions: n ~ @Zero, m ~ @Succ @Zero
        let zero = Value::data_constructor_rc("Zero".into_with_db(&db), vec![]);
        let succ_zero = Value::data_constructor_rc("Succ".into_with_db(&db), vec![zero.clone()]);
        let solutions = vec![
            (Level::new(0), zero.clone()),
            (Level::new(1), succ_zero.clone()),
        ];
        env.apply_subst(&solutions)
            .expect("apply_subst should succeed");

        // **PHASE 9**: Check types[2]: TyConstructor(Vec, [Bit, @Zero])
        match env.types[2].as_ref() {
            val::Ty::TyConstructor(_, args) => match args[1].as_ref() {
                Value::DataConstructor(dcon) => {
                    assert_eq!(dcon.constructor.name(&db).to_string(&db), "Zero");
                }
                other => panic!("Expected @Zero, got {:?}", other),
            },
            other => panic!("Expected TyConstructor, got {:?}", other),
        }

        // **PHASE 9**: Check types[3]: TyConstructor(Vec, [Bit, (@Succ @Zero)])
        match env.types[3].as_ref() {
            val::Ty::TyConstructor(_, args) => match args[1].as_ref() {
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
            other => panic!("Expected TyConstructor, got {:?}", other),
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
        let db = TestDatabase::default();
        let global = make_vec_global(&db);

        let mut env = make_env(&db, &global);
        let bit_code = Value::bit_rc();
        let nat_code = Value::type_constructor_rc("Nat".into_with_db(&db), vec![]);
        let nat_ty = crate::eval::decode_type_code(&global, &nat_code).expect("should decode");

        // **PHASE 9**: Push n, m, p : Nat (decoded) at levels 0, 1, 2
        let n = env.push_var(nat_ty.clone());
        let m = env.push_var(nat_ty.clone());
        let p = env.push_var(nat_ty);

        // Push v : Vec Bit n (decoded) at level 3
        let vec_bit_n =
            Value::type_constructor_rc("Vec".into_with_db(&db), vec![bit_code.clone(), n.clone()]);
        let vec_ty_n = crate::eval::decode_type_code(&global, &vec_bit_n).expect("should decode");
        env.push_var(vec_ty_n);

        // Push w : Vec Bit m (decoded) at level 4
        let vec_bit_m =
            Value::type_constructor_rc("Vec".into_with_db(&db), vec![bit_code.clone(), m.clone()]);
        let vec_ty_m = crate::eval::decode_type_code(&global, &vec_bit_m).expect("should decode");
        env.push_var(vec_ty_m);

        // Push x : Vec Bit p (decoded) at level 5
        let vec_bit_p =
            Value::type_constructor_rc("Vec".into_with_db(&db), vec![bit_code.clone(), p.clone()]);
        let vec_ty_p = crate::eval::decode_type_code(&global, &vec_bit_p).expect("should decode");
        env.push_var(vec_ty_p);

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

        // **PHASE 9**: Verify types[3]: TyConstructor(Vec, [Bit, @Zero])
        match env.types[3].as_ref() {
            val::Ty::TyConstructor(name, args) => {
                assert_eq!(name.name(&db).to_string(&db), "Vec");
                match args[1].as_ref() {
                    Value::DataConstructor(dcon) => {
                        assert_eq!(dcon.constructor.name(&db).to_string(&db), "Zero");
                    }
                    other => panic!("types[3] index: Expected @Zero, got {:?}", other),
                }
            }
            other => panic!("types[3]: Expected TyConstructor, got {:?}", other),
        }

        // **PHASE 9**: Verify types[4]: TyConstructor(Vec, [Bit, (@Succ @Zero)])
        match env.types[4].as_ref() {
            val::Ty::TyConstructor(name, args) => {
                assert_eq!(name.name(&db).to_string(&db), "Vec");
                match args[1].as_ref() {
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
            other => panic!("types[4]: Expected TyConstructor, got {:?}", other),
        }

        // **PHASE 9**: Verify types[5]: TyConstructor(Vec, [Bit, (@Succ (@Succ @Zero))])
        match env.types[5].as_ref() {
            val::Ty::TyConstructor(name, args) => {
                assert_eq!(name.name(&db).to_string(&db), "Vec");
                match args[1].as_ref() {
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
                                    other => panic!(
                                        "types[5] inner: Expected @Zero, got {:?}",
                                        other
                                    ),
                                }
                            }
                            other => panic!("types[5] middle: Expected @Succ, got {:?}", other),
                        }
                    }
                    other => panic!("types[5] index: Expected @Succ, got {:?}", other),
                }
            }
            other => panic!("types[5]: Expected TyConstructor, got {:?}", other),
        }
    }

    // ========== Coverage Checking tests ==========

    /// Test that exhaustive pattern matching on Nat succeeds.
    /// n : Nat |- n case @Zero => @Zero, @Succ %m => @Zero : Nat
    #[test]
    fn test_exhaustive_nat_case() {
        let db = TestDatabase::default();
        let global = make_nat_global(&db);
        let mut env = make_env(&db, &global);

        // **PHASE 9**: Push n : Nat (decoded)
        let nat_code = Value::type_constructor_rc("Nat".into_with_db(&db), vec![]);
        let nat_ty = crate::eval::decode_type_code(&global, &nat_code).expect("should decode");
        env.push_var(nat_ty.clone());

        // Parse case: !0 case { @Zero => [@Zero] | @Succ %m => [@Zero] }
        // !0 refers to the variable at index 0 (the most recent variable, n)
        let case_stx = parse(&db, "!0 case { @Zero => [@Zero] | @Succ %m => [@Zero] }");
        let Syntax::Case(case) = case_stx.as_ref() else {
            panic!("Expected Case syntax");
        };

        // Check the case against type Nat (decoded)
        let result = type_check_case(&mut env, case, &nat_ty);
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
        let db = TestDatabase::default();
        let global = make_nat_global(&db);
        let mut env = make_env(&db, &global);

        // **PHASE 9**: Push n : Nat (decoded)
        let nat_code = Value::type_constructor_rc("Nat".into_with_db(&db), vec![]);
        let nat_ty = crate::eval::decode_type_code(&global, &nat_code).expect("should decode");
        env.push_var(nat_ty.clone());

        // Parse case: !0 case { @Zero => [@Zero] }  (missing @Succ)
        // !0 refers to the variable at index 0 (the most recent variable, n)
        let case_stx = parse(&db, "!0 case { @Zero => [@Zero] }");
        let Syntax::Case(case) = case_stx.as_ref() else {
            panic!("Expected Case syntax");
        };

        // Check should fail with NonExhaustiveMatch
        let result = type_check_case(&mut env, case, &nat_ty);
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
        let db = TestDatabase::default();
        let global = make_vec_global(&db);
        let mut env = make_env(&db, &global);

        // Push a : UniverseType at level 0
        let universe_ty: val::RcTy = val::Ty::universe_type_rc();
        env.push_var(universe_ty.clone());
        let _universe_code: RcValue = Value::UniverseCode(0).into();
        let a = Value::variable_rc(Level::new(0), universe_ty);

        // **PHASE 9**: Push v : Vec a @Zero (decoded) at level 1
        let zero = Value::data_constructor_rc("Zero".into_with_db(&db), vec![]);
        let vec_a_zero =
            Value::type_constructor_rc("Vec".into_with_db(&db), vec![a.clone(), zero.clone()]);
        let vec_ty = crate::eval::decode_type_code(&global, &vec_a_zero).expect("should decode");
        env.push_var(vec_ty);

        // Parse case: !0 case { @VNil => [@Zero] }
        // !0 refers to the variable at index 0 (the most recent variable, v)
        // This should be exhaustive because @VCons is impossible at index @Zero
        let case_stx = parse(&db, "!0 case { @VNil => [@Zero] }");
        let Syntax::Case(case) = case_stx.as_ref() else {
            panic!("Expected Case syntax");
        };

        // Check should succeed - @VCons is unreachable, only @VNil is required
        let nat_code = Value::type_constructor_rc("Nat".into_with_db(&db), vec![]);
        let nat_ty = crate::eval::decode_type_code(&global, &nat_code).expect("should decode");
        let result = type_check_case(&mut env, case, &nat_ty);
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
        let db = TestDatabase::default();
        let global = make_vec_global(&db);
        let mut env = make_env(&db, &global);

        // Push a : UniverseType at level 0
        let universe_ty: val::RcTy = val::Ty::universe_type_rc();
        env.push_var(universe_ty.clone());
        let _universe_code: RcValue = Value::UniverseCode(0).into();
        let a = Value::variable_rc(Level::new(0), universe_ty);

        // **PHASE 9**: Push n : Nat (decoded) at level 1
        let nat_code = Value::type_constructor_rc("Nat".into_with_db(&db), vec![]);
        let nat_ty = crate::eval::decode_type_code(&global, &nat_code).expect("should decode");
        env.push_var(nat_ty.clone());
        let n = Value::variable_rc(Level::new(1), nat_ty.clone());

        // Push v : Vec a n (decoded) at level 2
        let vec_a_n =
            Value::type_constructor_rc("Vec".into_with_db(&db), vec![a.clone(), n.clone()]);
        let vec_ty = crate::eval::decode_type_code(&global, &vec_a_n).expect("should decode");
        env.push_var(vec_ty);

        // Parse case: !0 case { @VNil => [@Zero] }  (missing @VCons)
        // !0 refers to the variable at index 0 (the most recent variable, v)
        let case_stx = parse(&db, "!0 case { @VNil => [@Zero] }");
        let Syntax::Case(case) = case_stx.as_ref() else {
            panic!("Expected Case syntax");
        };

        // Check should fail - both @VNil and @VCons are required when index is a variable
        let result = type_check_case(&mut env, case, &nat_ty);
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
    #[ignore = "PHASE 9: Eq type synthesis requires eq.ty to synthesize, but type codes are check-only after Strong Tarski"]
    fn test_check_eq_type() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // **PHASE 9 ISSUE**: Both type_check_eq and type_synth_eq call type_synth(eq.ty),
        // but type codes like BitCode are check-only. This test is fundamentally incompatible
        // with the Strong Tarski design where codes don't synthesize.
        // TODO: Either redesign Eq to work with check-only codes, or require annotations
        let eq = Syntax::eq_rc(
            Rc::new(Syntax::BitCode),
            Syntax::zero_rc(),
            Syntax::zero_rc(),
        );

        let u0_ty = val::Ty::universe_rc(0);
        let result = type_check(&mut env, &eq, &u0_ty);
        assert!(result.is_ok(), "type_check Eq against Universe(0) failed: {:?}", result.err());
    }

    #[test]
    fn test_check_refl() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // **PHASE 9**: refl : SignalEl(Eq U0 U0 U0)
        // EqType is a VALUE, not a type code, so we wrap it in SignalEl
        let refl = parse(&db, "refl");
        let eq_value = eval_str(&db, &global, "Eq U0 U0 U0");
        let eq_ty = val::Ty::signal_el_rc(eq_value);
        let result = type_check(&mut env, &refl, &eq_ty);
        assert!(result.is_ok(), "type_check failed: {:?}", result.err());
    }

    #[test]
    fn test_check_refl_fails_on_different_endpoints() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // **PHASE 9**: refl : SignalEl(Eq U0 U0 U1) should fail (endpoints don't match)
        let refl = parse(&db, "refl");
        let eq_value = eval_str(&db, &global, "Eq U0 U0 U1");
        let eq_ty = val::Ty::signal_el_rc(eq_value);
        assert!(type_check(&mut env, &refl, &eq_ty).is_err());
    }

    #[test]
    #[ignore] // TODO: Fix transport motive to use proper semantic Pi types with El(U0) domain
    fn test_check_transport() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // Test: transport along an equality of types
        // Context: [A : U0, B : U0, h : Eq U0 A B, x : A]
        // Term: transport [%0 -> %0] %h %x : B
        // The motive [%0 -> %0] is the identity function on types
        // **PHASE 9**: This transports a value x : A to a value of type B

        let u0_code: RcValue = Value::UniverseCode(0).into();

        // Push A : Universe(0) - a small type
        let u0_ty = val::Ty::universe_rc(0);
        let a = env.push_var(u0_ty.clone());

        // Push B : Universe(0) - another small type
        let b = env.push_var(u0_ty);

        // Push h : Eq U0 A B (decoded as EqType)
        let eq_code = Value::eq_rc(u0_code.clone(), a.clone(), b.clone());
        let eq_ty = crate::eval::decode_type_code(&global, &eq_code).expect("should decode EqType");
        env.push_var(eq_ty);

        // Push x : A (decoded from type code)
        let a_ty = crate::eval::decode_type_code(&global, &a).expect("should decode");
        env.push_var(a_ty);

        // Construct: transport %0 to (λ %y → %y) by %1
        // Parse at depth 4 since we have 4 variables in scope (A, B, h, x)
        // %0 = x (index 0), %1 = h (index 1), %2 = B (index 2), %3 = A (index 3)
        // The motive (λ %y → %y) is the identity function on types
        let transport =
            syn::parse::parse_syntax_at_depth(&db, "transport %0 to λ %y → %y by %1", 4)
                .expect("should parse");

        // Synthesize the type - should be B (decoded)
        let result = type_synth(&mut env, &transport);
        assert!(result.is_ok(), "type_synth failed: {:?}", result.err());

        let synth_ty = result.unwrap();
        // The synthesized type should be equal to B (decoded)
        let b_ty = crate::eval::decode_type_code(&global, &b).expect("should decode");
        assert!(
            equal::types_equal(
                &global,
                &env.values.transparent,
                env.depth(),
                &synth_ty,
                &b_ty
            ),
            "Expected type El(B), got {:?}",
            synth_ty
        );
    }

    #[test]
    #[ignore] // TODO: Fix transport motive to use proper semantic Pi types with El(U0) domain
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

        use crate::test_utils::load_prelude;

        let db = TestDatabase::default();

        // Set up Nat and Vec type constructors via prelude
        let prelude = "tcon @Nat : -> U0 where dcon @Z : #[@Nat]; tcon @Vec (%a : U0) : (%n : #[@Nat]) -> U0 where dcon @VNil : #[@Vec %a [@Z]];";
        let global = load_prelude(&db, prelude);

        let mut env = make_env(&db, &global);
        let nat_id = "Nat".into_with_db(&db);
        let vec_id = "Vec".into_with_db(&db);
        let u0_code: RcValue = Value::UniverseCode(0).into();
        let nat_code = Value::type_constructor_rc(nat_id, vec![]);

        // Context:
        // A : El(U0) - a small type
        // n : El(Nat)
        // **PHASE 9**: Decoded types
        // m : Nat (decoded)
        // eq_proof : Eq Nat n m (decoded as EqType)
        // v : Vec A n (decoded)

        // Push A : Universe(0) - a small type
        let u0_ty = val::Ty::universe_rc(0);
        let a = env.push_var(u0_ty);

        // Push n : Nat (decoded)
        let nat_ty = crate::eval::decode_type_code(&global, &nat_code).expect("should decode");
        let n = env.push_var(nat_ty.clone());

        // Push m : Nat (decoded)
        let m = env.push_var(nat_ty);

        // Push eq_proof : Eq Nat n m (decoded as EqType)
        let eq_code = Value::eq_rc(nat_code.clone(), n.clone(), m.clone());
        let eq_ty = crate::eval::decode_type_code(&global, &eq_code).expect("should decode EqType");
        env.push_var(eq_ty);

        // Push v : Vec A n (decoded)
        let vec_a_n = Value::type_constructor_rc(vec_id, vec![a.clone(), n.clone()]);
        let vec_ty = crate::eval::decode_type_code(&global, &vec_a_n).expect("should decode");
        env.push_var(vec_ty);

        // Now we want to construct a term of type Vec A m
        // We use transport with a motive that maps a Nat to Vec A (that Nat)
        //
        // transport v to (λ i → Vec A i) by eq_proof : Vec A m
        //
        // At depth 5: %0 = v, %1 = eq_proof, %2 = m, %3 = n, %4 = A

        let transport_term = syn::parse::parse_syntax_at_depth(
            &db,
            "transport %0 to λ %i → #[@Vec %4 %i] by %1",
            5,
        )
        .expect("should parse");

        // Type check: should synthesize Vec A m
        let result = type_synth(&mut env, &transport_term);
        assert!(result.is_ok(), "type_synth failed: {:?}", result.err());

        let synth_ty = result.unwrap();

        // **PHASE 9**: The synthesized type should be Vec A m (decoded)
        let expected_code = Value::type_constructor_rc(vec_id, vec![a.clone(), m.clone()]);
        let expected_ty = crate::eval::decode_type_code(&global, &expected_code).expect("should decode");

        assert!(
            equal::types_equal(
                &global,
                &env.values.transparent,
                env.depth(),
                &synth_ty,
                &expected_ty
            ),
            "Expected type El(Vec A m), got {:?}",
            synth_ty
        );

        // This demonstrates that transport successfully performs the type refinement
        // that would occur when pattern matching on an equality proof!
    }

    // ========== Let expression tests ==========

    #[test]
    fn test_let_simple_synth() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // let %x : U0 = U0; %x
        // Should synthesize to El(U1) (since U0 : El(U1))
        let let_expr = parse(&db, "let %x : U1 = U0; %x");
        let result = type_synth(&mut env, &let_expr);
        assert!(result.is_ok(), "type_synth failed: {:?}", result.err());

        let synth_ty = result.unwrap();
        // **PHASE 9**: Type is Universe(1) (decoded)
        match synth_ty.as_ref() {
            val::Ty::Universe(level) => assert_eq!(*level, 1),
            other => panic!("Expected Universe(1), got {:?}", other),
        }
    }

    #[test]
    fn test_let_simple_check() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // **PHASE 9**: let %x : U0 = U0; %x : Universe(1)
        let let_expr = parse(&db, "let %x : U1 = U0; %x");
        let u1_ty = val::Ty::universe_rc(1);
        let result = type_check(&mut env, &let_expr, &u1_ty);
        assert!(result.is_ok(), "type_check failed: {:?}", result.err());
    }

    #[test]
    fn test_let_body_uses_binding() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // let %A : U1 = U0; %A
        // The body references the let-bound variable
        let let_expr = parse(&db, "let %A : U1 = U0; %A");
        let result = type_synth(&mut env, &let_expr);
        assert!(result.is_ok(), "type_synth failed: {:?}", result.err());

        let synth_ty = result.unwrap();
        // **PHASE 9**: Type is Universe(1) (decoded)
        match synth_ty.as_ref() {
            val::Ty::Universe(level) => assert_eq!(*level, 1),
            other => panic!("Expected Universe(1), got {:?}", other),
        }
    }

    #[test]
    fn test_let_nested() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // let %A : U1 = U0; let %B : U1 = %A; %B
        let let_expr = parse(&db, "let %A : U1 = U0; let %B : U1 = %A; %B");
        let result = type_synth(&mut env, &let_expr);
        assert!(result.is_ok(), "type_synth failed: {:?}", result.err());

        let synth_ty = result.unwrap();
        // **PHASE 9**: Type is Universe(1) (decoded)
        match synth_ty.as_ref() {
            val::Ty::Universe(level) => assert_eq!(*level, 1),
            other => panic!("Expected Universe(1), got {:?}", other),
        }
    }

    #[test]
    #[ignore = "PHASE 9: Eq type synthesis requires eq.ty to synthesize, but type codes are check-only after Strong Tarski"]
    fn test_let_delta_reduction_in_equality() {
        // CRITICAL TEST: This is the test case from the design document
        // let y = U0; let h : Eq U1 U0 y = refl;
        // This tests that δ-reduction works correctly in conversion checking
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // **PHASE 9 ISSUE**: The Eq type annotation "Eq U1 U0 %y" requires U1 to synthesize,
        // but universe codes are check-only. This test requires a redesign of Eq to work
        // with check-only type codes, or require explicit annotations.
        // TODO: Redesign Eq to handle check-only codes
        let let_expr = parse(&db, "let %y : U1 = (U0 : U1); let %h : Eq U1 U0 %y = refl; %h");
        let result = type_synth(&mut env, &let_expr);
        assert!(
            result.is_ok(),
            "δ-reduction test failed: {:?}",
            result.err()
        );

        // **PHASE 9**: The type should be ModuleEl(EqType(...)) after δ-reduction
        // EqType is a module-level type, so it wraps in ModuleEl
        let synth_ty = result.unwrap();
        match synth_ty.as_ref() {
            val::Ty::ModuleEl(code) => {
                match code.as_ref() {
                    Value::EqType(_) => {
                        // Success! The equality type code was synthesized correctly
                    }
                    other => panic!("Expected EqType, got {:?}", other),
                }
            }
            other => panic!("Expected ModuleEl(EqType), got {:?}", other),
        }
    }

    #[test]
    fn test_let_with_universe_values() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // let %T : U1 = U0; let %x : U1 = %T; %x
        // Chain of let bindings with universe values
        let let_expr = parse(&db, "let %T : U1 = U0; let %x : U1 = %T; %x");
        let result = type_synth(&mut env, &let_expr);
        assert!(result.is_ok(), "type_synth failed: {:?}", result.err());

        let synth_ty = result.unwrap();
        // **PHASE 9**: Type is Universe(1) (decoded)
        match synth_ty.as_ref() {
            val::Ty::Universe(level) => assert_eq!(*level, 1),
            other => panic!("Expected Universe(1), got {:?}", other),
        }
    }

    #[test]
    fn test_let_type_annotation_checked() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // let %x : Bit = U0; %x
        // This should fail because U0 is not a Bit
        let let_expr = parse(&db, "let %x : Bit = U0; %x");
        let result = type_synth(&mut env, &let_expr);
        assert!(result.is_err(), "Expected type error, but got success");
    }

    #[test]
    fn test_let_in_lambda_with_pi_type() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // **PHASE 9**: λ %A → let %B : U0 = %A; %B : Pi(A : Universe(0), Universe(0))
        // Let can appear in lambda bodies, and we check against a semantic Pi type
        let lam_expr = parse(&db, "λ %A → let %B : U0 = %A; %B");
        let domain_ty = val::Ty::universe_rc(0);
        // The codomain is non-dependent, so the syntactic body uses syn::Ty::El
        let codomain_syn = syn::Ty::el_rc(Rc::new(Syntax::UniverseCode(0)));
        let ty_closure = val::TyClosure::new(val::LocalEnv::new(), codomain_syn);
        let pi_ty = val::Ty::pi_rc(domain_ty, Icit::Explicit, ty_closure);
        let result = type_check(&mut env, &lam_expr, &pi_ty);
        assert!(result.is_ok(), "type_check failed: {:?}", result.err());
    }

    #[test]
    fn test_let_in_lambda_body() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // **PHASE 9**: λ %x → let %y : U0 = %x; %y : Pi(x : Universe(0), Universe(0))
        // Let can appear in lambda bodies
        let lam_expr = parse(&db, "λ %x → let %y : U0 = %x; %y");
        let domain_ty = val::Ty::universe_rc(0);
        // The codomain is non-dependent, so the syntactic body uses syn::Ty::El
        let codomain_syn = syn::Ty::el_rc(Rc::new(Syntax::UniverseCode(0)));
        let ty_closure = val::TyClosure::new(val::LocalEnv::new(), codomain_syn);
        let pi_ty = val::Ty::pi_rc(domain_ty, Icit::Explicit, ty_closure);
        let result = type_check(&mut env, &lam_expr, &pi_ty);
        assert!(result.is_ok(), "type_check failed: {:?}", result.err());
    }

    // ========== Universe Level Checking Tests ==========

    #[test]
    fn test_pi_universe_max_rule() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // ∀ (%x : U0) → U0 should have type El(U1) (max(0, 0) = 0, so Pi : U1)
        let pi_expr: RcSyntax = Syntax::PiCode(
            Syntax::UniverseCode(0).into(),
            Icit::Explicit,
            Binding::new(Name::anonymous(&db), Syntax::UniverseCode(0).into()),
        )
        .into();
        let u1_ty = val::Ty::universe_rc(1);
        let result = type_check(&mut env, &pi_expr, &u1_ty);
        assert!(result.is_ok(), "Pi (U0 -> U0) should be in U1");

        // **PHASE 9**: ∀ (%x : U0) → U1 should have type Universe(2) (max(0, 1) = 1, so Pi : U2)
        let pi_expr: RcSyntax = Syntax::PiCode(
            Syntax::UniverseCode(0).into(),
            Icit::Explicit,
            Binding::new(Name::anonymous(&db), Syntax::UniverseCode(1).into()),
        )
        .into();
        let u2_ty = val::Ty::universe_rc(2);
        let result = type_check(&mut env, &pi_expr, &u2_ty);
        assert!(result.is_ok(), "Pi (U0 -> U1) should be in U2");

        // ∀ (%x : U1) → U0 should have type Universe(2) (max(1, 0) = 1, so Pi : U2)
        let pi_expr: RcSyntax = Syntax::PiCode(
            Syntax::UniverseCode(1).into(),
            Icit::Explicit,
            Binding::new(Name::anonymous(&db), Syntax::UniverseCode(0).into()),
        )
        .into();
        let u2_ty = val::Ty::universe_rc(2);
        let result = type_check(&mut env, &pi_expr, &u2_ty);
        assert!(result.is_ok(), "Pi (U1 -> U0) should be in U2");
    }

    #[test]
    fn test_pi_universe_cumulativity() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // **PHASE 9**: ∀ (%x : U0) → U0 can be checked against Universe(2) (cumulativity: U1 <= U2)
        let pi_expr: RcSyntax = Syntax::PiCode(
            Syntax::UniverseCode(0).into(),
            Icit::Explicit,
            Binding::new(Name::anonymous(&db), Syntax::UniverseCode(0).into()),
        )
        .into();
        let u2_ty = val::Ty::universe_rc(2);
        let result = type_check(&mut env, &pi_expr, &u2_ty);
        assert!(
            result.is_ok(),
            "Pi (U0 -> U0) should be checkable against U2 (cumulativity)"
        );
    }

    #[test]
    fn test_pi_universe_level_too_low_fails() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // **PHASE 9**: ∀ (%x : U0) → U1 should NOT be checkable against Universe(1)
        // (max(0, 1) = 1, so Pi : U2, but we're checking against U1)
        let pi_expr: RcSyntax = Syntax::PiCode(
            Syntax::UniverseCode(0).into(),
            Icit::Explicit,
            Binding::new(Name::anonymous(&db), Syntax::UniverseCode(1).into()),
        )
        .into();
        let u1_ty = val::Ty::universe_rc(1);
        let result = type_check(&mut env, &pi_expr, &u1_ty);
        assert!(
            result.is_err(),
            "Pi (U0 -> U1) should NOT be in U1 (needs U2)"
        );
    }

    #[test]
    fn test_universe_synthesis_increments() {
        let db = TestDatabase::default();
        let global = val::GlobalEnv::new(&db);
        let mut env = make_env(&db, &global);

        // With check-only type codes, we must annotate universe codes
        // U0 : UniverseType (the meta-level classifier)
        let u0: RcSyntax =
            Syntax::check_rc(syn::Ty::universe_type_rc(), Syntax::UniverseCode(0).into());
        let ty = type_synth(&mut env, &u0).expect("should synthesize");
        match ty.as_ref() {
            val::Ty::UniverseType => {} // Correct!
            _ => panic!("Expected UniverseType, got {:?}", ty),
        }

        // U5 : UniverseType
        let u5: RcSyntax =
            Syntax::check_rc(syn::Ty::universe_type_rc(), Syntax::UniverseCode(5).into());
        let ty = type_synth(&mut env, &u5).expect("should synthesize");
        match ty.as_ref() {
            val::Ty::UniverseType => {} // Correct!
            _ => panic!("Expected UniverseType, got {:?}", ty),
        }
    }
}
