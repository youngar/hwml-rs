use crate::common::Level;
use crate::equal;
use crate::eval;
use crate::syn as stx;
use crate::syn;
use crate::syn::Syntax;
use crate::val;
use crate::val::{Closure, Environment, LocalEnv, Value};
use std::rc::Rc;

#[derive(Clone, Debug)]
pub struct TCEnvironment<'db, 'g> {
    pub values: val::Environment<'db, 'g>,
    pub types: Vec<Rc<Value<'db>>>,
}

impl<'db, 'g> TCEnvironment<'db, 'g> {
    fn type_of(&self, level: Level) -> &Rc<Value<'db>> {
        let index: usize = level.into();
        &self.types[index]
    }

    fn var_type(&self, var: &stx::Variable) -> &Rc<Value<'db>> {
        let level = var.index.to_level(self.depth());
        self.type_of(level)
    }

    fn value_of(&self, level: Level) -> &Rc<Value<'db>> {
        self.values.get(level)
    }

    fn var_value(&self, var: &stx::Variable) -> &Rc<Value<'db>> {
        let level = var.index.to_level(self.depth());
        self.value_of(level)
    }

    fn push(&mut self, value: Rc<Value<'db>>, ty: Rc<Value<'db>>) {
        self.values.push(value);
        self.types.push(ty);
    }

    pub fn push_var(&mut self, ty: Rc<Value<'db>>) -> Rc<Value<'db>> {
        let var = Rc::new(Value::variable(Level::new(self.depth()), ty.clone()));
        self.push(var.clone(), ty);
        var
    }

    fn pop(&mut self) {
        self.values.pop();
        self.types.pop();
    }

    fn truncate(&mut self, depth: usize) {
        self.values.truncate(depth);
        self.types.truncate(depth);
    }

    fn depth(&self) -> usize {
        self.values.depth()
    }

    fn extend_vars<T>(&mut self, types: T)
    where
        T: IntoIterator<Item = Rc<Value<'db>>>,
    {
        for ty in types {
            self.values.push_var(ty.clone());
            self.types.push(ty);
        }
    }
}

#[derive(Debug, Clone)]
pub enum Error<'db> {
    /// Cannot synthesize a type.
    BadSynth {
        tm: Rc<Syntax<'db>>,
    },
    /// Bad type.
    BadType {
        tm: Rc<Syntax<'db>>,
    },
    /// Bad elimination.
    BadElim {
        tm: Rc<Syntax<'db>>,
        ty_got: Rc<Value<'db>>,
    },
    /// Bad constructor.
    BadCtor {
        tm: Rc<Syntax<'db>>,
        ty_exp: Rc<Value<'db>>,
    },
    /// Inferred a type that did not match the expected type.
    BadCheck {
        tm: Rc<Syntax<'db>>,
        ty_exp: Rc<Value<'db>>,
        ty_got: Rc<Value<'db>>,
    },
    EvaluationFailure(eval::Error),
    LookupError(val::LookupError<'db>),
    MatchOnNonDatatype(Rc<Value<'db>>),
}

impl<'db> From<eval::Error> for Error<'db> {
    fn from(e: eval::Error) -> Self {
        Error::EvaluationFailure(e)
    }
}

use std::result::Result;

/// Evaluate a syntactic term to a semantic value.
fn eval<'db, 'g>(
    env: &TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
) -> Result<Rc<Value<'db>>, Error<'db>> {
    let mut sem_env = env.values.clone();
    eval::eval(&mut sem_env, term).map_err(Error::EvaluationFailure)
}

/// Adaptor for running a closure from the semantic domain.
fn run_closure<'db, 'g, T>(
    env: &TCEnvironment<'db, 'g>,
    closure: &val::Closure<'db>,
    args: T,
) -> Result<Rc<Value<'db>>, Error<'db>>
where
    T: IntoIterator<Item = Rc<Value<'db>>>,
{
    eval::run_closure(&env.values.global, closure, args).map_err(Error::EvaluationFailure)
}

/// Synthesize (infer) types for variables and elimination forms.
pub fn type_synth<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
) -> Result<Rc<Value<'db>>, Error<'db>> {
    match term {
        Syntax::Variable(variable) => type_synth_variable(env, variable),
        Syntax::Constant(constant) => type_synth_constant(env, constant),
        Syntax::Prim(prim) => type_synth_prim(env, prim),
        Syntax::Check(check) => type_synth_check(env, check),
        Syntax::Application(application) => type_synth_application(env, application),
        Syntax::Case(case) => type_synth_case(env, case),
        Syntax::Metavariable(metavariable) => type_synth_metavariable(env, metavariable),

        // Universe: U_n : U_(n+1)
        // For simplicity, we use predicative universes where U_n : U_(n+1)
        Syntax::Universe(universe) => {
            let current_level: usize = universe.level.into();
            let next_level = crate::common::UniverseLevel::new(current_level + 1);
            Ok(Rc::new(Value::universe(next_level)))
        }

        // HardwareUniverse constructs - Lift is the only one that can be synthesized
        // Bit, HArrow, and Quote need to be checked against expected types
        Syntax::Lift(lift) => type_synth_lift(env, lift),

        _ => Err(Error::BadSynth {
            tm: Rc::new(term.clone()),
        }),
    }
}

/// Synthesize a type for a variable.
pub fn type_synth_variable<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    variable: &syn::Variable<'db>,
) -> Result<Rc<Value<'db>>, Error<'db>> {
    // Pull the type from the typing environment.
    Ok(env.var_type(variable).clone())
}

/// Synthesize the type of a constant by looking it up in the global environment.
pub fn type_synth_constant<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    constant: &syn::Constant<'db>,
) -> Result<Rc<Value<'db>>, Error<'db>> {
    // Look up the constant in the global environment
    let constant_info = env
        .values
        .global
        .constant(constant.name)
        .map_err(Error::LookupError)?;

    // Evaluate the type to get a Value
    eval(env, &constant_info.ty)
}

/// Synthesize the type of a primitive by looking it up in the global environment.
/// Primitives have types but no definitions.
pub fn type_synth_prim<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    prim: &syn::Prim<'db>,
) -> Result<Rc<Value<'db>>, Error<'db>> {
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
) -> Result<Rc<Value<'db>>, Error<'db>> {
    // Check that the type is a valid meta-level type (not a hardware type)
    check_meta_type(env, &check.ty)?;
    let ty = eval(env, &check.ty)?;
    type_check(env, &check.term, &ty)?;
    Ok(ty)
}

/// Synthesize the type of a metavariable.
pub fn type_synth_metavariable<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    metavariable: &syn::Metavariable<'db>,
) -> Result<Rc<Value<'db>>, Error<'db>> {
    // Lookup the metavariable info in the global environment.
    let meta_info = env
        .values
        .global
        .metavariable(metavariable.id)
        .map_err(|_| Error::BadSynth {
            tm: Rc::new(Syntax::Metavariable(metavariable.clone())),
        })?;

    // The metavariable has a telescope of argument types.
    // We need to check that the substitution has the right number of arguments.
    if metavariable.substitution.len() != meta_info.arguments.len() {
        return Err(Error::BadSynth {
            tm: Rc::new(Syntax::Metavariable(metavariable.clone())),
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
        };
        let expected_ty = eval::eval(&mut temp_env, arg_ty).map_err(|_| Error::BadSynth {
            tm: Rc::new(Syntax::Metavariable(metavariable.clone())),
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
    };
    let meta_ty = eval::eval(&mut temp_env, &meta_info.ty).map_err(|_| Error::BadSynth {
        tm: Rc::new(Syntax::Metavariable(metavariable.clone())),
    })?;

    Ok(meta_ty)
}

/// Synthesize the type of a function application.
pub fn type_synth_application<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    application: &syn::Application<'db>,
) -> Result<Rc<Value<'db>>, Error<'db>> {
    // First synthesize the type of the term being applied.
    let fun_ty = type_synth(env, &application.function)?;

    // Ensure that the applied term is a function `(x : src) -> tgt(x)`.
    let Value::Pi(pi) = &*fun_ty else {
        return Err(Error::BadElim {
            tm: Rc::new(Syntax::Application(application.clone())),
            ty_got: fun_ty,
        });
    };

    // Check the argument against the source type of the function.
    type_check(env, &application.argument, &*pi.source)?;

    // The overall type is determined by substituting the argument into the target type.
    let arg = eval(env, &application.argument)?;
    run_closure(&env, &pi.target, [arg])
}

/// Synthesize the type of a case expression.
pub fn type_synth_case<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    case: &syn::Case<'db>,
) -> Result<Rc<Value<'db>>, Error<'db>> {
    // First synthesize the type of the scrutinee.
    let scrutinee_ty = type_synth(env, &case.expr)?;

    let motive_clos = Closure::new(env.values.local.clone(), case.motive.clone());

    // Ensure that the term being matched is a datatype.
    let Value::TypeConstructor(type_constructor) = &*scrutinee_ty else {
        return Err(Error::BadElim {
            tm: Rc::new(Syntax::Case(case.clone())),
            ty_got: scrutinee_ty,
        });
    };
    let constructor = type_constructor.constructor;

    // Get the type constructor info.
    let type_info = env
        .values
        .global
        .type_constructor(type_constructor.constructor)
        .map_err(Error::LookupError)?;

    // Get the number of parameters.
    let num_parameters = type_info.num_parameters();

    // Create an array of parameters.
    let parameters = type_constructor
        .iter()
        .take(num_parameters)
        .cloned()
        .collect::<Vec<_>>();

    // First, create variables for the indices.
    let index_bindings = type_info.indices().to_vec();
    let index_telescope = crate::syn::Telescope::from(index_bindings);
    let index_tys = eval::eval_telescope(env.values.global, parameters.clone(), &index_telescope)?;

    // Check that the motive returns a type.
    // TODO: we really need to check the arity of the motive.
    {
        // Push each index in to the environment, while building up
        let depth = env.depth();
        let mut scrutinee_ty_args = parameters.clone();
        let mut motive_args = Vec::new();
        for ty in index_tys.types {
            let var = env.push_var(ty);
            scrutinee_ty_args.push(var.clone());
            motive_args.push(var);
        }

        // Create a variable for the scrutinee.
        let scrutinee_ty = Rc::new(Value::type_constructor(
            type_constructor.constructor,
            scrutinee_ty_args,
        ));
        let scrutinee_var = env.push_var(scrutinee_ty);
        motive_args.push(scrutinee_var);

        // Check that the motive returns a type.
        check_type(env, &case.motive)?;
        env.truncate(depth);
    }

    // Check the types of the branches.
    for branch in &case.branches {
        let data_info = env
            .values
            .global
            .data_constructor(branch.constructor)
            .map_err(Error::LookupError)?;

        let depth = env.depth();

        // Create fresh variables for the data constructor arguments.
        let dcon_arg_tys =
            eval::eval_telescope(env.values.global, parameters.clone(), &data_info.arguments)?;
        let mut dcon_args: Vec<Rc<Value<'_>>> = Vec::new();
        for ty in dcon_arg_tys.types {
            let var = env.push_var(ty);
            dcon_args.push(var);
        }

        // Create the data constructor value.
        let dcon_val = Rc::new(Value::data_constructor(constructor, dcon_args.clone()));
        let mut branch_motive_args =
            type_constructor.arguments[type_info.num_parameters()..].to_vec();
        branch_motive_args.push(dcon_val);

        // Evaluate the motive to get the type of the branch body.
        let branch_ty = eval::run_closure(env.values.global, &motive_clos, branch_motive_args)?;

        // Check the branch body against the motive.
        type_check(env, &branch.body, &branch_ty)?;

        // Reset the environment.
        env.truncate(depth);
    }

    // Check that the scrutinee is the right type.
    //let scrutinee_ty = type_synth(env, &case.expr)?;
    let Value::TypeConstructor(type_constructor) = &*scrutinee_ty else {
        return Err(Error::MatchOnNonDatatype(scrutinee_ty));
    };

    // We will evaluate the motive, reading the indices off of the type of the
    // scrutinee, and finally passing in the scrutinee itself.
    let scrutinee = eval(env, &case.expr)?;
    let mut motive_args = type_constructor.arguments[type_info.num_parameters()..].to_vec();
    motive_args.push(scrutinee);
    let ty = eval::run_closure(env.values.global, &motive_clos, motive_args)?;
    Ok(ty)
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
        Syntax::TypeConstructor(tc) => type_check_type_constructor(env, tc, ty),
        Syntax::DataConstructor(dc) => type_check_data_constructor(env, dc, ty),

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

        _ => type_check_synth_term(env, term, ty),
    }
}

/// Typecheck a pi term.
fn type_check_pi<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    pi: &syn::Pi<'db>,
    ty: &Value<'db>,
) -> Result<(), Error<'db>> {
    // The expected type of a pi must be a universe.
    let Value::Universe(_) = ty else {
        return Err(Error::BadCtor {
            tm: Rc::new(Syntax::Pi(pi.clone())),
            ty_exp: Rc::new(ty.clone()),
        });
    };

    // Check that the source type is valid.
    check_type(env, &pi.source)?;

    // Evaluate the source type to a value.
    let sem_source_ty = eval(env, &pi.source)?;

    // Check that the target type is of the same universe as the pi.
    env.push_var(sem_source_ty);
    let result = type_check(env, &pi.target, ty);
    env.pop();
    result
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
            let var = Rc::new(Value::variable(Level::new(env.depth()), source.clone()));
            let target = run_closure(env, target_closure, [var.clone()])?;
            env.push(var, source.clone());
            let r = type_check(env, &lam.body, &target);
            env.pop();
            r
        }
        _ => Err(Error::BadCtor {
            tm: Rc::new(Syntax::Lambda(lam.clone())),
            ty_exp: Rc::new(ty.clone()),
        }),
    }
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
                    tm: Rc::new(Syntax::TypeConstructor(tcon.clone())),
                });
            }

            let mut ty_env = val::Environment {
                global: env.values.global,
                local: val::LocalEnv::new(),
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
            tm: Rc::new(Syntax::TypeConstructor(tcon.clone())),
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
            match equal::type_equiv(env.values.global, env.depth(), ty_exp, &ty_got) {
                Ok(_) => Ok(()),
                Err(_) => Err(Error::BadCheck {
                    tm: Rc::new(Syntax::DataConstructor(dc.clone())),
                    ty_exp: Rc::new(ty_exp.clone()),
                    ty_got,
                }),
            }
        }
        _ => Err(Error::BadCtor {
            tm: Rc::new(Syntax::DataConstructor(dc.clone())),
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
) -> Result<Rc<Value<'db>>, Error<'db>> {
    // Check that the inner term is a valid hardware type
    check_hwtype(env, &lift.ty)?;

    // ^ht : Type (at universe level 0)
    Ok(Rc::new(Value::universe(crate::common::UniverseLevel::new(
        0,
    ))))
}

fn type_check_bit<'db, 'g>(
    _env: &mut TCEnvironment<'db, 'g>,
    ty: &Value<'db>,
) -> Result<(), Error<'db>> {
    match ty {
        Value::SignalUniverse(_) => Ok(()),
        _ => Err(Error::BadCtor {
            tm: Rc::new(Syntax::Bit(syn::Bit::new())),
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
            tm: Rc::new(Syntax::HArrow(harrow.clone())),
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
            tm: Rc::new(Syntax::SLift(slift.clone())),
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
            tm: Rc::new(Syntax::MLift(mlift.clone())),
            ty_exp: Rc::new(ty.clone()),
        }),
    }
}

/// Check that `0` (Zero) is valid against the expected type.
/// Zero values can be checked against ^(Sig Bit) (a Lift containing an SLift of Bit).
fn type_check_zero<'db, 'g>(
    _env: &mut TCEnvironment<'db, 'g>,
    zero: &syn::Zero<'db>,
    ty: &Value<'db>,
) -> Result<(), Error<'db>> {
    // The expected type must be ^(Sig Bit), which is Lift(SLift(Bit))
    match ty {
        Value::Lift(lift) => match lift.ty.as_ref() {
            Value::SLift(slift) => match slift.ty.as_ref() {
                Value::Bit(_) => Ok(()),
                _ => Err(Error::BadCtor {
                    tm: Rc::new(Syntax::Zero(zero.clone())),
                    ty_exp: Rc::new(ty.clone()),
                }),
            },
            _ => Err(Error::BadCtor {
                tm: Rc::new(Syntax::Zero(zero.clone())),
                ty_exp: Rc::new(ty.clone()),
            }),
        },
        _ => Err(Error::BadCtor {
            tm: Rc::new(Syntax::Zero(zero.clone())),
            ty_exp: Rc::new(ty.clone()),
        }),
    }
}

/// Check that `1` (One) is valid against the expected type.
/// One values can be checked against ^(Sig Bit) (a Lift containing an SLift of Bit).
fn type_check_one<'db, 'g>(
    _env: &mut TCEnvironment<'db, 'g>,
    one: &syn::One<'db>,
    ty: &Value<'db>,
) -> Result<(), Error<'db>> {
    // The expected type must be ^(Sig Bit), which is Lift(SLift(Bit))
    match ty {
        Value::Lift(lift) => match lift.ty.as_ref() {
            Value::SLift(slift) => match slift.ty.as_ref() {
                Value::Bit(_) => Ok(()),
                _ => Err(Error::BadCtor {
                    tm: Rc::new(Syntax::One(one.clone())),
                    ty_exp: Rc::new(ty.clone()),
                }),
            },
            _ => Err(Error::BadCtor {
                tm: Rc::new(Syntax::One(one.clone())),
                ty_exp: Rc::new(ty.clone()),
            }),
        },
        _ => Err(Error::BadCtor {
            tm: Rc::new(Syntax::One(one.clone())),
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

// Synthesize a type for the term, then check for equality against the expected type.
pub fn type_check_synth_term<'db, 'g>(
    env: &mut TCEnvironment<'db, 'g>,
    term: &Syntax<'db>,
    ty1: &Value<'db>,
) -> Result<(), Error<'db>> {
    let ty2 = type_synth(env, term)?;
    match crate::equal::type_equiv(env.values.global, env.depth(), ty1, &ty2) {
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
        return check_module_type(env, &Syntax::HArrow(harrow.clone()));
    }

    // SLift/MLift (hardware types) are valid types - they live in HType
    if matches!(term, Syntax::SLift(_) | Syntax::MLift(_)) {
        return check_hwtype(env, term);
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
            tm: Rc::new(Syntax::TypeConstructor(tcon.clone())),
        });
    }

    let mut ty_env = val::Environment {
        global: env.values.global,
        local: val::LocalEnv::new(),
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
    use crate::ConstantId;
    use crate::Database;
    use hwml_support::FromWithDb;

    /// Helper to create a TCEnvironment with a GlobalEnv
    fn make_env<'db, 'g>(global: &'g val::GlobalEnv<'db>) -> TCEnvironment<'db, 'g> {
        TCEnvironment {
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
        let mut env = make_env(&global);

        // ^(^s Bit) - a lifted hardware type (Lift containing SLift containing Bit)
        let lift_bit = parse(&db, "^(^s Bit)");
        assert!(check_meta_type(&mut env, &lift_bit).is_ok());
    }

    /// Test that hardware types (Bit) are NOT valid meta-level types.
    #[test]
    fn test_hwtype_is_not_valid_meta_type() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&global);

        // Bit - a hardware type
        let bit = parse(&db, "Bit");
        assert!(check_meta_type(&mut env, &bit).is_err());
    }

    /// Test that Universe is a valid meta-level type.
    #[test]
    fn test_universe_is_valid_meta_type() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&global);

        // 𝒰0 should be accepted
        let u0 = parse(&db, "U0");
        assert!(check_meta_type(&mut env, &u0).is_ok());
    }

    /// Test that Pi types with valid meta-level source/target are valid.
    #[test]
    fn test_pi_is_valid_meta_type() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&global);

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
        let mut env = make_env(&global);

        let u0 = parse(&db, "U0");
        assert!(check_type(&mut env, &u0).is_ok());
    }

    /// Test that check_type accepts Pi types.
    #[test]
    fn test_check_type_accepts_pi() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&global);

        let pi = parse(&db, "forall (%x : U0) -> U0");
        assert!(check_type(&mut env, &pi).is_ok());
    }

    /// Test that check_type accepts Bit (signal type - lives in SignalUniverse).
    #[test]
    fn test_check_type_accepts_bit() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&global);

        // Bit is a signal type (SType), so it's a valid type
        let bit = parse(&db, "Bit");
        assert!(check_type(&mut env, &bit).is_ok());
    }

    /// Test that check_type accepts HArrow (module type).
    #[test]
    fn test_check_type_accepts_harrow() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&global);

        // ^s Bit -> ^s Bit : MType (module type with hardware type components)
        let harrow = parse(&db, "^s Bit -> ^s Bit");
        assert!(check_type(&mut env, &harrow).is_ok());
    }

    /// Test that check_type accepts Lift types.
    #[test]
    fn test_check_type_accepts_lift() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&global);

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
        let mut env = make_env(&global);

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
        let mut env = make_env(&global);

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
        let _db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&global);

        // Push a variable of type 𝒰0
        let u0_val = Rc::new(Value::universe(UniverseLevel::new(0)));
        env.push_var(u0_val.clone());

        // Variable %0 should have type 𝒰0
        // Note: We use manual AST construction here because the parser requires
        // named variables to be in its name context.
        let var = Syntax::variable_rc(crate::common::Index(0));
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

        let cid = |s: &str| ConstantId::from_with_db(&db, s);

        // Add constant @myConst : 𝒰0 = 𝒰0
        global.add_constant(
            cid("myConst"),
            val::ConstantInfo::new(parse(&db, "U0"), parse(&db, "U0")),
        );

        let mut env = make_env(&global);

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

        let cid = |s: &str| ConstantId::from_with_db(&db, s);

        // Add primitive $Nat : 𝒰0
        global.add_primitive(cid("Nat"), val::PrimitiveInfo::new(parse(&db, "U0")));

        let mut env = make_env(&global);

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
        let mut env = make_env(&global);

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
        let mut env = make_env(&global);

        // λ %x → %x : ∀ (%x : 𝒰0) → 𝒰0
        let lam = parse(&db, "λ %x -> %x");

        // Create the Pi type as a Value
        let u0_val = Rc::new(Value::universe(UniverseLevel::new(0)));
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
        let mut env = make_env(&global);

        let bit = parse(&db, "Bit");
        let signal_universe = Value::SignalUniverse(val::SignalUniverse::new());

        assert!(type_check(&mut env, &bit, &signal_universe).is_ok());
    }

    /// Test that HArrow checks against ModuleUniverse.
    #[test]
    fn test_check_harrow_against_module_universe() {
        let db = Database::default();
        let global = val::GlobalEnv::new();
        let mut env = make_env(&global);

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
        let mut env = make_env(&global);

        // Set up: we need a variable of Pi type
        // Create a function f : ∀ (%x : 𝒰0) → 𝒰0
        let u0_val = Rc::new(Value::universe(UniverseLevel::new(0)));
        let u0_syn = parse(&db, "U0");
        let pi_val = Rc::new(Value::Pi(val::Pi {
            source: u0_val.clone(),
            target: Closure::new(val::LocalEnv::new(), u0_syn),
        }));

        // Push f into the environment
        env.push_var(pi_val);

        // Now apply f to (^(^s Bit)) which has type 𝒰0
        // Note: We use manual AST construction for the variable reference
        // because the parser requires named variables to be in its name context.
        let lift_bit = parse(&db, "^(^s Bit)");
        let app = Syntax::application_rc(Syntax::variable_rc(crate::common::Index(0)), lift_bit);

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

        let _db = Database::default();
        let mut global = val::GlobalEnv::new();

        // Declare ?[0] : U0
        let meta_id = MetaVariableId(0);
        global.add_metavariable(meta_id, vec![], Syntax::universe_rc(UniverseLevel::new(0)));

        let mut env = make_env(&global);

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
        let meta_id = MetaVariableId(0);
        global.add_metavariable(
            meta_id,
            vec![Syntax::universe_rc(UniverseLevel::new(0))],
            Syntax::universe_rc(UniverseLevel::new(0)),
        );

        let mut env = make_env(&global);

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

        let _db = Database::default();
        let mut global = val::GlobalEnv::new();

        // Declare ?[0] (%x : U0) : U0 (expects 1 argument)
        let meta_id = MetaVariableId(0);
        global.add_metavariable(
            meta_id,
            vec![Syntax::universe_rc(UniverseLevel::new(0))],
            Syntax::universe_rc(UniverseLevel::new(0)),
        );

        let mut env = make_env(&global);

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
        let meta_id = MetaVariableId(0);
        global.add_metavariable(
            meta_id,
            vec![Syntax::lift_rc(Syntax::bit_rc())],
            Syntax::universe_rc(UniverseLevel::new(0)),
        );

        let mut env = make_env(&global);

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
        let meta_id = MetaVariableId(0);
        global.add_metavariable(
            meta_id,
            vec![
                Syntax::universe_rc(UniverseLevel::new(0)), // %A : U0
                Syntax::variable_rc(Index(0)),              // %x : %A (references %A)
            ],
            Syntax::universe_rc(UniverseLevel::new(0)),
        );

        let mut env = make_env(&global);

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
}
