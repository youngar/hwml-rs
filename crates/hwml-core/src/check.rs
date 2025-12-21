use itertools::DedupWithCount;

use crate::common::Level;
use crate::equal;
use crate::eval;
use crate::syn as stx;
use crate::syn;
use crate::syn::Syntax;
use crate::val;
use crate::val::Closure;
use crate::val::Value;
use std::rc::Rc;

pub struct TCEnvironment<'g, 'db> {
    pub globals: &'g val::GlobalEnv<'db>,
    pub values: val::Environment<'g, 'db>,
    pub types: Vec<Rc<Value<'db>>>,
}

impl<'g, 'db> TCEnvironment<'g, 'db> {
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

    fn push_var(&mut self, ty: Rc<Value<'db>>) -> Rc<Value<'db>> {
        let var = Rc::new(Value::variable(ty.clone(), Level::new(self.depth())));
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
fn eval<'g, 'db>(
    env: &TCEnvironment<'g, 'db>,
    term: &Syntax<'db>,
) -> Result<Rc<Value<'db>>, Error<'db>> {
    let mut sem_env = env.values.clone();
    eval::eval(&mut sem_env, term).map_err(Error::EvaluationFailure)
}

/// Adaptor for running a closure from the semantic domain.
fn run_closure<'g, 'db, T>(
    env: &TCEnvironment<'g, 'db>,
    closure: &val::Closure<'db>,
    args: T,
) -> Result<Rc<Value<'db>>, Error<'db>>
where
    T: IntoIterator<Item = Rc<Value<'db>>>,
{
    eval::run_closure(&env.values.global, closure, args).map_err(Error::EvaluationFailure)
}

/// Synthesize (infer) types for variables and elimination forms.
pub fn type_synth<'g, 'db>(
    env: &mut TCEnvironment<'g, 'db>,
    term: &Syntax<'db>,
) -> Result<Rc<Value<'db>>, Error<'db>> {
    match term {
        Syntax::Variable(variable) => type_synth_variable(env, variable),
        Syntax::Check(check) => type_synth_check(env, check),
        Syntax::Application(application) => type_synth_application(env, application),
        Syntax::Case(case) => type_synth_case(env, case),
        _ => Err(Error::BadSynth {
            tm: Rc::new(term.clone()),
        }),
    }
}

/// Synthesize a type for a variable.
pub fn type_synth_variable<'g, 'db>(
    env: &mut TCEnvironment<'g, 'db>,
    variable: &syn::Variable,
) -> Result<Rc<Value<'db>>, Error<'db>> {
    // Pull the type from the typing environment.
    Ok(env.var_type(variable).clone())
}

/// Synthesize the type of a term annotated with a type.
pub fn type_synth_check<'g, 'db>(
    env: &mut TCEnvironment<'g, 'db>,
    check: &syn::Check<'db>,
) -> Result<Rc<Value<'db>>, Error<'db>> {
    check_type(env, &check.ty)?;
    let ty = eval(env, &check.ty)?;
    type_check(env, &check.term, &ty)?;
    Ok(ty)
}

/// Synthesize the type of a function application.
pub fn type_synth_application<'g, 'db>(
    env: &mut TCEnvironment<'g, 'db>,
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
pub fn type_synth_case<'g, 'db>(
    env: &mut TCEnvironment<'g, 'db>,
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
pub fn type_check<'g, 'db>(
    env: &mut TCEnvironment<'g, 'db>,
    term: &Syntax<'db>,
    ty: &Value<'db>,
) -> Result<(), Error<'db>> {
    match term {
        Syntax::Pi(pi) => type_check_pi(env, pi, ty),
        Syntax::Lambda(lam) => type_check_lambda(env, lam, ty),
        Syntax::TypeConstructor(tc) => type_check_type_constructor(env, tc, ty),
        Syntax::DataConstructor(dc) => type_check_data_constructor(env, dc, ty),
        _ => type_check_synth_term(env, term, ty),
    }
}

/// Typecheck a pi term.
fn type_check_pi<'g, 'db>(
    env: &mut TCEnvironment<'g, 'db>,
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

fn type_check_lambda<'g, 'db>(
    env: &mut TCEnvironment<'g, 'db>,
    lam: &syn::Lambda<'db>,
    ty: &Value<'db>,
) -> Result<(), Error<'db>> {
    match ty {
        Value::Pi(val::Pi {
            source,
            target: target_closure,
        }) => {
            let var = Rc::new(Value::variable(source.clone(), Level::new(env.depth())));
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

fn type_check_type_constructor<'g, 'db>(
    env: &mut TCEnvironment<'g, 'db>,
    tcon: &syn::TypeConstructor<'db>,
    ty: &Value<'db>,
) -> Result<(), Error<'db>> {
    match ty {
        Value::Universe(u) => {
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

fn type_check_data_constructor<'g, 'db>(
    env: &mut TCEnvironment<'g, 'db>,
    dc: &syn::DataConstructor<'db>,
    ty_exp: &Value<'db>,
) -> Result<(), Error<'db>> {
    match ty_exp {
        Value::TypeConstructor(tc) => {
            let dc_info = env
                .globals
                .data_constructor(dc.constructor)
                .map_err(Error::LookupError)?;
            let tc_info = env
                .globals
                .type_constructor(tc.constructor)
                .map_err(Error::LookupError)?;

            let mut ty_env = val::Environment {
                global: env.globals,
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
            match equal::is_type_convertible(env.globals, env.depth(), ty_exp, &ty_got) {
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

// Synthesize a type for the term, then check for equality against the expected type.
pub fn type_check_synth_term<'g, 'db>(
    env: &mut TCEnvironment<'g, 'db>,
    term: &Syntax<'db>,
    ty1: &Value<'db>,
) -> Result<(), Error<'db>> {
    let ty2 = type_synth(env, term)?;
    match crate::equal::is_type_convertible(env.globals, env.depth(), ty1, &ty2) {
        Ok(()) => Ok(()),
        Err(_) => Err(Error::BadCheck {
            tm: Rc::new(term.clone()),
            ty_got: ty2,
            ty_exp: Rc::new(ty1.clone()),
        }),
    }
}

/// Check that the given term is a valid type.
pub fn check_type<'g, 'db>(
    env: &mut TCEnvironment<'g, 'db>,
    term: &Syntax<'db>,
) -> Result<(), Error<'db>> {
    // If the term is a pi, then we just check that it is valid.
    if let Syntax::Pi(pi) = term {
        return check_pi_type(env, pi);
    }

    if let Syntax::TypeConstructor(tc) = term {
        return check_type_constructor_type(env, tc);
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
fn check_pi_type<'g, 'db>(
    env: &mut TCEnvironment<'g, 'db>,
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

fn check_type_constructor_type<'g, 'db>(
    env: &mut TCEnvironment<'g, 'db>,
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
