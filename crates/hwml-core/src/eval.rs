use crate::common;
use crate::syn::{self as stx};
use crate::syn::{self, Syntax};
use crate::val::{self, Closure, Eliminator, Environment, Flex, GlobalEnv, Normal, Rigid, Value};
use crate::val::{self as dom, DataConstructor, LocalEnv, SemTelescope};
use std::rc::Rc;

#[derive(Debug, Clone)]
pub enum Error {
    BadApplication,
    BadCase,
    UnknownTypeConstructor,
    UnknownDataConstructor,
    UnknownMetavariable,
}

pub fn eval<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    stx: &Syntax<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    match stx {
        Syntax::Constant(constant) => eval_constant(env, &constant),
        Syntax::Variable(var) => eval_variable(env, &var),
        Syntax::Check(chk) => eval_check(env, chk),
        Syntax::Pi(pi) => eval_pi(env, pi),
        Syntax::Lambda(lam) => eval_lambda(env, lam),
        Syntax::TypeConstructor(type_constructor) => eval_type_constructor(env, type_constructor),
        Syntax::DataConstructor(data_constructor) => eval_data_constructor(env, data_constructor),
        Syntax::Application(app) => eval_application(env, &app),
        Syntax::Case(case) => eval_case(env, case),
        Syntax::Universe(uni) => eval_universe(env, &uni),
        Syntax::Metavariable(meta) => eval_metavariable(env, meta),
        Syntax::Bit(_) | Syntax::Lift(_) | Syntax::Quote(_) | Syntax::HArrow(_) => {
            todo!("sorry, not evaluatable yet");
        }
    }
}

fn eval_constant<'db, 'g>(
    _env: &mut Environment<'db, 'g>,
    constant: &syn::Constant<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::Constant(constant.name)))
}

fn eval_variable<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    var: &syn::Variable,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(env.get(var.index.to_level(env.depth())).clone())
}

fn eval_check<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    chk: &syn::Check<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    eval(env, &chk.term)
}

fn eval_type_constructor<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    type_constructor: &syn::TypeConstructor<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    // Evaluate all the arguments
    let mut evaluated_args = Vec::new();
    for arg in type_constructor {
        let evaluated_arg = eval(env, arg)?;
        evaluated_args.push(evaluated_arg);
    }

    // Create a TypeConstructor value with the constructor and evaluated arguments
    let type_constructor_value =
        Value::type_constructor(type_constructor.constructor, evaluated_args);
    Ok(Rc::new(type_constructor_value))
}

fn eval_data_constructor<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    data_constructor: &syn::DataConstructor<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    // Evaluate all the arguments
    let mut evaluated_args = Vec::new();
    for arg in data_constructor {
        let evaluated_arg = eval(env, arg)?;
        evaluated_args.push(evaluated_arg);
    }

    // Create a DataConstructor value with the constructor and evaluated arguments
    let data_value = Value::data_constructor(data_constructor.constructor, evaluated_args);
    Ok(Rc::new(data_value))
}

fn eval_pi<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    pi: &syn::Pi<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    let source = eval(env, &pi.source)?;
    let target = Closure::new(env.local.clone(), pi.target.clone());
    Ok(Rc::new(Value::pi(source, target)))
}

fn eval_lambda<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    lambda: &syn::Lambda<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::Lambda(dom::Lambda {
        body: Closure::new(env.local.clone(), lambda.body.clone()),
    })))
}

fn eval_universe<'db, 'g>(
    _: &mut Environment<'db, 'g>,
    universe: &syn::Universe,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::universe(universe.level)))
}

fn eval_metavariable<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    meta: &syn::Metavariable<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    // Evaluate all the arguments in the substitution to build the local environment.
    let mut local_env = val::LocalEnv::new();
    for arg in meta.iter() {
        let evaluated_arg = eval(env, arg)?;
        local_env.push(evaluated_arg);
    }

    // Look up the metavariable info to get its type.
    let meta_info = env
        .global
        .metavariable(meta.id)
        .map_err(|_| Error::UnknownMetavariable)?;

    // Create an environment for evaluating the type with the substitution.
    let mut type_env = Environment {
        global: env.global,
        local: local_env.clone(),
    };

    // Evaluate the type of the metavariable in the extended environment.
    let meta_ty = eval(&mut type_env, &meta_info.ty)?;

    // Create a metavariable value with the local environment.
    let meta_value = val::MetaVariable::new(meta.id, local_env);

    // Create a Flex neutral with an empty spine.
    let flex = val::Flex::new(meta_value, val::Spine::empty(), meta_ty);

    Ok(Rc::new(Value::Flex(flex)))
}

fn eval_application<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    application: &stx::Application<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    // Evaluate the function and argument to a value, then perform the substitution.
    let fun: Rc<Value> = eval(env, &application.function)?;
    let arg: Rc<Value> = eval(env, &application.argument)?;
    run_application(&env.global, &*fun, arg)
}

/// Perform an application.
pub fn run_application<'db>(
    global: &GlobalEnv<'db>,
    fun: &Value<'db>,
    arg: Rc<Value<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    match fun {
        Value::Lambda(lambda) => apply_lambda(global, lambda, arg),
        Value::Rigid(rigid) => apply_rigid(global, rigid, arg),
        Value::Flex(flex) => apply_flex(global, flex, arg),
        _ => Err(Error::BadApplication),
    }
}

/// Perform the application of a lambda to an argument.
fn apply_lambda<'db>(
    global: &GlobalEnv<'db>,
    lambda: &val::Lambda<'db>,
    arg: Rc<Value<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    run_closure(global, &lambda.body, [arg])
}

/// Perform the application of a rigid neutral to an argument.
fn apply_rigid<'db>(
    global: &GlobalEnv<'db>,
    rigid: &Rigid<'db>,
    arg: Rc<Value<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    // If the operator is not pi-typed, bail.
    let Value::Pi(pi) = rigid.ty.as_ref() else {
        return Err(Error::BadApplication);
    };

    // Use the pi type of the neutral to compute typing information.
    let source_ty = pi.source.clone();
    let target_ty = run_closure(global, &pi.target, [arg.clone()])?;

    // Build the application eliminator.
    let arg_normal = Normal::new(source_ty, arg);
    let eliminator = Eliminator::application(arg_normal);

    // Extend the spine with the application.
    let new_rigid = Rigid::new(rigid.head, rigid.spine.clone(), rigid.ty.clone())
        .apply_eliminator(eliminator, target_ty.clone());

    Ok(Rc::new(Value::Rigid(new_rigid)))
}

/// Perform the application of a flexible neutral to an argument.
fn apply_flex<'db>(
    global: &GlobalEnv<'db>,
    flex: &Flex<'db>,
    arg: Rc<Value<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    // If the operator is not pi-typed, bail.
    let Value::Pi(pi) = flex.ty.as_ref() else {
        return Err(Error::BadApplication);
    };

    // Use the pi type of the neutral to compute typing information.
    let source_ty = pi.source.clone();
    let target_ty = run_closure(global, &pi.target, [arg.clone()])?;

    // Build the application eliminator.
    let arg_normal = Normal::new(source_ty, arg);
    let eliminator = Eliminator::application(arg_normal);

    // Extend the spine with the application.
    let new_flex = Flex::new(flex.head.clone(), flex.spine.clone(), flex.ty.clone())
        .apply_eliminator(eliminator, target_ty.clone());

    Ok(Rc::new(Value::Flex(new_flex)))
}

fn eval_case<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    case: &stx::Case<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    // Evaluate the scrutinee expression
    let scrutinee = eval(env, &case.expr)?;
    let motive = Closure::new(env.local.clone(), case.motive.clone());
    let branches = case
        .branches
        .iter()
        .map(|branch| {
            let body = Closure::new(env.local.clone(), branch.body.clone());
            dom::CaseBranch::new(branch.constructor, branch.arity, body)
        })
        .collect();
    run_case(&env.global, scrutinee, motive, branches)
}

fn run_case<'db>(
    global: &GlobalEnv<'db>,
    scrutinee: Rc<Value<'db>>,
    motive: Closure<'db>,
    branches: Vec<dom::CaseBranch<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    match scrutinee.as_ref() {
        Value::DataConstructor(scrutinee) => {
            run_case_on_data_constructor(global, scrutinee, branches)
        }
        Value::Rigid(rigid) => {
            run_case_on_rigid(global, scrutinee.clone(), rigid, motive, branches)
        }
        Value::Flex(flex) => run_case_on_flex(global, scrutinee.clone(), flex, motive, branches),
        _ => Err(Error::BadCase),
    }
}

fn run_case_on_data_constructor<'db>(
    global: &GlobalEnv<'db>,
    scrutinee: &DataConstructor<'db>,
    branches: Vec<dom::CaseBranch<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    // Find the matching branch.
    for branch in &branches {
        if branch.constructor == scrutinee.constructor {
            return run_closure(global, &branch.body, scrutinee.arguments.clone());
        }
    }
    // If we didn't match any branches, we have a bad case.
    Err(Error::BadCase)
}

fn run_case_on_rigid<'db>(
    global: &GlobalEnv<'db>,
    scrutinee: Rc<Value<'db>>,
    rigid: &Rigid<'db>,
    motive: Closure<'db>,
    branches: Vec<dom::CaseBranch<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    // Verify that the type is a type constructor.
    let Value::TypeConstructor(type_constructor) = rigid.ty.as_ref() else {
        return Err(Error::BadCase);
    };
    let constructor = type_constructor.constructor;

    // Look up the type information from the global environment.
    let type_info = global
        .type_constructor(constructor)
        .map_err(|_| Error::UnknownTypeConstructor)?;

    // Get the parameters and indices off of the types.
    let num_parameters = type_info.num_parameters();
    let parameters = &type_constructor.arguments[..num_parameters];
    let indices = &type_constructor.arguments[num_parameters..];

    // Calculate the final type of the case statement.
    let mut motive_args = indices.to_vec();
    motive_args.push(scrutinee);
    let final_ty = run_closure(&global, &motive, motive_args)?;

    // Build the case eliminator.
    let eliminator = Eliminator::case(constructor, parameters.to_vec(), motive, branches);

    // Extend the spine with the case.
    let new_rigid = Rigid::new(rigid.head, rigid.spine.clone(), rigid.ty.clone())
        .apply_eliminator(eliminator, final_ty.clone());

    Ok(Rc::new(Value::Rigid(new_rigid)))
}

fn run_case_on_flex<'db>(
    global: &GlobalEnv<'db>,
    scrutinee: Rc<Value<'db>>,
    flex: &Flex<'db>,
    motive: Closure<'db>,
    branches: Vec<dom::CaseBranch<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    // Verify that the type is a type constructor.
    let Value::TypeConstructor(type_constructor) = flex.ty.as_ref() else {
        return Err(Error::BadCase);
    };
    let constructor = type_constructor.constructor;

    // Look up the type information from the global environment.
    let type_info = global
        .type_constructor(constructor)
        .map_err(|_| Error::UnknownTypeConstructor)?;

    // Get the parameters and indices off of the types.
    let num_parameters = type_info.num_parameters();
    let parameters = &type_constructor.arguments[..num_parameters];
    let indices = &type_constructor.arguments[num_parameters..];

    // Calculate the final type of the case statement.
    let mut motive_args = indices.to_vec();
    motive_args.push(scrutinee);
    let final_ty = run_closure(&global, &motive, motive_args)?;

    // Build the case eliminator.
    let eliminator = Eliminator::case(constructor, parameters.to_vec(), motive, branches);

    // Extend the spine with the case.
    let new_flex = Flex::new(flex.head.clone(), flex.spine.clone(), flex.ty.clone())
        .apply_eliminator(eliminator, final_ty.clone());

    Ok(Rc::new(Value::Flex(new_flex)))
}

pub fn run_spine<'db>(
    global: &GlobalEnv<'db>,
    mut eliminatee: Rc<Value<'db>>,
    spine: &val::Spine<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    for eliminator in spine.iter() {
        match eliminator {
            Eliminator::Application(application) => {
                eliminatee =
                    run_application(global, &eliminatee, application.argument.value.clone())?;
            }
            Eliminator::Case(case) => {
                eliminatee = run_case(
                    global,
                    eliminatee,
                    case.motive.clone(),
                    case.branches.clone(),
                )?;
            }
        }
    }
    Ok(eliminatee)
}

/// Perform a delayed substitution.
/// Takes only the local environment from the closure and extends it with the provided arguments.
/// The global environment must be provided separately.
pub fn run_closure<'db, T>(
    global: &GlobalEnv<'db>,
    closure: &Closure<'db>,
    args: T,
) -> Result<Rc<Value<'db>>, Error>
where
    T: IntoIterator<Item = Rc<Value<'db>>>,
{
    let mut local = closure.local.clone();
    local.extend(args);
    let mut env = Environment { global, local };
    eval(&mut env, &closure.term)
}

/// Evaluate a telescope to a list of types.
pub fn eval_telescope<'db, 'g, T>(
    global: &'g GlobalEnv<'db>,
    params: T,
    telescope: &stx::Telescope<'db>,
) -> Result<SemTelescope<'db>, Error>
where
    T: IntoIterator<Item = Rc<Value<'db>>>,
{
    // We start with a fresh local environment since types are defined in the
    // global environment.
    let mut env = Environment {
        global: global,
        local: LocalEnv::new(),
    };
    // Extend the environment with the parameters.
    env.extend(params);
    let mut types = Vec::new();

    // Evaluate each binding in the telescope.
    for ty in &telescope.bindings {
        // Evaluate this type.
        let ty = eval(&mut env, ty)?;
        types.push(ty.clone());
        // Create a variable of this type.
        // TODO: only push the variable if there is another binding.
        env.push_var(ty);
    }
    Ok(SemTelescope { types })
}
