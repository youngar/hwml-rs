use crate::syn::{self as stx};
use crate::syn::{self, Syntax};
use crate::val::{self, Closure, Environment, GlobalEnv, Neutral, Value};
use crate::val::{self as dom, DataConstructor, LocalEnv, SemTelescope};
use std::rc::Rc;

#[derive(Debug, Clone)]
pub enum Error {
    BadApplication,
    BadCase,
    UnknownTypeConstructor,
    UnknownDataConstructor,
}

pub fn eval<'g, 'db>(
    env: &mut Environment<'g, 'db>,
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

fn eval_constant<'g, 'db>(
    _env: &mut Environment<'g, 'db>,
    constant: &syn::Constant<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::Constant(constant.name)))
}

fn eval_variable<'g, 'db>(
    env: &mut Environment<'g, 'db>,
    var: &syn::Variable,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(env.get(var.index.to_level(env.depth())).clone())
}

fn eval_check<'g, 'db>(
    env: &mut Environment<'g, 'db>,
    chk: &syn::Check<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    eval(env, &chk.term)
}

fn eval_type_constructor<'g, 'db>(
    env: &mut Environment<'g, 'db>,
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

fn eval_data_constructor<'g, 'db>(
    env: &mut Environment<'g, 'db>,
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

fn eval_pi<'g, 'db>(
    env: &mut Environment<'g, 'db>,
    pi: &syn::Pi<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    let source = eval(env, &pi.source)?;
    let target = Closure::new(env.local.clone(), pi.target.clone());
    Ok(Rc::new(Value::pi(source, target)))
}

fn eval_lambda<'g, 'db>(
    env: &mut Environment<'g, 'db>,
    lambda: &syn::Lambda<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::Lambda(dom::Lambda {
        body: Closure::new(env.local.clone(), lambda.body.clone()),
    })))
}

fn eval_universe<'g, 'db>(
    _: &mut Environment<'g, 'db>,
    universe: &syn::Universe,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::universe(universe.level)))
}

fn eval_metavariable<'g, 'db>(
    _env: &mut Environment<'g, 'db>,
    _meta: &syn::Metavariable<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    todo!()
}

fn eval_application<'g, 'db>(
    env: &mut Environment<'g, 'db>,
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
        Value::Neutral(ty, neutral) => apply_neutral(global, ty, neutral.clone(), arg),
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

/// Perform the application of a neutral term to an argument.
fn apply_neutral<'db>(
    global: &GlobalEnv<'db>,
    ty: &Value<'db>,
    neutral: Rc<Neutral<'db>>,
    arg: Rc<Value<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    // If the operator is not pi-typed, bail.
    let Value::Pi(pi) = ty else {
        return Err(Error::BadApplication);
    };

    // Use the pi type of the neutral to compute typing information.
    let source_ty = pi.source.clone();
    let target_ty = run_closure(global, &pi.target, [arg.clone()])?;

    // Build the new application.
    let app = Value::application(target_ty, neutral, source_ty, arg);
    Ok(Rc::new(app))
}

fn eval_case<'g, 'db>(
    env: &mut Environment<'g, 'db>,
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
        Value::Neutral(scrutinee_ty, scrutinee_ne) => run_case_on_neutral(
            global,
            scrutinee.clone(),
            scrutinee_ty,
            scrutinee_ne,
            motive,
            branches,
        ),
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

fn run_case_on_neutral<'db>(
    global: &GlobalEnv<'db>,
    scrutinee: Rc<Value<'db>>,
    scrutinee_ty: &Rc<Value<'db>>,
    scrutinee_ne: &Rc<Neutral<'db>>,
    motive: Closure<'db>,
    branches: Vec<dom::CaseBranch<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    // Verity that the type is a type constructor.
    let Value::TypeConstructor(type_constructor) = scrutinee_ty.as_ref() else {
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

    // Calculatue the final type of the case statement,
    let mut motive_args = indices.to_vec();
    motive_args.push(scrutinee);
    let final_ty = run_closure(&global, &motive, motive_args)?;

    let case = Value::case(
        final_ty,
        scrutinee_ne.clone(),
        constructor,
        parameters.to_vec(),
        motive,
        branches,
    );
    Ok(Rc::new(case))
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
pub fn eval_telescope<'g, 'db, T>(
    global: &'g GlobalEnv<'db>,
    params: T,
    telescope: &stx::Telescope<'db>,
) -> Result<SemTelescope<'db>, Error>
where
    T: IntoIterator<Item = Rc<Value<'db>>>,
{
    // We start with a fresh local environment since ypes are defined in the
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
