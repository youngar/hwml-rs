use crate::common::Level;
use crate::syn::{self as stx};
use crate::syn::{self, Telescope};
use crate::syn::{Case, Syntax};
use crate::val::{self as dom, DataConstructor, SemTelescope};
use crate::val::{self, Normal};
use crate::val::{Closure, Environment, GlobalEnv, Neutral, Value};
use std::rc::Rc;

#[derive(Debug, Clone)]
pub enum Error {
    BadApplication,
    BadCase,
    UnknownTypeConstructor,
    UnknownDataConstructor,
}

pub fn eval<'db>(env: &mut Environment<'db>, stx: &Syntax<'db>) -> Result<Rc<Value<'db>>, Error> {
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
        _ => todo!(),
    }
}

fn eval_constant<'db>(
    _env: &mut Environment<'db>,
    constant: &syn::Constant<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::Constant(constant.name)))
}

fn eval_variable<'db>(
    env: &mut Environment<'db>,
    var: &syn::Variable,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(env.get(var.index.to_level(env.depth())).clone())
}

fn eval_check<'db>(
    env: &mut Environment<'db>,
    chk: &syn::Check<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    eval(env, &chk.term)
}

fn eval_type_constructor<'db>(
    env: &mut Environment<'db>,
    type_constructor: &syn::TypeConstructor<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    // Evaluate all the arguments
    let mut evaluated_args = Vec::new();
    for arg in &type_constructor.arguments {
        let evaluated_arg = eval(env, arg)?;
        evaluated_args.push(evaluated_arg);
    }

    // Create a TypeConstructor value with the constructor and evaluated arguments
    let type_constructor_value =
        Value::type_constructor(type_constructor.constructor, evaluated_args);
    Ok(Rc::new(type_constructor_value))
}

fn eval_data_constructor<'db>(
    env: &mut Environment<'db>,
    data_constructor: &syn::DataConstructor<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    // Evaluate all the arguments
    let mut evaluated_args = Vec::new();
    for arg in &data_constructor.arguments {
        let evaluated_arg = eval(env, arg)?;
        evaluated_args.push(evaluated_arg);
    }

    // Create a DataConstructor value with the constructor and evaluated arguments
    let data_value = Value::data_constructor(data_constructor.constructor, evaluated_args);
    Ok(Rc::new(data_value))
}

fn eval_pi<'db>(env: &mut Environment<'db>, pi: &syn::Pi<'db>) -> Result<Rc<Value<'db>>, Error> {
    let source = eval(env, &pi.source)?;
    let target = Closure::new(env.local.clone(), pi.target.clone());
    Ok(Rc::new(Value::pi(source, target)))
}

fn eval_lambda<'db>(
    env: &mut Environment<'db>,
    lambda: &syn::Lambda<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::Lambda(dom::Lambda {
        body: Closure::new(env.local.clone(), lambda.body.clone()),
    })))
}

fn eval_universe<'db>(
    _: &mut Environment<'db>,
    universe: &syn::Universe,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::universe(universe.level)))
}

fn eval_metavariable<'db>(
    _env: &mut Environment<'db>,
    _meta: &syn::Metavariable<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    todo!()
}

fn eval_application<'db>(
    env: &mut Environment<'db>,
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

fn eval_case<'db>(
    env: &mut Environment<'db>,
    case: &stx::Case<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    // Evaluate the scrutinee expression
    let scrutinee = eval(env, &case.expr)?;
    run_case(env, scrutinee, case)
}

fn run_case<'db>(
    env: &mut Environment<'db>,
    scrutinee: Rc<Value<'db>>,
    case: &Case<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    match scrutinee.as_ref() {
        Value::DataConstructor(scrutinee) => run_case_on_data_constructor(env, scrutinee, case),
        Value::Neutral(scrutinee_ty, scrutinee_ne) => {
            run_case_on_neutral(env, scrutinee_ty, &scrutinee, scrutinee_ne, case)
        }
        _ => Err(Error::BadCase),
    }
}

fn run_case_on_data_constructor<'db>(
    env: &mut Environment<'db>,
    scrutinee: &DataConstructor<'db>,
    case: &Case<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    // Push the arguments onto the environment.
    for data in &scrutinee.arguments {
        env.push(data.clone());
    }
    // Find the matching branch.
    for branch in &case.branches {
        if branch.constructor == scrutinee.constructor {
            return eval(env, &branch.body);
        }
    }
    // If we didn't match any branches, we have a bad case.
    Err(Error::BadCase)
}

fn run_case_on_neutral<'db>(
    env: &mut Environment<'db>,
    scrutinee_ty: &Rc<Value<'db>>,
    scrutinee_val: &Rc<Value<'db>>,
    scrutinee_ne: &Rc<Neutral<'db>>,
    case: &Case<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    // Check that the scrutinee type is a type constructor.
    let Value::TypeConstructor(type_constructor) = scrutinee_ty.as_ref() else {
        return Err(Error::BadCase);
    };

    // Create a closure wrapping the motive. This will be used to determine the type of each branch.
    let motive_clos = Closure::new(env.local.clone(), case.motive.clone());

    // Calculate the final type of the case expression by substituting the scrutinee into the motive.
    let final_ty = run_closure(&env.global, &motive_clos, [scrutinee_val.clone()])?;

    // Create a variable with the same type as the scrutinee.
    let scrutinee_ty_var = Rc::new(Value::variable(
        scrutinee_ty.clone(),
        Level::new(env.depth()),
    ));

    // Normalize the motive by substituting a variable into the it.
    let motive_sem = run_closure(&env.global, &motive_clos, [scrutinee_ty_var.clone()])?;

    // Look up the scrutinee type information.
    let type_info = env
        .global
        .type_constructor(type_constructor.constructor)
        .map_err(|_| Error::UnknownTypeConstructor)?;

    // Find the number of parameters.
    let num_parameters = type_info.num_parameters();

    // Create an array of parameters.
    let parameters = type_constructor
        .arguments
        .iter()
        .take(num_parameters)
        .cloned();

    let mut branches = Vec::new();
    for branch in &case.branches {
        // Create a variable for each argument to this dataconstructor.
        let constructor_info = env
            .global
            .data_constructor(branch.constructor)
            .map_err(|_| Error::UnknownDataConstructor)?
            .clone();

        // Find the types of the constructor arguments.
        let arg_types = eval_telescope(env, parameters.clone(), &constructor_info.arguments)?;

        // Create a variable for each data constructor argument.
        let mut arg_vars = vec![];
        for ty in arg_types.types {
            arg_vars.push(env.local.push_var(ty));
        }

        // Get the type of this branch by substituting the constructor instance into the motive.
        let branch_scrut = Rc::new(Value::data_constructor(
            branch.constructor,
            arg_vars.clone(),
        ));
        let branch_type = run_closure(&env.global, &motive_clos, [branch_scrut])?;

        // Evaluate the branch body and create a normal value for it.
        let branch_value = eval(env, &branch.body)?;
        let branch_norm = Normal::new(branch_type, branch_value);
        branches.push(dom::CaseBranch::new(
            branch.constructor,
            branch.arity,
            branch_norm,
        ));
    }

    Ok(Rc::new(Value::case(
        final_ty,
        scrutinee_ne.clone(),
        motive_sem.clone(),
        branches,
    )))
}

pub fn run_with_args<'db, T>(
    env: &Environment<'db>,
    syntax: &Syntax<'db>,
    args: T,
) -> Result<Rc<Value<'db>>, Error>
where
    T: IntoIterator<Item = Rc<Value<'db>>>,
{
    let mut env = env.clone();
    env.extend(args);
    eval(&mut env, syntax)
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
    let mut env = Environment {
        global: global.clone(),
        local,
    };
    eval(&mut env, &closure.term)
}

pub fn eval_telescope<'db, T>(
    env: &mut Environment<'db>,
    args: T,
    telescope: &Telescope<'db>,
) -> Result<SemTelescope<'db>, Error>
where
    T: IntoIterator<Item = Rc<Value<'db>>>,
{
    let depth = env.depth();
    env.extend(args);
    let mut types = Vec::new();

    for ty in &telescope.bindings {
        // Evaluate this type.
        let ty = eval(env, ty)?;
        types.push(ty.clone());
        // Create a variable of this type.
        // TODO: only push the variable if there is another binding.
        env.push_var(ty);
    }
    env.truncate(depth);
    Ok(SemTelescope { types })
}
