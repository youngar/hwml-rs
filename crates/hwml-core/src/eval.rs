use crate::syn as stx;
use crate::syn;
use crate::syn::Syntax;
use crate::val as dom;
use crate::val;
use crate::val::{Closure, Environment, Neutral, Value};
use std::rc::Rc;

#[derive(Debug, Clone)]
pub enum Error {
    BadApplication,
}

pub fn eval<'db>(env: &mut Environment<'db>, stx: &Syntax<'db>) -> Result<Rc<Value<'db>>, Error> {
    match stx {
        Syntax::Constant(constant) => eval_constant(env, &constant),
        Syntax::Variable(var) => eval_variable(env, &var),
        Syntax::Check(chk) => eval_check(env, chk),
        Syntax::Pi(pi) => eval_pi(env, pi),
        Syntax::Lambda(lam) => eval_lambda(env, lam),
        Syntax::Application(app) => eval_application(env, &app),
        Syntax::Universe(uni) => eval_universe(env, &uni),
        Syntax::Metavariable(meta) => eval_metavariable(env, meta),
        _ => todo!(),
    }
}

fn eval_constant<'db>(
    env: &mut Environment<'db>,
    constant: &syn::Constant<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    todo!()
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

fn eval_pi<'db>(env: &mut Environment<'db>, pi: &syn::Pi<'db>) -> Result<Rc<Value<'db>>, Error> {
    let source = eval(env, &pi.source)?;
    let target = Closure::new(env.clone(), pi.target.clone());
    Ok(Rc::new(Value::pi(source, target)))
}

fn eval_lambda<'db>(
    env: &mut Environment<'db>,
    lambda: &syn::Lambda<'db>,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::Lambda(dom::Lambda {
        body: Closure::new(env.clone(), lambda.body.clone()),
    })))
}

fn eval_universe<'db>(
    _: &mut Environment<'db>,
    universe: &syn::Universe,
) -> Result<Rc<Value<'db>>, Error> {
    Ok(Rc::new(Value::universe(universe.level)))
}

fn eval_metavariable<'db>(
    env: &mut Environment<'db>,
    meta: &syn::Metavariable<'db>,
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
    run_application(&*fun, arg)
}

/// Perform an application.
pub fn run_application<'db>(
    fun: &Value<'db>,
    arg: Rc<Value<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    match fun {
        Value::Lambda(lambda) => apply_lambda(lambda, arg),
        Value::Neutral(ty, neutral) => apply_neutral(ty, neutral.clone(), arg),
        _ => Err(Error::BadApplication),
    }
}

/// Perform the application of a lambda to an argument.
fn apply_lambda<'db>(
    lambda: &val::Lambda<'db>,
    arg: Rc<Value<'db>>,
) -> Result<Rc<Value<'db>>, Error> {
    run_closure(&lambda.body, [arg])
}

/// Perform the application of a neutral term to an argument.
fn apply_neutral<'db>(
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
    let target_ty = run_closure(&pi.target, [arg.clone()])?;

    // Build the new application.
    let app = Value::application(target_ty, neutral, source_ty, arg);
    Ok(Rc::new(app))
}

/// Perform a delayed substitution.
pub fn run_closure<'db, T>(closure: &Closure<'db>, args: T) -> Result<Rc<Value<'db>>, Error>
where
    T: IntoIterator<Item = Rc<Value<'db>>>,
{
    let mut env = closure.environment.clone();
    env.extend(args);
    eval(&mut env, &closure.term)
}
