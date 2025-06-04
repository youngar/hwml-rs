use crate::domain as dom;
use crate::domain;
use crate::domain::{Closure, Environment, Neutral, Value};
use crate::syntax as stx;
use crate::syntax;
use crate::syntax::Syntax;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub enum Error {
    BadApplication,
}

pub fn eval(env: &mut Environment, stx: &Syntax) -> Result<Rc<Value>, Error> {
    match stx {
        Syntax::Variable(var) => eval_variable(env, &var),
        Syntax::Check(chk) => eval_check(env, chk),
        Syntax::Pi(pi) => eval_pi(env, pi),
        Syntax::Lambda(lam) => eval_lambda(env, lam),
        Syntax::Application(app) => eval_application(env, &app),
        Syntax::Universe(uni) => eval_universe(env, &uni),
    }
}

fn eval_variable(env: &mut Environment, var: &syntax::Variable) -> Result<Rc<Value>, Error> {
    Ok(env.get(var.index.to_level(env.depth())).clone())
}

fn eval_check(env: &mut Environment, chk: &syntax::Check) -> Result<Rc<Value>, Error> {
    eval(env, &chk.term)
}

fn eval_pi(env: &mut Environment, pi: &syntax::Pi) -> Result<Rc<Value>, Error> {
    let source = eval(env, &pi.source)?;
    let target = Closure::new(env.clone(), pi.target.clone());
    Ok(Rc::new(Value::pi(source, target)))
}

fn eval_lambda(env: &mut Environment, lambda: &syntax::Lambda) -> Result<Rc<Value>, Error> {
    Ok(Rc::new(Value::Lambda(dom::Lambda {
        body: Closure::new(env.clone(), lambda.body.clone()),
    })))
}

fn eval_universe(_: &mut Environment, universe: &syntax::Universe) -> Result<Rc<Value>, Error> {
    Ok(Rc::new(Value::universe(universe.level)))
}

fn eval_application(
    env: &mut Environment,
    application: &stx::Application,
) -> Result<Rc<Value>, Error> {
    // Evaluate the function and argument to a value, then perform the substitution.
    let fun: Rc<Value> = eval(env, &application.function)?;
    let arg: Rc<Value> = eval(env, &application.argument)?;
    run_application(&*fun, arg)
}

/// Perform an application.
pub fn run_application(fun: &Value, arg: Rc<Value>) -> Result<Rc<Value>, Error> {
    match fun {
        Value::Lambda(lambda) => apply_lambda(lambda, arg),
        Value::Neutral(ty, neutral) => apply_neutral(ty, neutral.clone(), arg),
        _ => Err(Error::BadApplication),
    }
}

/// Perform the application of a lambda to an argument.
fn apply_lambda(lambda: &domain::Lambda, arg: Rc<Value>) -> Result<Rc<Value>, Error> {
    run_closure(&lambda.body, [arg])
}

/// Perform the application of a neutral term to an argument.
fn apply_neutral(ty: &Value, neutral: Rc<Neutral>, arg: Rc<Value>) -> Result<Rc<Value>, Error> {
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
pub fn run_closure<T>(closure: &Closure, args: T) -> Result<Rc<Value>, Error>
where
    T: IntoIterator<Item = Rc<Value>>,
{
    let mut env = closure.environment.clone();
    env.extend(args);
    eval(&mut env, &closure.term)
}
