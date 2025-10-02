use crate::common::Level;
use crate::eval;
use crate::syn as stx;
use crate::syn;
use crate::syn::Syntax;
use crate::val;
use crate::val::Value;
use std::rc::Rc;

pub struct EnvironmentEntry {
    pub value: Rc<Value>,
    pub ty: Rc<Value>,
}

pub type Environment = Vec<EnvironmentEntry>;

/// Convert a typechecking environment to an environment in the semantic domain, by throwing
/// away the types and just remembering the semanticvalues associated with each variable.
fn semantic_env(env: &Environment) -> val::Environment {
    let mut dom_env = val::Environment::new();
    for entry in env.iter() {
        dom_env.push(entry.value.clone());
    }
    dom_env
}

/// Push a variable into the typechecking environment.
fn var_push(env: &mut Environment, value: Rc<Value>, ty: Rc<Value>) {
    env.push(EnvironmentEntry { value, ty });
}

/// Access the entry of a variable in the syntax.
fn var_entry<'a>(env: &'a Environment, var: &stx::Variable) -> &'a EnvironmentEntry {
    let i: usize = var.index.into();
    &env[i]
}

/// Access the type of a variable in the syntax.
fn var_type<'a>(env: &'a Environment, var: &stx::Variable) -> &'a Rc<Value> {
    &var_entry(env, var).ty
}

#[derive(Debug, Clone)]
pub enum Error {
    TypeSynthesisFailure,
    TypeMismatch,
    EvaluationFailure(eval::Error),
    Misc(String),
}

type Result<T> = std::result::Result<T, Error>;

fn err<T>(message: &str) -> Result<T> {
    Err(Error::Misc(String::from(message)))
}

/// Evaluate a syntactic term to a semantic value.
fn eval(env: &Environment, term: &Syntax) -> Result<Rc<Value>> {
    let mut sem_env = semantic_env(env);
    match eval::eval(&mut sem_env, term) {
        Ok(value) => Ok(value),
        Err(error) => Err(Error::EvaluationFailure(error)),
    }
}

/// Adaptor for running a closure from the semantic domain.
fn run_closure<T>(closure: &val::Closure, args: T) -> Result<Rc<Value>>
where
    T: IntoIterator<Item = Rc<Value>>,
{
    match eval::run_closure(closure, args) {
        Ok(value) => Ok(value),
        Err(error) => Err(Error::EvaluationFailure(error)),
    }
}

/// Synthesize (infer) types for variables and elimination forms.
pub fn type_synth(env: &mut Environment, term: &Syntax) -> Result<Rc<Value>> {
    match term {
        Syntax::Variable(variable) => type_synth_variable(env, variable),
        Syntax::Application(application) => type_synth_application(env, application),
        _ => Err(Error::TypeSynthesisFailure),
    }
}

/// Synthesize a type for a variable.
pub fn type_synth_variable(env: &mut Environment, variable: &syn::Variable) -> Result<Rc<Value>> {
    // Pull the type from the typing environment.
    Ok(var_type(env, variable).clone())
}

/// Synthesize the type of a function application.
pub fn type_synth_application(
    env: &mut Environment,
    application: &syn::Application,
) -> Result<Rc<Value>> {
    // First synthesize the type of the term being applied.
    let fun_ty = type_synth(env, &application.function)?;

    // Ensure that the applied term is a function `(x : src) -> tgt(x)`.
    let Value::Pi(pi) = &*fun_ty else {
        return Err(Error::TypeMismatch);
    };

    // Check the argument against the source type of the function.
    type_check(env, &application.argument, &*pi.source)?;

    // The overall type is determined by substituting the argument into the target type.
    let arg = eval(env, &application.argument)?;
    run_closure(&pi.target, [arg])
}

/// Check types of terms against an expected type.
pub fn type_check(env: &mut Environment, term: &Syntax, ty: &Value) -> Result<()> {
    match term {
        Syntax::Pi(pi) => type_check_pi(env, pi, ty),
        _ => type_check_synth_term(env, term, ty),
    }
}

/// Typecheck a pi term.
fn type_check_pi(env: &mut Environment, pi: &syn::Pi, ty: &Value) -> Result<()> {
    // The expected type of a pi must be a universe.
    let Value::Universe(_) = ty else {
        return Err(Error::TypeMismatch);
    };

    // Check that the source type is valid.
    check_type(env, &pi.source)?;

    // Evaluate the source type to a value.
    let sem_source_ty = eval(env, &pi.source)?;

    // Construct a variable of the source type.
    let var = Rc::new(Value::variable(sem_source_ty.clone(), Level(env.len())));

    // Check that the target type is of the same universe as the pi.
    var_push(env, var, sem_source_ty);
    let result = type_check(env, &pi.target, ty);
    env.pop();
    result
}

// Synthesize a type for the term, then check for equality against the expected type.
pub fn type_check_synth_term(env: &mut Environment, term: &Syntax, ty1: &Value) -> Result<()> {
    let ty2 = type_synth(env, term)?;
    check_type_equal(env, ty1, &*ty2)
}

/// Check that two types are equal.
pub fn check_type_equal(env: &Environment, a: &Value, b: &Value) -> Result<()> {
    err("not implemented")
}

/// Check that the given term is a valid type.
pub fn check_type(env: &mut Environment, term: &Syntax) -> Result<()> {
    // If the term is a pi, then we just check that it is valid.
    if let Syntax::Pi(pi) = term {
        return check_pi_type(env, pi);
    }

    // Otherwise, synthesize a type for the term, which must be a universe.
    let ty = type_synth(env, term)?;
    if let Value::Universe(_) = &*ty {
        return Ok(());
    }

    // Otherwise return failure: this is not a type.
    Err(Error::TypeMismatch)
}

/// Check that a pi is a valid type.
fn check_pi_type(env: &mut Environment, pi: &stx::Pi) -> Result<()> {
    // First check that the source-type of the pi is a type.
    check_type(env, &pi.source)?;

    // Evaluate the source-type.
    let ty = eval(env, &pi.source)?;

    // Check the codomain under an environment extended with one additional
    // variable, of the domain type, representing the pi binder.
    let tm = Rc::new(Value::variable(ty.clone(), Level(env.len())));
    var_push(env, tm, ty);
    let result = check_type(env, &pi.target);
    env.pop();
    result
}
