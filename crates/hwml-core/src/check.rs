use crate::common::Level;
use crate::eval;
use crate::syn as stx;
use crate::syn;
use crate::syn::Syntax;
use crate::val;
use crate::val::Value;
use std::rc::Rc;

pub struct EnvironmentEntry<'db> {
    pub value: Rc<Value<'db>>,
    pub ty: Rc<Value<'db>>,
}

pub type Environment<'db> = Vec<EnvironmentEntry<'db>>;

/// Convert a typechecking environment to an environment in the semantic domain, by throwing
/// away the types and just remembering the semanticvalues associated with each variable.
fn semantic_env<'db>(env: &Environment<'db>) -> val::Environment<'db> {
    let mut dom_env = val::Environment::new();
    for entry in env.iter() {
        dom_env.push(entry.value.clone());
    }
    dom_env
}

/// Push a variable into the typechecking environment.
fn var_push<'db>(env: &mut Environment<'db>, value: Rc<Value<'db>>, ty: Rc<Value<'db>>) {
    env.push(EnvironmentEntry { value, ty });
}

/// Access the entry of a variable in the syntax.
fn var_entry<'a, 'db>(env: &'a Environment<'db>, var: &stx::Variable) -> &'a EnvironmentEntry<'db> {
    let i: usize = var.index.into();
    &env[i]
}

/// Access the type of a variable in the syntax.
fn var_type<'a, 'db>(env: &'a Environment<'db>, var: &stx::Variable) -> &'a Rc<Value<'db>> {
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
fn eval<'db>(env: &Environment<'db>, term: &Syntax<'db>) -> Result<Rc<Value<'db>>> {
    let mut sem_env = semantic_env(env);
    match eval::eval(&mut sem_env, term) {
        Ok(value) => Ok(value),
        Err(error) => Err(Error::EvaluationFailure(error)),
    }
}

/// Adaptor for running a closure from the semantic domain.
fn run_closure<'db, T>(
    global: &val::GlobalEnv<'db>,
    closure: &val::Closure<'db>,
    args: T,
) -> Result<Rc<Value<'db>>>
where
    T: IntoIterator<Item = Rc<Value<'db>>>,
{
    match eval::run_closure(global, closure, args) {
        Ok(value) => Ok(value),
        Err(error) => Err(Error::EvaluationFailure(error)),
    }
}

/// Synthesize (infer) types for variables and elimination forms.
pub fn type_synth<'db>(env: &mut Environment<'db>, term: &Syntax<'db>) -> Result<Rc<Value<'db>>> {
    match term {
        Syntax::Variable(variable) => type_synth_variable(env, variable),
        Syntax::Application(application) => type_synth_application(env, application),
        Syntax::DataConstructor(data_constructor) => {
            type_synth_data_constructor(env, data_constructor)
        }
        _ => Err(Error::TypeSynthesisFailure),
    }
}

/// Synthesize a type for a variable.
pub fn type_synth_variable<'db>(
    env: &mut Environment<'db>,
    variable: &syn::Variable,
) -> Result<Rc<Value<'db>>> {
    // Pull the type from the typing environment.
    Ok(var_type(env, variable).clone())
}

/// Synthesize the type of a function application.
pub fn type_synth_application<'db>(
    env: &mut Environment<'db>,
    application: &syn::Application<'db>,
) -> Result<Rc<Value<'db>>> {
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
    let sem_env = semantic_env(env);
    run_closure(&sem_env.global, &pi.target, [arg])
}

/// Synthesize the type of a data constructor application.
pub fn type_synth_data_constructor<'db>(
    env: &mut Environment<'db>,
    data_constructor: &syn::DataConstructor<'db>,
) -> Result<Rc<Value<'db>>> {
    // TODO: For now, we'll return a placeholder type.
    // In a full implementation, we would:
    // 1. Look up the constructor's type signature from the global environment
    // 2. Check that the arguments match the constructor's parameter types
    // 3. Return the constructor's return type (the inductive type it constructs)

    // For now, return a universe as a placeholder
    let _ = (env, data_constructor); // Use the parameters to avoid unused variable warnings
    todo!("Data constructor type synthesis not yet implemented")
}

/// Check types of terms against an expected type.
pub fn type_check<'db>(
    env: &mut Environment<'db>,
    term: &Syntax<'db>,
    ty: &Value<'db>,
) -> Result<()> {
    match term {
        Syntax::Pi(pi) => type_check_pi(env, pi, ty),
        _ => type_check_synth_term(env, term, ty),
    }
}

/// Typecheck a pi term.
fn type_check_pi<'db>(
    env: &mut Environment<'db>,
    pi: &syn::Pi<'db>,
    ty: &Value<'db>,
) -> Result<()> {
    // The expected type of a pi must be a universe.
    let Value::Universe(_) = ty else {
        return Err(Error::TypeMismatch);
    };

    // Check that the source type is valid.
    check_type(env, &pi.source)?;

    // Evaluate the source type to a value.
    let sem_source_ty = eval(env, &pi.source)?;

    // Construct a variable of the source type.
    let var = Rc::new(Value::variable(
        sem_source_ty.clone(),
        Level::new(env.len()),
    ));

    // Check that the target type is of the same universe as the pi.
    var_push(env, var, sem_source_ty);
    let result = type_check(env, &pi.target, ty);
    env.pop();
    result
}

// Synthesize a type for the term, then check for equality against the expected type.
pub fn type_check_synth_term<'db>(
    env: &mut Environment<'db>,
    term: &Syntax<'db>,
    ty1: &Value<'db>,
) -> Result<()> {
    let ty2 = type_synth(env, term)?;
    check_type_equal(env, ty1, &*ty2)
}

/// Check that two types are equal.
pub fn check_type_equal<'db>(
    _env: &Environment<'db>,
    _a: &Value<'db>,
    _b: &Value<'db>,
) -> Result<()> {
    err("not implemented")
}

/// Check that the given term is a valid type.
pub fn check_type<'db>(env: &mut Environment<'db>, term: &Syntax<'db>) -> Result<()> {
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
fn check_pi_type<'db>(env: &mut Environment<'db>, pi: &stx::Pi<'db>) -> Result<()> {
    // First check that the source-type of the pi is a type.
    check_type(env, &pi.source)?;

    // Evaluate the source-type.
    let ty = eval(env, &pi.source)?;

    // Check the codomain under an environment extended with one additional
    // variable, of the domain type, representing the pi binder.
    let tm = Rc::new(Value::variable(ty.clone(), Level::new(env.len())));
    var_push(env, tm, ty);
    let result = check_type(env, &pi.target);
    env.pop();
    result
}
