use crate::common::{Index, Level};
use crate::eval;
use crate::syn::{RcSyntax, Syntax};
use crate::val;
use crate::val::{Closure, Neutral, Normal, Value};
use std::rc::Rc;

/// A quotation error.
#[derive(Debug, Clone)]
pub enum Error {
    /// Something about the input was ill-typed, preventing quotation.
    IllTyped,
    /// Quotation can force evaluation, which may itself prevent an error.
    Eval(eval::Error),
}

type Result<T> = std::result::Result<T, Error>;

/// Read a normal (value * type) back into syntax. The resulting syntax is in normal form.
pub fn quote_normal<'db>(
    db: &'db dyn salsa::Database,
    depth: usize,
    normal: &Normal<'db>,
) -> Result<RcSyntax<'db>> {
    quote(db, depth, &normal.ty, &normal.value)
}

/// Read a value back into syntax. The resulting syntax is in normal form.
/// Quotation is a type-directed procedure whereby we convert a value in the
/// semantic domain to a syntactic normal form.
pub fn quote<'db>(
    db: &'db dyn salsa::Database,
    depth: usize,
    ty: &Value<'db>,
    value: &Value<'db>,
) -> Result<RcSyntax<'db>> {
    match ty {
        Value::Pi(pi) => quote_pi_instance(db, depth, pi, value),
        Value::Universe(universe) => quote_universe_instance(db, depth, universe, value),
        Value::Neutral(_, neutral) => quote_neutral_instance(db, depth, neutral, value),
        _ => Err(Error::IllTyped),
    }
}

/// Read an instance of a pi type back to syntax.
fn quote_pi_instance<'db>(
    db: &'db dyn salsa::Database,
    depth: usize,
    ty: &val::Pi<'db>,
    value: &Value<'db>,
) -> Result<RcSyntax<'db>> {
    // Build a variable representing the lambda's argument.
    let var = Rc::new(Value::variable(ty.source.clone(), Level::new(depth)));

    // Compute the body type by substituting the variable into the target type.
    let body_ty = match eval::run_closure(&ty.target, [var.clone()]) {
        Ok(body_ty) => body_ty,
        Err(error) => return Err(Error::Eval(error)),
    };

    // Compute the body value. This will error if the value is not a lambda.
    let body = match eval::run_application(value, var) {
        Ok(body_ty) => body_ty,
        Err(eval_error) => return Err(Error::Eval(eval_error)),
    };

    // Now quote the body back to syntax.
    let body_stx = quote(db, depth + 1, &body_ty, &body)?;

    // Build and return the lambda.
    let lam = Syntax::lambda(body_stx);
    Ok(Rc::new(lam))
}

/// Read an instance of a universe back to syntax.
fn quote_universe_instance<'db>(
    db: &'db dyn salsa::Database,
    depth: usize,
    _: &val::Universe,
    value: &Value<'db>,
) -> Result<RcSyntax<'db>> {
    quote_type(db, depth, value)
}

/// Read an instance of some neutral type back to syntax.
fn quote_neutral_instance<'db>(
    db: &'db dyn salsa::Database,
    depth: usize,
    _: &val::Neutral<'db>,
    value: &Value<'db>,
) -> Result<RcSyntax<'db>> {
    // The type is unknown, so we proceed by syntax. If the value was not a neutral,
    // then we would know the type. EG if the value was headed by a lambda, we could
    // know that the type was a pi.
    match value {
        Value::Neutral(_ty, neutral) => quote_neutral(db, depth, neutral),
        _ => Err(Error::IllTyped),
    }
}

/// Read back a type in the semantic domain into a syntactic type.
pub fn quote_type<'db>(
    db: &'db dyn salsa::Database,
    depth: usize,
    value: &Value<'db>,
) -> Result<RcSyntax<'db>> {
    match value {
        Value::Pi(pi) => quote_pi(db, depth, pi),
        Value::Universe(universe) => quote_universe(db, depth, universe),
        Value::Neutral(_ty, neutral) => quote_neutral(db, depth, neutral),
        _ => Err(Error::IllTyped),
    }
}

// Read a pi back to syntax.
fn quote_pi<'db>(
    db: &'db dyn salsa::Database,
    depth: usize,
    sem_pi: &val::Pi<'db>,
) -> Result<RcSyntax<'db>> {
    // Read back the source type.
    let sem_source_ty = &sem_pi.source;
    let syn_source_ty = quote_type(db, depth, sem_source_ty)?;

    // Read back the target type.
    let var = Rc::new(Value::variable(sem_pi.source.clone(), Level::new(depth)));
    let sem_target_ty = match eval::run_closure(&sem_pi.target, [var]) {
        Ok(ty) => ty,
        Err(error) => return Err(Error::Eval(error)),
    };
    let syn_target_ty = quote_type(db, depth + 1, &sem_target_ty)?;

    // Return the syntactic pi.
    let syn_pi = Syntax::pi(syn_source_ty, syn_target_ty);
    Ok(Rc::new(syn_pi))
}

/// Read a universe back to syntax.
fn quote_universe<'db>(
    _db: &'db dyn salsa::Database,
    _depth: usize,
    sem_universe: &val::Universe,
) -> Result<RcSyntax<'db>> {
    // Return a syntactic universe at the same universe level.
    let syn_universe = Syntax::universe(sem_universe.level);
    Ok(Rc::new(syn_universe))
}

/// Read a neutral term back to syntax.
fn quote_neutral<'db>(
    db: &'db dyn salsa::Database,
    depth: usize,
    neutral: &val::Neutral<'db>,
) -> Result<RcSyntax<'db>> {
    match neutral {
        Neutral::Variable(var) => quote_variable(db, depth, var),
        Neutral::Application(app) => quote_application(db, depth, app),
    }
}

/// Read a variable back to syntax.
fn quote_variable<'db>(
    _db: &'db dyn salsa::Database,
    depth: usize,
    sem_var: &val::Variable,
) -> Result<RcSyntax<'db>> {
    // Convert the DB level to an index, and return the syntactic variable.
    let syn_var = Syntax::variable(sem_var.level.to_index(depth));
    Ok(Rc::new(syn_var))
}

/// Read a stuck application back to syntax.
fn quote_application<'db>(
    db: &'db dyn salsa::Database,
    depth: usize,
    sem_app: &val::Application<'db>,
) -> Result<RcSyntax<'db>> {
    // Read back the function.
    let sem_fun = &sem_app.function;
    let syn_fun = quote_neutral(db, depth, &sem_fun)?;

    // Read back the argument.
    let sem_arg = &sem_app.argument;
    let syn_arg = quote_normal(db, depth, &sem_arg)?;

    // Return the syntactic application.
    let syn_app = Syntax::application(syn_fun, syn_arg);
    Ok(Rc::new(syn_app))
}
