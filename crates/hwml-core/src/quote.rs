use crate::common::Level;
use crate::eval;
use crate::syn::{Case, CaseBranch, RcSyntax, Syntax};
use crate::val::{self, Environment, LocalEnv};
use crate::val::{GlobalEnv, Neutral, Normal, Value};
use std::rc::Rc;

/// A quotation error.
#[derive(Debug, Clone)]
pub enum Error {
    /// Something about the input was ill-typed, preventing quotation.
    IllTyped,
    /// Quotation can force evaluation, which may itself prevent an error.
    EvalError(eval::Error),
    LookupError(val::LookupError),
}

type Result<T> = std::result::Result<T, Error>;

/// Read a normal (value * type) back into syntax. The resulting syntax is in normal form.
pub fn quote_normal<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    normal: &Normal<'db>,
) -> Result<RcSyntax<'db>> {
    quote(db, global, depth, &normal.ty, &normal.value)
}

/// Read a value back into syntax. The resulting syntax is in normal form.
/// Quotation is a type-directed procedure whereby we convert a value in the
/// semantic domain to a syntactic normal form.
pub fn quote<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    ty: &Value<'db>,
    value: &Value<'db>,
) -> Result<RcSyntax<'db>> {
    match ty {
        Value::Pi(pi) => quote_pi_instance(db, global, depth, pi, value),
        Value::Universe(universe) => quote_universe_instance(db, global, depth, universe, value),
        Value::TypeConstructor(tc) => quote_type_constructor_instance(db, global, depth, tc, value),
        Value::Neutral(_, neutral) => quote_neutral_instance(db, global, depth, neutral, value),
        _ => Err(Error::IllTyped),
    }
}

/// Read an instance of a pi type back to syntax.
fn quote_pi_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    ty: &val::Pi<'db>,
    value: &Value<'db>,
) -> Result<RcSyntax<'db>> {
    // Build a variable representing the lambda's argument.
    let var = Rc::new(Value::variable(ty.source.clone(), Level::new(depth)));

    // Compute the body type by substituting the variable into the target type.
    let body_ty = match eval::run_closure(global, &ty.target, [var.clone()]) {
        Ok(body_ty) => body_ty,
        Err(error) => return Err(Error::EvalError(error)),
    };

    // Compute the body value. This will error if the value is not a lambda.
    let body = match eval::run_application(global, value, var) {
        Ok(body_ty) => body_ty,
        Err(eval_error) => return Err(Error::EvalError(eval_error)),
    };

    // Now quote the body back to syntax.
    let body_stx = quote(db, global, depth + 1, &body_ty, &body)?;

    // Build and return the lambda.
    let lam = Syntax::lambda(body_stx);
    Ok(Rc::new(lam))
}

/// Read an instance of a universe back to syntax.
fn quote_universe_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    _: &val::Universe,
    value: &Value<'db>,
) -> Result<RcSyntax<'db>> {
    quote_type(db, global, depth, value)
}

/// Read an instance of a datatype back to syntax.
fn quote_type_constructor_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    ty: &val::TypeConstructor<'db>,
    value: &Value<'db>,
) -> Result<RcSyntax<'db>> {
    match value {
        Value::DataConstructor(data_constructor) => {
            quote_data_constructor(db, global, depth, ty, data_constructor)
        }
        Value::Neutral(_, neutral) => quote_neutral(db, global, depth, neutral),
        _ => Err(Error::IllTyped),
    }
}

/// Read an instance of some neutral type back to syntax.
fn quote_neutral_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    _: &val::Neutral<'db>,
    value: &Value<'db>,
) -> Result<RcSyntax<'db>> {
    // The type is unknown, so we proceed by syntax. If the value was not a neutral,
    // then we would know the type. EG if the value was headed by a lambda, we could
    // know that the type was a pi.
    match value {
        Value::Neutral(_ty, neutral) => quote_neutral(db, global, depth, neutral),
        _ => Err(Error::IllTyped),
    }
}

/// Read back a type in the semantic domain into a syntactic type.
pub fn quote_type<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    value: &Value<'db>,
) -> Result<RcSyntax<'db>> {
    match value {
        Value::Pi(pi) => quote_pi(db, global, depth, pi),
        Value::TypeConstructor(tc) => quote_type_constructor(db, global, depth, tc),
        Value::Universe(universe) => quote_universe(db, depth, universe),
        Value::Neutral(_ty, neutral) => quote_neutral(db, global, depth, neutral),
        _ => Err(Error::IllTyped),
    }
}

// Read a pi back to syntax.
fn quote_pi<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    sem_pi: &val::Pi<'db>,
) -> Result<RcSyntax<'db>> {
    // Read back the source type.
    let sem_source_ty = &sem_pi.source;
    let syn_source_ty = quote_type(db, global, depth, sem_source_ty)?;

    // Read back the target type.
    let var = Rc::new(Value::variable(sem_pi.source.clone(), Level::new(depth)));
    let sem_target_ty = match eval::run_closure(global, &sem_pi.target, [var]) {
        Ok(ty) => ty,
        Err(error) => return Err(Error::EvalError(error)),
    };
    let syn_target_ty = quote_type(db, global, depth + 1, &sem_target_ty)?;

    // Return the syntactic pi.
    let syn_pi = Syntax::pi(syn_source_ty, syn_target_ty);
    Ok(Rc::new(syn_pi))
}

/// Read a data constructor instance back to syntax.
fn quote_type_constructor<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    sem_tcon: &val::TypeConstructor<'db>,
) -> Result<RcSyntax<'db>> {
    // Get the constructor constant.
    let constructor = sem_tcon.constructor;

    // Look up the type info.
    let type_info = global
        .type_constructor(constructor)
        .map_err(Error::LookupError)?
        .clone();

    // Create a new environment.
    let mut env = Environment {
        global: global.clone(),
        local: LocalEnv::new(),
    };

    // The arguments vector contains parameters first, then indices.
    let mut arguments = Vec::new();

    // Combine parameters and indices into a single iterator.
    let all_bindings = type_info
        .parameters
        .bindings
        .iter()
        .chain(type_info.indices.bindings.iter());

    // Quote each argument (both parameters and indices).
    for (sem_arg, syn_ty) in sem_tcon.arguments.iter().zip(all_bindings) {
        // Evaluate the type of the current argument.
        let sem_ty = eval::eval(&mut env, &syn_ty).map_err(Error::EvalError)?;

        // Quote the current argument.
        let syn_arg = quote(db, global, depth, &sem_ty, sem_arg)?;
        arguments.push(syn_arg);

        // Push the semantic argument into the environment for subsequent iterations.
        env.push(sem_arg.clone());
    }
    Ok(Syntax::type_constructor_rc(constructor, arguments))
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
    global: &GlobalEnv<'db>,
    depth: usize,
    neutral: &val::Neutral<'db>,
) -> Result<RcSyntax<'db>> {
    match neutral {
        Neutral::Variable(var) => quote_variable(db, depth, var),
        Neutral::Application(app) => quote_application(db, global, depth, app),
        Neutral::Case(case) => quote_case(db, global, depth, case),
    }
}

/// Read a data constructor instance back to syntax.
fn quote_data_constructor<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    mut depth: usize,
    type_constructor: &val::TypeConstructor<'db>,
    sem_data: &val::DataConstructor<'db>,
) -> Result<RcSyntax<'db>> {
    // Get the constructor constant.
    let constructor = sem_data.constructor;

    // Look up the type constructor info (from the type, not the data constructor).
    let type_info = global
        .type_constructor(type_constructor.constructor)
        .map_err(Error::LookupError)?
        .clone();

    // Look up the data constructor info.
    let data_info = global
        .data_constructor(constructor)
        .map_err(Error::LookupError)?
        .clone();

    // Find the number of parameters.
    let num_parameters = type_info.num_parameters();

    // Create an array of just the paremeters, leaving out indices.
    let parameters = type_constructor
        .arguments
        .iter()
        .take(num_parameters)
        .cloned();

    // Create an environment for evaluating the type of each argument, with
    // parameters in the context.
    let mut env = Environment {
        global: global.clone(),
        local: LocalEnv::new(),
    };
    env.extend(parameters);
    depth = depth + num_parameters;

    // Quote each argument.
    let mut arguments = Vec::new();
    for (sem_arg, syn_ty) in sem_data.arguments.iter().zip(data_info.arguments.bindings) {
        // Evaluate the type of the current argument.
        let sem_ty = eval::eval(&mut env, &syn_ty).map_err(Error::EvalError)?;

        // Quote the current argument
        let syn_arg = quote(db, global, depth, &sem_ty, &sem_arg)?;
        arguments.push(syn_arg);

        // Push the semantic argument into the environment for subsequent iterations.
        env.push(sem_arg.clone());
    }
    Ok(Syntax::data_constructor_rc(constructor, arguments))
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
    global: &GlobalEnv<'db>,
    depth: usize,
    sem_app: &val::Application<'db>,
) -> Result<RcSyntax<'db>> {
    // Read back the function.
    let sem_fun = &sem_app.function;
    let syn_fun = quote_neutral(db, global, depth, &sem_fun)?;

    // Read back the argument.
    let sem_arg = &sem_app.argument;
    let syn_arg = quote_normal(db, global, depth, &sem_arg)?;

    // Return the syntactic application.
    let syn_app = Syntax::application(syn_fun, syn_arg);
    Ok(Rc::new(syn_app))
}

fn quote_case<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    depth: usize,
    sem_case: &val::Case<'db>,
) -> Result<RcSyntax<'db>> {
    // Read back the scrutinee expression.
    let sem_scrutinee = &sem_case.scrutinee;
    let syn_scrutinee = quote_neutral(db, global, depth, &sem_scrutinee)?;

    let sem_motive = &sem_case.motive;
    let syn_motive = quote_type(db, global, depth + 1, &sem_motive)?;

    let syn_branches = sem_case
        .branches
        .iter()
        .map(|branch| {
            quote_normal(db, global, depth + branch.arity, &branch.body)
                .map(|body| CaseBranch::new(branch.constructor, branch.arity, body))
        })
        .collect::<Result<_>>()?;
    Ok(Syntax::case_rc(syn_scrutinee, syn_motive, syn_branches))
}
