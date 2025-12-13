use crate::common::Level;
use crate::eval;
use crate::syn as stx;
use crate::syn;
use crate::syn::Syntax;
use crate::val;
use crate::val::Closure;
use crate::val::Value;
use std::rc::Rc;

pub struct TCEnvironment<'db> {
    pub values: val::Environment<'db>,
    pub types: Vec<Rc<Value<'db>>>,
}

impl<'db> TCEnvironment<'db> {
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

    fn push_var(&mut self, ty: Rc<Value<'db>>) {
        let var = Rc::new(Value::variable(ty.clone(), Level::new(self.depth())));
        self.push(var, ty);
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
pub enum Error {
    TypeSynthesisFailure,
    TypeMismatch,
    EvaluationFailure(eval::Error),
    LookupError(val::LookupError),
    Misc(String),
}

type Result<T> = std::result::Result<T, Error>;

fn err<T>(message: &str) -> Result<T> {
    Err(Error::Misc(String::from(message)))
}

/// Evaluate a syntactic term to a semantic value.
fn eval<'db>(env: &TCEnvironment<'db>, term: &Syntax<'db>) -> Result<Rc<Value<'db>>> {
    let mut sem_env = env.values.clone();
    eval::eval(&mut sem_env, term).map_err(Error::EvaluationFailure)
}

/// Adaptor for running a closure from the semantic domain.
fn run_closure<'db, T>(
    env: &TCEnvironment<'db>,
    closure: &val::Closure<'db>,
    args: T,
) -> Result<Rc<Value<'db>>>
where
    T: IntoIterator<Item = Rc<Value<'db>>>,
{
    eval::run_closure(&env.values.global, closure, args).map_err(Error::EvaluationFailure)
}

fn eval_telescope<'db>(
    env: &mut TCEnvironment<'db>,
    args: impl IntoIterator<Item = Rc<Value<'db>>>,
    telescope: &stx::Telescope<'db>,
) -> Result<val::SemTelescope<'db>> {
    eval::eval_telescope(&env.values.global, args, telescope).map_err(Error::EvaluationFailure)
}

/// Synthesize (infer) types for variables and elimination forms.
pub fn type_synth<'db>(env: &mut TCEnvironment<'db>, term: &Syntax<'db>) -> Result<Rc<Value<'db>>> {
    match term {
        Syntax::Variable(variable) => type_synth_variable(env, variable),
        Syntax::Check(check) => type_synth_check(env, check),
        Syntax::Application(application) => type_synth_application(env, application),
        Syntax::Case(case) => type_synth_case(env, case),
        _ => Err(Error::TypeSynthesisFailure),
    }
}

/// Synthesize a type for a variable.
pub fn type_synth_variable<'db>(
    env: &mut TCEnvironment<'db>,
    variable: &syn::Variable,
) -> Result<Rc<Value<'db>>> {
    // Pull the type from the typing environment.
    Ok(env.var_type(variable).clone())
}

/// Synthesize the type of a term annotated with a type.
pub fn type_synth_check<'db>(
    env: &mut TCEnvironment<'db>,
    check: &syn::Check<'db>,
) -> Result<Rc<Value<'db>>> {
    let ty = eval(env, &check.ty)?;
    type_check(env, &check.term, &ty)?;
    Ok(ty)
}

/// Synthesize the type of a function application.
pub fn type_synth_application<'db>(
    env: &mut TCEnvironment<'db>,
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
    run_closure(&env, &pi.target, [arg])
}

/// Synthesize the type of a case expression.
pub fn type_synth_case<'db>(
    env: &mut TCEnvironment<'db>,
    case: &syn::Case<'db>,
) -> Result<Rc<Value<'db>>> {
    // First synthesize the type of the scrutinee.
    let scrutinee_ty = type_synth(env, &case.expr)?;

    let motive_clos = Closure::new(env.values.local.clone(), case.motive.clone());

    // Ensure that the term being matched is a datatype.
    let Value::TypeConstructor(type_constructor) = &*scrutinee_ty else {
        return Err(Error::TypeMismatch);
    };

    // Get the type constructor info.
    let type_info = env
        .values
        .global
        .type_constructor(type_constructor.constructor)
        .map_err(Error::LookupError)?;

    // Get the number of parameters.
    let num_parameters = type_info.num_parameters();

    // Create an array of parameters.
    let parameters = type_constructor.iter().take(num_parameters).cloned();

    // Check the types of the branches.
    for branch in &case.branches {
        let data_info = env
            .values
            .global
            .data_constructor(branch.constructor)
            .map_err(Error::LookupError)?;

        //let arg_types = eval_telescope(env, parameters.clone(), &data_info.arguments)?;
        //let args: Vec<Rc<Value<'_>>> = arg_types.map(|ty| env.push_var(ty));
        //let branch_scrut = Rc::new(Value::data_constructor(branch.constructor, args));
        //let branch_type = run_closure(env, &motive_clos, [branch_scrut.clone()])?;

        //type_check(
        //    env,
        //    &branch.body,
        //    &run_closure(env, motive, [branch_scrut])?,
        //)?;
    }

    todo!();
    // Evaluate the motive to a value.
    let scrutinee = eval(env, &case.expr)?;
    //let ty = run_closure(env, motive, [scrutinee]);
    //Ok(ty)
}

/// Check types of terms against an expected type.
pub fn type_check<'db>(
    env: &mut TCEnvironment<'db>,
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
    env: &mut TCEnvironment<'db>,
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

    // Check that the target type is of the same universe as the pi.
    env.push_var(sem_source_ty);
    let result = type_check(env, &pi.target, ty);
    env.pop();
    result
}

// Synthesize a type for the term, then check for equality against the expected type.
pub fn type_check_synth_term<'db>(
    env: &mut TCEnvironment<'db>,
    term: &Syntax<'db>,
    ty1: &Value<'db>,
) -> Result<()> {
    let ty2 = type_synth(env, term)?;
    check_type_equal(env, ty1, &*ty2)
}

/// Check that two types are equal.
pub fn check_type_equal<'db>(
    _env: &TCEnvironment<'db>,
    _a: &Value<'db>,
    _b: &Value<'db>,
) -> Result<()> {
    err("not implemented")
}

/// Check that the given term is a valid type.
pub fn check_type<'db>(env: &mut TCEnvironment<'db>, term: &Syntax<'db>) -> Result<()> {
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
fn check_pi_type<'db>(env: &mut TCEnvironment<'db>, pi: &stx::Pi<'db>) -> Result<()> {
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
