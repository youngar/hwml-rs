///! Renaming: preparing metavariable solutions for substitution.
use crate::*;
use hwml_core::syn::{RcSyntax, Syntax};
use hwml_core::val::{
    self, Eliminator, Environment, Flex, GlobalEnv, LocalEnv, Normal, Rigid, Value,
};
use hwml_core::*;
use std::{collections::HashMap, fmt, fmt::Display, rc::Rc, result::Result};

////////////////////////////////////////////////////////////////////////////////
/// Inversion
////////////////////////////////////////////////////////////////////////////////

/// A partial renaming from variables in one context, to variables in a different
/// context. A renaming is a substitution that maps variables to variables. The
/// renaming is partial because, it does not provide a mapping for all variables
/// under the original context.
pub struct Renaming {
    /// The number of variables in scope originally.
    pub depth: usize,
    /// A map from variables in the original scope (expressed as levels) to
    /// variables in the new scope. The number of entries in the map is the size
    /// of the new context.
    pub map: HashMap<Level, Level>,
}

impl Renaming {
    pub fn new(depth: usize) -> Renaming {
        Renaming {
            depth,
            map: HashMap::new(),
        }
    }

    pub fn source_depth(&self) -> usize {
        self.depth
    }

    pub fn target_depth(&self) -> usize {
        self.map.len()
    }

    pub fn get(&self, src: Level) -> Option<Level> {
        self.map.get(&src).cloned()
    }

    pub fn get_idx(&self, src: Level) -> Option<Index> {
        self.get(src).map(|tgt| tgt.to_index(self.depth))
    }

    pub fn under_binder<'db, R, F>(&mut self, ty: Rc<Value<'db>>, f: F) -> R
    where
        F: FnOnce(&mut Renaming, Rc<Value<'db>>) -> R,
    {
        self.depth = self.depth + 1;
        let a = Level::new(self.source_depth());
        let b = Level::new(self.target_depth());
        self.map.insert(a, b);
        let var = Rc::new(Value::variable(a, ty));
        let result = f(self, var);
        self.map.remove(&a);
        result
    }
}

#[derive(Debug, Clone)]
pub enum InversionError<'db> {
    /// Internal evaluation error.
    EvalError(eval::Error),
    /// One of the values of the substitution is not a plain variable, which prevents us from inverting the
    /// substitution. All values in the substitution must be a plain variable.
    NonInvertibleValue(usize, Rc<Value<'db>>),
    /// A variable appears as a value in the substitution more than once.
    NonLinearVariable(usize, usize, Rc<Value<'db>>),
}

impl<'db> From<eval::Error> for InversionError<'db> {
    fn from(eval_error: eval::Error) -> InversionError<'db> {
        InversionError::EvalError(eval_error)
    }
}

impl<'db> Display for InversionError<'db> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EvalError(e) => write!(f, "eval error: {:?}", e),
            Self::NonInvertibleValue(i, v) => write!(f, "non invertible value: {:?} at {}", v, i),
            Self::NonLinearVariable(i, j, v) => {
                write!(f, "non linear variable {:?} at {} and {}", v, i, j)
            }
        }
    }
}

/// Every metavariable occurence has an associated substitution. When the
/// substitution consists solely of unique variables, it forms a pattern. When a
/// metavariable with a pattern substitution appears in a unification problem,
/// we can attempt to solve the metavariable. This function checks if a
/// substitution forms a valid pattern, and if so, returns a renaming which maps
/// variables in the current context to the free variables of the metavariable.
pub fn invert_substitution<'db, 'g>(
    ctx: &SolverEnvironment<'db, 'g>,
    depth: usize,
    substitution: &LocalEnv<'db>,
) -> Result<Renaming, InversionError<'db>> {
    let mut renaming = Renaming::new(depth);
    // Each value in the substitution must be a unique variable with no eliminators.
    for (i, x) in substitution.iter().enumerate() {
        let x = force(ctx, x.clone())?;
        match &*x {
            Value::Rigid(r) if !r.spine.is_empty() => {
                if let Some(j) = renaming.map.get(&r.head.level) {
                    return Err(InversionError::NonLinearVariable(j.into(), i, x));
                }
                renaming.map.insert(r.head.level, i.into());
            }
            _ => return Err(InversionError::NonInvertibleValue(i, x)),
        };
    }
    Ok(renaming)
}

////////////////////////////////////////////////////////////////////////////////
/// Renaming
////////////////////////////////////////////////////////////////////////////////

/// A quotation error.
#[derive(Debug, Clone)]
pub enum Error<'db> {
    /// Something about the input was ill-typed, preventing quotation.
    IllTyped {
        tm: Rc<Value<'db>>,
        ty: Rc<Value<'db>>,
    },
    /// Quotation can force evaluation, which may itself prevent an error.
    EvalError(eval::Error),
    LookupError(val::LookupError<'db>),
    /// A variable occurred in the solution which was not renamed.
    ScopeError(Level),
    Occurs,
    NotAType(Rc<Value<'db>>),
}

impl<'db> From<eval::Error> for Error<'db> {
    fn from(error: eval::Error) -> Self {
        Error::EvalError(error)
    }
}

impl<'db> From<val::LookupError<'db>> for Error<'db> {
    fn from(error: val::LookupError<'db>) -> Self {
        Error::LookupError(error)
    }
}

/// Rename a normal form back into syntax. The resulting syntax is in normal form.
pub fn rename_normal<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    normal: &Normal<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    rename(db, global, meta, renaming, &normal.ty, &normal.value)
}

/// Prepare a metavariable solution by reading the solution back to syntax, and
/// renaming variables according to the renaming. Will fail if we encounter a
/// variable for which no renaming exists, or if we encounter the metavariable
/// itself. This is a fusion of the occurs check, quoting, and renaming, in a
/// single pass over the solution. The solution does not have to be in normal
/// form.
pub fn rename<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    ty: &Rc<Value<'db>>,
    value: &Rc<Value<'db>>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    match &**ty {
        Value::Universe(_) => rename_type(db, global, meta, renaming, value),
        Value::Pi(pi) => rename_pi_instance(db, global, meta, renaming, pi, value),
        Value::TypeConstructor(tcon) => {
            rename_type_constructor_instance(db, global, meta, renaming, tcon, value)
        }
        Value::Rigid(rigid) => rename_rigid_instance(db, global, meta, renaming, rigid, value),
        _ => Err(Error::IllTyped {
            tm: value.clone(),
            ty: ty.clone(),
        }),
    }
}

fn rename_pi_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    pi: &val::Pi<'db>,
    value: &Rc<Value<'db>>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    match &**value {
        Value::Lambda(lambda) => rename_lambda(db, global, meta, renaming, pi, lambda),
        Value::Rigid(rigid) => rename_rigid(db, global, meta, renaming, rigid),
        Value::Flex(flex) => rename_flex(db, global, meta, renaming, flex),
        _ => Err(Error::IllTyped {
            tm: value.clone(),
            ty: Rc::new(Value::Pi(pi.clone())),
        }),
    }
}

fn rename_type_constructor_instance<'db>(
    _db: &'db dyn salsa::Database,
    _global: &GlobalEnv<'db>,
    _meta: MetaVariableId,
    _renaming: &mut Renaming,
    _ty: &val::TypeConstructor<'db>,
    _value: &Value<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    todo!();
}

fn rename_rigid_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    ty: &val::Rigid<'db>,
    value: &Value<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    match value {
        Value::Rigid(rigid) => rename_rigid(db, global, meta, renaming, rigid),
        _ => Err(Error::IllTyped {
            tm: Rc::new(value.clone()),
            ty: Rc::new(Value::Rigid(ty.clone())),
        }),
    }
}

////////////////////////////////////////////////////////////////////////////////
/// Types
////////////////////////////////////////////////////////////////////////////////

pub fn rename_type<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    value: &Value<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    match value {
        Value::Universe(universe) => rename_universe(db, global, meta, renaming, universe),
        Value::Pi(pi) => rename_pi(db, global, meta, renaming, pi),
        Value::TypeConstructor(tcon) => rename_type_constructor(db, global, meta, renaming, tcon),
        Value::Rigid(rigid) => rename_rigid(db, global, meta, renaming, rigid),
        Value::Flex(flex) => rename_flex(db, global, meta, renaming, flex),
        _ => Err(Error::NotAType(Rc::new(value.clone()))),
    }
}

fn rename_universe<'db>(
    _db: &'db dyn salsa::Database,
    _global: &GlobalEnv<'db>,
    _meta: MetaVariableId,
    _renaming: &mut Renaming,
    universe: &val::Universe,
) -> Result<RcSyntax<'db>, Error<'db>> {
    Ok(Syntax::universe_rc(universe.level))
}

fn rename_pi<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    pi: &val::Pi<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    let sem_source = &pi.source;
    let sem_target_closure = &pi.target;
    let syn_source = rename_type(db, global, meta, renaming, &sem_source)?;
    let syn_target = renaming.under_binder(sem_source.clone(), |renaming, var| {
        let sem_target = eval::run_closure(global, &sem_target_closure, [var])?;
        rename_type(db, global, meta, renaming, &sem_target)
    })?;
    Ok(Rc::new(Syntax::pi(syn_source, syn_target)))
}

fn rename_type_constructor<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    tcon: &val::TypeConstructor<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    let type_info = global.type_constructor(tcon.constructor)?.clone();
    let mut env = Environment {
        global: global,
        local: LocalEnv::new(),
    };
    let mut syn_args = Vec::new();
    for (sem_arg, syn_arg_ty) in tcon.iter().zip(type_info.arguments.iter()) {
        let sem_arg_ty = eval::eval(&mut env, &syn_arg_ty)?;
        let syn_arg = rename(db, global, meta, renaming, &sem_arg_ty, sem_arg)?;
        syn_args.push(syn_arg);
        env.push(sem_arg.clone());
    }
    Ok(Syntax::type_constructor_rc(tcon.constructor, syn_args))
}

////////////////////////////////////////////////////////////////////////////////
/// Terms
////////////////////////////////////////////////////////////////////////////////

fn rename_lambda<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    sem_pi: &val::Pi<'db>,
    sem_lambda: &val::Lambda<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    let val::Pi {
        source: sem_source,
        target: sem_target_closure,
    } = sem_pi;
    let syn_body: Rc<Syntax<'db>> =
        renaming.under_binder(sem_source.clone(), |renaming, var| {
            let sem_body_ty: Rc<Value<'db>> =
                eval::run_closure(global, sem_target_closure, [var.clone()])?;
            let sem_body: Rc<Value<'db>> = eval::apply_lambda(global, sem_lambda, var)?;
            rename(db, global, meta, renaming, &sem_body_ty, &sem_body)
        })?;
    Ok(Rc::new(Syntax::lambda(syn_body)))
}

fn rename_rigid<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    rigid: &Rigid<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    let head = rename_variable(db, meta, renaming, &rigid.head)?;
    rename_spine(db, global, meta, renaming, head, &rigid.spine)
}

fn rename_flex<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    flex: &Flex<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    let head = rename_metavariable(db, global, meta, renaming, &flex.head)?;
    rename_spine(db, global, meta, renaming, head, &flex.spine)
}

fn rename_data_constructor<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    type_constructor: &val::TypeConstructor<'db>,
    sem_data: &val::DataConstructor<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    let constructor = sem_data.constructor;
    let type_info = global
        .type_constructor(type_constructor.constructor)
        .map_err(Error::LookupError)?
        .clone();
    let data_info = global
        .data_constructor(constructor)
        .map_err(Error::LookupError)?
        .clone();
    let num_parameters = type_info.num_parameters();
    let parameters = type_constructor.iter().take(num_parameters).cloned();
    let mut env = Environment {
        global: global,
        local: LocalEnv::new(),
    };
    env.extend(parameters);
    let mut syn_args = Vec::new();
    for (sem_arg, syn_arg_ty) in sem_data.iter().zip(data_info.arguments.bindings) {
        let sem_arg_ty = eval::eval(&mut env, &syn_arg_ty)?;
        let syn_arg = rename(db, global, meta, renaming, &sem_arg_ty, &sem_arg)?;
        syn_args.push(syn_arg);
        env.push(sem_arg.clone());
    }
    Ok(Syntax::data_constructor_rc(constructor, syn_args))
}

////////////////////////////////////////////////////////////////////////////////
/// Eliminators and Spines
////////////////////////////////////////////////////////////////////////////////

fn rename_spine<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    mut head: Rc<Syntax<'db>>,
    spine: &val::Spine<'db>,
) -> Result<Rc<Syntax<'db>>, Error<'db>> {
    for eliminator in spine.iter() {
        head = rename_eliminator(db, global, meta, renaming, head, eliminator)?;
    }
    Ok(head)
}

fn rename_eliminator<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    head: RcSyntax<'db>,
    eliminator: &Eliminator<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    match eliminator {
        Eliminator::Application(app) => rename_application(db, global, meta, renaming, head, app),
        Eliminator::Case(case) => rename_case(db, global, meta, renaming, head, case),
    }
}

fn rename_application<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    head: RcSyntax<'db>,
    app: &val::Application<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    let sem_arg = &app.argument;
    let syn_arg = rename_normal(db, global, meta, renaming, sem_arg)?;
    Ok(Syntax::application_rc(head, syn_arg))
}

fn rename_case<'db>(
    _db: &'db dyn salsa::Database,
    _global: &GlobalEnv<'db>,
    _meta: MetaVariableId,
    _renaming: &mut Renaming,
    _head: RcSyntax<'db>,
    _case: &val::Case<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    todo!();
}

////////////////////////////////////////////////////////////////////////////////
/// Variables and Meta Variables
////////////////////////////////////////////////////////////////////////////////

fn rename_variable<'db>(
    _db: &'db dyn salsa::Database,
    _meta: MetaVariableId,
    renaming: &Renaming,
    sem_var: &val::Variable,
) -> Result<RcSyntax<'db>, Error<'db>> {
    let Some(idx) = renaming.get_idx(sem_var.level) else {
        return Err(Error::ScopeError(sem_var.level));
    };
    Ok(Rc::new(Syntax::variable(idx)))
}

fn rename_metavariable<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    sem_meta: &val::MetaVariable<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    if sem_meta.id == meta {
        return Err(Error::Occurs);
    }
    let info = global.metavariable(sem_meta.id).unwrap();
    let substitution =
        rename_substitution(db, global, meta, renaming, &info.arguments, &sem_meta.local)?;
    Ok(Syntax::metavariable_rc(sem_meta.id, substitution))
}

fn rename_substitution<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    tys: &syn::Telescope<'db>,
    sem_substitution: &LocalEnv<'db>,
) -> Result<Vec<RcSyntax<'db>>, Error<'db>> {
    let mut env = Environment {
        global: global,
        local: LocalEnv::new(),
    };
    let mut syn_substitution = Vec::new();
    for (sem_arg, syn_arg_ty) in sem_substitution.iter().zip(tys.iter()) {
        let sem_arg_ty = eval::eval(&mut env, &syn_arg_ty)?;
        let syn_arg = rename(db, global, meta, renaming, &sem_arg_ty, sem_arg)?;
        syn_substitution.push(syn_arg);
        env.push(sem_arg.clone());
    }
    Ok(syn_substitution)
}
