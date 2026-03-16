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

    pub fn under_binder<'db, R, F>(&mut self, ty: RcValue<'db>, f: F) -> R
    where
        F: FnOnce(&mut Renaming, RcValue<'db>) -> R,
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
    NonInvertibleValue(usize, RcValue<'db>),
    /// A variable appears as a value in the substitution more than once.
    NonLinearVariable(usize, usize, RcValue<'db>),
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
            // A plain variable has an empty spine (no eliminators applied)
            Value::Rigid(r) if r.spine.is_empty() => {
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
        tm: RcValue<'db>,
        ty: RcValue<'db>,
    },
    /// Quotation can force evaluation, which may itself prevent an error.
    EvalError(eval::Error),
    LookupError(val::LookupError<'db>),
    /// A variable occurred in the solution which was not renamed.
    ScopeError(Level),
    Occurs,
    NotAType(RcValue<'db>),
    /// Case scrutinee must be a variable (not a complex expression).
    CaseScrutineeMustBeVariable,
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
    ty: &RcValue<'db>,
    value: &RcValue<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    match &**ty {
        Value::Universe(_) => rename_type(db, global, meta, renaming, value),
        Value::Pi(pi) => rename_pi_instance(db, global, meta, renaming, pi, value),
        Value::TypeConstructor(tcon) => {
            rename_type_constructor_instance(db, global, meta, renaming, tcon, value)
        }
        // Hardware-level types
        Value::Lift(lift) => rename_lift_instance(db, global, meta, renaming, lift, value),
        Value::HardwareUniverse(_) => rename_hwuniverse_instance(db, global, meta, renaming, value),
        Value::SignalUniverse(_) => {
            rename_signal_universe_instance(db, global, meta, renaming, value)
        }
        Value::ModuleUniverse(_) => {
            rename_module_universe_instance(db, global, meta, renaming, value)
        }
        Value::SLift(slift) => rename_slift_instance(db, global, meta, renaming, slift, value),
        Value::MLift(mlift) => rename_mlift_instance(db, global, meta, renaming, mlift, value),
        Value::Bit(_) => rename_bit_instance(db, global, meta, renaming, value),
        Value::HArrow(harrow) => rename_harrow_instance(db, global, meta, renaming, harrow, value),
        // Neutral types
        Value::Prim(_) | Value::Constant(_) => {
            rename_neutral_instance(db, global, meta, renaming, value)
        }
        Value::Rigid(rigid) => rename_rigid_instance(db, global, meta, renaming, rigid, value),
        Value::Flex(flex) => rename_flex_instance(db, global, meta, renaming, flex, value),
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
    value: &RcValue<'db>,
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
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    tcon: &val::TypeConstructor<'db>,
    value: &Value<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    match value {
        Value::DataConstructor(dcon) => {
            rename_data_constructor(db, global, meta, renaming, tcon, dcon)
        }
        Value::Prim(prim) => rename_prim(prim),
        Value::Constant(constant) => rename_constant(constant),
        Value::Rigid(rigid) => rename_rigid(db, global, meta, renaming, rigid),
        Value::Flex(flex) => rename_flex(db, global, meta, renaming, flex),
        _ => Err(Error::IllTyped {
            tm: Rc::new(value.clone()),
            ty: Rc::new(Value::TypeConstructor(tcon.clone())),
        }),
    }
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
        Value::Flex(flex) => rename_flex(db, global, meta, renaming, flex),
        _ => Err(Error::IllTyped {
            tm: Rc::new(value.clone()),
            ty: Rc::new(Value::Rigid(ty.clone())),
        }),
    }
}

fn rename_flex_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    ty: &val::Flex<'db>,
    value: &Value<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    match value {
        Value::Rigid(rigid) => rename_rigid(db, global, meta, renaming, rigid),
        Value::Flex(flex) => rename_flex(db, global, meta, renaming, flex),
        _ => Err(Error::IllTyped {
            tm: Rc::new(value.clone()),
            ty: Rc::new(Value::Flex(ty.clone())),
        }),
    }
}

fn rename_neutral_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    value: &RcValue<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    match &**value {
        Value::Prim(prim) => rename_prim(prim),
        Value::Constant(constant) => rename_constant(constant),
        Value::Rigid(rigid) => rename_rigid(db, global, meta, renaming, rigid),
        Value::Flex(flex) => rename_flex(db, global, meta, renaming, flex),
        _ => Err(Error::IllTyped {
            tm: value.clone(),
            ty: value.clone(),
        }),
    }
}

////////////////////////////////////////////////////////////////////////////////
/// Hardware-Level Instance Functions
////////////////////////////////////////////////////////////////////////////////

fn rename_lift_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    lift: &val::Lift<'db>,
    value: &RcValue<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    // Lift's inner type determines what kind of values we expect
    match lift.ty.as_ref() {
        Value::SLift(slift) => rename_slift_instance(db, global, meta, renaming, slift, value),
        Value::MLift(mlift) => rename_mlift_instance(db, global, meta, renaming, mlift, value),
        _ => Err(Error::IllTyped {
            tm: value.clone(),
            ty: Rc::new(Value::Lift(lift.clone())),
        }),
    }
}

fn rename_hwuniverse_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    value: &RcValue<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    // HardwareUniverse has two type constructors: SLift and MLift
    match &**value {
        Value::SLift(slift) => rename_slift(db, global, meta, renaming, slift),
        Value::MLift(mlift) => rename_mlift(db, global, meta, renaming, mlift),
        Value::Prim(prim) => rename_prim(prim),
        Value::Constant(constant) => rename_constant(constant),
        Value::Rigid(rigid) => rename_rigid(db, global, meta, renaming, rigid),
        Value::Flex(flex) => rename_flex(db, global, meta, renaming, flex),
        _ => Err(Error::IllTyped {
            tm: value.clone(),
            ty: Rc::new(Value::HardwareUniverse(val::HardwareUniverse::new())),
        }),
    }
}

fn rename_signal_universe_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    value: &RcValue<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    // SignalUniverse has Bit as its type constructor
    match &**value {
        Value::Bit(_) => Ok(Syntax::bit_rc()),
        Value::Prim(prim) => rename_prim(prim),
        Value::Constant(constant) => rename_constant(constant),
        Value::Rigid(rigid) => rename_rigid(db, global, meta, renaming, rigid),
        Value::Flex(flex) => rename_flex(db, global, meta, renaming, flex),
        _ => Err(Error::IllTyped {
            tm: value.clone(),
            ty: Rc::new(Value::SignalUniverse(val::SignalUniverse::new())),
        }),
    }
}

fn rename_module_universe_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    value: &RcValue<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    // ModuleUniverse has HArrow as its type constructor
    match &**value {
        Value::HArrow(harrow) => rename_harrow(db, global, meta, renaming, harrow),
        Value::Prim(prim) => rename_prim(prim),
        Value::Constant(constant) => rename_constant(constant),
        Value::Rigid(rigid) => rename_rigid(db, global, meta, renaming, rigid),
        Value::Flex(flex) => rename_flex(db, global, meta, renaming, flex),
        _ => Err(Error::IllTyped {
            tm: value.clone(),
            ty: Rc::new(Value::ModuleUniverse(val::ModuleUniverse::new())),
        }),
    }
}

fn rename_slift_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    slift: &val::SLift<'db>,
    value: &RcValue<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    // SLift wraps a signal type (like Bit)
    match slift.ty.as_ref() {
        Value::Bit(_) => rename_bit_instance(db, global, meta, renaming, value),
        _ => Err(Error::IllTyped {
            tm: value.clone(),
            ty: Rc::new(Value::SLift(slift.clone())),
        }),
    }
}

fn rename_mlift_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    mlift: &val::MLift<'db>,
    value: &RcValue<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    // MLift wraps a module type (like HArrow)
    match mlift.ty.as_ref() {
        Value::HArrow(harrow) => rename_harrow_instance(db, global, meta, renaming, harrow, value),
        _ => Err(Error::IllTyped {
            tm: value.clone(),
            ty: Rc::new(Value::MLift(mlift.clone())),
        }),
    }
}

fn rename_bit_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    value: &RcValue<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    match &**value {
        Value::Zero(_) => Ok(Syntax::zero_rc()),
        Value::One(_) => Ok(Syntax::one_rc()),
        Value::Prim(prim) => rename_prim(prim),
        Value::Constant(constant) => rename_constant(constant),
        Value::Rigid(rigid) => rename_rigid(db, global, meta, renaming, rigid),
        Value::Flex(flex) => rename_flex(db, global, meta, renaming, flex),
        _ => Err(Error::IllTyped {
            tm: value.clone(),
            ty: Rc::new(Value::Bit(val::Bit::new())),
        }),
    }
}

fn rename_harrow_instance<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    harrow: &val::HArrow<'db>,
    value: &RcValue<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    match &**value {
        Value::Module(module) => rename_module(db, global, meta, renaming, harrow, module),
        Value::Prim(prim) => rename_prim(prim),
        Value::Constant(constant) => rename_constant(constant),
        Value::Rigid(rigid) => rename_rigid(db, global, meta, renaming, rigid),
        Value::Flex(flex) => rename_flex(db, global, meta, renaming, flex),
        _ => Err(Error::IllTyped {
            tm: value.clone(),
            ty: Rc::new(Value::HArrow(harrow.clone())),
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
        Value::Lift(lift) => rename_lift(db, global, meta, renaming, lift),
        Value::HardwareUniverse(_) => Ok(Syntax::hardware_rc()),
        Value::SLift(slift) => rename_slift(db, global, meta, renaming, slift),
        Value::MLift(mlift) => rename_mlift(db, global, meta, renaming, mlift),
        Value::SignalUniverse(_) => Ok(Syntax::signal_universe_rc()),
        Value::Bit(_) => Ok(Syntax::bit_rc()),
        Value::ModuleUniverse(_) => Ok(Syntax::module_universe_rc()),
        Value::HArrow(harrow) => rename_harrow(db, global, meta, renaming, harrow),
        Value::Prim(prim) => rename_prim(prim),
        Value::Constant(constant) => rename_constant(constant),
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
    Ok(Rc::new(Syntax::pi(
        syn_source,
        hwml_core::binding::Binding::new(syn_target),
    )))
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
        transparent: val::TransparentEnv::new(),
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

fn rename_lift<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    lift: &val::Lift<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    let ty = rename_type(db, global, meta, renaming, &lift.ty)?;
    Ok(Syntax::lift_rc(ty))
}

fn rename_slift<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    slift: &val::SLift<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    let ty = rename_type(db, global, meta, renaming, &slift.ty)?;
    Ok(Syntax::slift_rc(ty))
}

fn rename_mlift<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    mlift: &val::MLift<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    let ty = rename_type(db, global, meta, renaming, &mlift.ty)?;
    Ok(Syntax::mlift_rc(ty))
}

fn rename_harrow<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    harrow: &val::HArrow<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    let sem_source = &harrow.source;
    let sem_target_closure = &harrow.target;
    let syn_source = rename_type(db, global, meta, renaming, &sem_source)?;
    let syn_target = renaming.under_binder(sem_source.clone(), |renaming, var| {
        let sem_target = eval::run_closure(global, &sem_target_closure, [var])?;
        rename_type(db, global, meta, renaming, &sem_target)
    })?;
    Ok(Syntax::harrow_rc(syn_source, syn_target))
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
    let syn_body: RcSyntax<'db> = renaming.under_binder(sem_source.clone(), |renaming, var| {
        let sem_body_ty: RcValue<'db> =
            eval::run_closure(global, sem_target_closure, [var.clone()])?;
        let sem_body: RcValue<'db> = eval::apply_lambda(global, sem_lambda, var)?;
        rename(db, global, meta, renaming, &sem_body_ty, &sem_body)
    })?;
    Ok(Rc::new(Syntax::lambda(hwml_core::binding::Binding::new(
        syn_body,
    ))))
}

fn rename_module<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    sem_harrow: &val::HArrow<'db>,
    sem_module: &val::Module<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    let val::HArrow {
        source: sem_source,
        target: sem_target_closure,
    } = sem_harrow;
    let syn_body: RcSyntax<'db> = renaming.under_binder(sem_source.clone(), |renaming, var| {
        let sem_body_ty: RcValue<'db> =
            eval::run_closure(global, sem_target_closure, [var.clone()])?;
        let sem_body: RcValue<'db> = eval::run_closure(global, &sem_module.body, [var])?;
        rename(db, global, meta, renaming, &sem_body_ty, &sem_body)
    })?;
    Ok(Syntax::module_rc(hwml_core::binding::Binding::new(
        syn_body,
    )))
}

fn rename_prim<'db>(prim: &hwml_core::val::Prim<'db>) -> Result<RcSyntax<'db>, Error<'db>> {
    Ok(Syntax::prim_rc(prim.name))
}

fn rename_constant<'db>(
    constant: &hwml_core::val::Constant<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    Ok(Syntax::constant_rc(constant.name))
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
        transparent: val::TransparentEnv::new(),
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
    mut head: RcSyntax<'db>,
    spine: &val::Spine<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
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

/// Rename a case eliminator.
///
/// Case expressions are check-only, so there's no return type to rename.
/// We use a placeholder type for renaming branch bodies.
fn rename_case<'db>(
    db: &'db dyn salsa::Database,
    global: &GlobalEnv<'db>,
    meta: MetaVariableId,
    renaming: &mut Renaming,
    head: RcSyntax<'db>,
    case: &val::Case<'db>,
) -> Result<RcSyntax<'db>, Error<'db>> {
    // The scrutinee must be a variable (not an arbitrary expression).
    // The `head` is the already-renamed head of the neutral term, which should
    // always be a Variable. Extract its Index for the Case syntax.
    let scrutinee_index = match head.as_ref() {
        Syntax::Variable(var) => var.index,
        _ => return Err(Error::CaseScrutineeMustBeVariable),
    };

    let parameters = &case.parameters;

    // No return_type in case anymore - case is check-only.
    // For renaming branch bodies, we use a placeholder type.
    // TODO: Thread the expected type through when we have check-only renaming.
    let placeholder_ty = Rc::new(Value::Universe(val::Universe::new(UniverseLevel::new(0))));
    let branch_ty = &placeholder_ty;

    let mut branches = Vec::new();
    for branch in &case.branches {
        let data_info = global.data_constructor(branch.constructor)?.clone();

        // Create an instance of this data constructor
        let dcon_arg_tys = eval::eval_telescope(global, parameters.clone(), &data_info.arguments)?;
        let mut dcon_args = Vec::new();
        for ty in dcon_arg_tys.types {
            dcon_args.push(Rc::new(Value::variable(
                Level::new(renaming.source_depth() + dcon_args.len()),
                ty,
            )));
        }

        // Evaluate the branch body closure
        let branch_val = eval::run_closure(global, &branch.body, dcon_args)?;

        // Rename the branch body with extended renaming
        // We need to extend the renaming for the constructor arguments
        let branch_syn = {
            // Temporarily extend renaming depth for each constructor argument
            let original_depth = renaming.depth;
            for i in 0..branch.arity {
                let src_level = Level::new(original_depth + i);
                let tgt_level = Level::new(renaming.map.len());
                renaming.map.insert(src_level, tgt_level);
            }
            renaming.depth = original_depth + branch.arity;

            let result = rename(db, global, meta, renaming, branch_ty, &branch_val)?;

            // Restore the renaming
            for i in 0..branch.arity {
                let src_level = Level::new(original_depth + i);
                renaming.map.remove(&src_level);
            }
            renaming.depth = original_depth;

            result
        };

        branches.push(syn::CaseBranch::new(
            branch.constructor,
            hwml_core::binding::DynBinding::new(branch.arity, branch_syn),
        ));
    }

    // No return_type to rename - case expressions are check-only
    Ok(Syntax::case_rc(scrutinee_index, branches))
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
        transparent: val::TransparentEnv::new(),
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

////////////////////////////////////////////////////////////////////////////////
/// Tests
////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use super::*;
    use hwml_core::syn::print::print_syntax_to_string;
    use hwml_core::test_utils::eval_str;
    use hwml_core::Database;

    /// Test context with database and global environment for concise tests.
    struct Ctx<'db> {
        db: &'db Database,
        global: GlobalEnv<'db>,
    }

    impl<'db> Ctx<'db> {
        fn new(db: &'db Database) -> Self {
            Self {
                db,
                global: GlobalEnv::new(),
            }
        }

        /// Parse and evaluate a string to a value
        fn eval(&self, input: &'db str) -> RcValue<'db> {
            eval_str(self.db, &self.global, input)
        }

        /// Create an identity renaming at depth 0 (empty map)
        fn identity_renaming(&self) -> Renaming {
            Renaming::new(0)
        }

        /// Create a dummy MetaVariableId for testing
        fn dummy_meta(&self) -> MetaVariableId {
            MetaVariableId::new(0)
        }

        /// Parse, evaluate term and type, rename the term at the type, return string
        fn rename_at(&self, term: &'db str, ty: &'db str) -> String {
            let term_val = self.eval(term);
            let ty_val = self.eval(ty);
            let mut renaming = self.identity_renaming();
            let syntax = rename(
                self.db,
                &self.global,
                self.dummy_meta(),
                &mut renaming,
                &ty_val,
                &term_val,
            )
            .expect("rename failed");
            print_syntax_to_string(self.db, &syntax)
        }

        /// Parse, evaluate a type, and rename_type, returning a string
        fn rename_type_str(&self, term: &'db str) -> String {
            let val = self.eval(term);
            let mut renaming = self.identity_renaming();
            let syntax = rename_type(
                self.db,
                &self.global,
                self.dummy_meta(),
                &mut renaming,
                &val,
            )
            .expect("rename_type failed");
            print_syntax_to_string(self.db, &syntax)
        }
    }

    // =========================================================================
    // Type Renaming Tests
    // =========================================================================

    #[test]
    fn test_rename_universes() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.rename_type_str("U0"), "𝒰0");
        assert_eq!(c.rename_type_str("U1"), "𝒰1");
    }

    #[test]
    fn test_rename_hardware_universes() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.rename_type_str("HardwareUniverse"), "HardwareUniverse");
        assert_eq!(c.rename_type_str("SignalUniverse"), "SignalUniverse");
        assert_eq!(c.rename_type_str("ModuleUniverse"), "ModuleUniverse");
    }

    #[test]
    fn test_rename_bit() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.rename_type_str("Bit"), "Bit");
    }

    #[test]
    fn test_rename_pi_types() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.rename_type_str("∀ (%x : U0) → U0"), "∀ (%0 : 𝒰0) → 𝒰0");
        assert_eq!(
            c.rename_type_str("∀ (%x : U0) (%y : U0) → U0"),
            "∀ (%0 : 𝒰0) (%1 : 𝒰0) → 𝒰0"
        );
    }

    #[test]
    fn test_rename_harrow_types() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.rename_type_str("Bit → Bit"), "Bit → Bit");
    }

    #[test]
    fn test_rename_lift() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.rename_type_str("^Bit"), "^Bit");
    }

    #[test]
    fn test_rename_slift() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.rename_type_str("^sBit"), "^sBit");
    }

    #[test]
    fn test_rename_mlift() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.rename_type_str("^m(Bit → Bit)"), "^m(Bit → Bit)");
    }

    // =========================================================================
    // Instance Renaming Tests
    // =========================================================================

    #[test]
    fn test_rename_bit_values() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.rename_at("0", "Bit"), "0");
        assert_eq!(c.rename_at("1", "Bit"), "1");
    }

    #[test]
    fn test_rename_lambda() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.rename_at("λ %x → %x", "∀ (%x : U0) → U0"), "λ %0 → %0");
    }

    #[test]
    fn test_rename_module() {
        let db = Database::new();
        let c = Ctx::new(&db);
        assert_eq!(c.rename_at("mod %x → %x", "Bit → Bit"), "mod %0 → %0");
    }
}
