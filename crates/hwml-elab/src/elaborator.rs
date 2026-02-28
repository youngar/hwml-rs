use crate::engine::*;
use hwml_core::{syn, val, Database};
use hwml_surface::syntax;
use std::rc::Rc;
use syn::Syntax;
use val::Value;

#[derive(Clone, Debug)]
pub struct Expected(Vec<&'static str>);

#[derive(Clone, Debug)]
pub enum ElabError {
    UnhandledStatement(syntax::Statement),
    UnhandledExpression(syntax::Expression),
    Unexpected(syntax::Expression, Expected),
    Generic(&'static str),
}

pub type ElabResult<A> = Result<A, ElabError>;

pub struct ElabState<'db> {
    db: &'db Database,
    global_env: val::GlobalEnv<'db>,
    solver: SolverState<'db>,
}

impl<'db> ElabState<'db> {
    pub fn new(db: &'db Database) -> Self {
        ElabState {
            db,
            global_env: val::GlobalEnv::new(),
            solver: SolverState::new(),
        }
    }
}

pub fn elab_program<'db>(
    db: &'db Database,
    program: &syntax::Program,
) -> ElabResult<val::GlobalEnv<'db>> {
    let mut state = ElabState::new(db);
    for statement in &program.statements {
        match elab_statement(&mut state, statement) {
            Ok(()) => continue,
            Err(e) => return Err(e),
        }
    }
    Ok(state.global_env)
}

pub fn elab_statement<'db>(
    state: &mut ElabState<'db>,
    statement: &syntax::Statement,
) -> ElabResult<()> {
    match statement {
        syntax::Statement::Def(def) => elab_def(state, def),
        _ => Result::Err(ElabError::UnhandledStatement(statement.clone())),
    }
}

fn elab_def<'db>(state: &mut ElabState<'db>, def: &syntax::Def) -> ElabResult<()> {
    let mut local_env = val::LocalEnv::new();

    // for group in def.bindings.groups {
    //     let ty = match group {
    //         syntax::BindingGroup::Typed(group) => {
    //             // when the group is typed, elaborate the type.
    //             let ty = elab_type(state, local_env, group.)?'
    //         },
    //         syntax::BindingGroup::Untyped(group) => todo!(),
    //     };
    //     let ty = check_expr(state, group.)
    // }

    Result::Err(ElabError::UnhandledStatement(syntax::Statement::Def(
        def.clone(),
    )))
}

struct Arg {}

struct Args {}

fn elab_def_bindings<'db>(state: &mut ElabState<'db>) {}

struct ElabExpState<'db> {
    global_state: ElabState<'db>,
}

struct Check<'db> {
    tm: val::Value<'db>,
}

type CheckResult<'db> = ElabResult<Check<'db>>;

fn check_exp<'db>(
    _state: &mut ElabState<'db>,
    exp: &syntax::Expression,
    ty: &Rc<val::Value>,
) -> CheckResult<'db> {
    match exp {
        exp => Err(ElabError::UnhandledExpression(exp.clone())),
    }
}

struct Infer<'db> {
    tm: val::Value<'db>,
    ty: val::Value<'db>,
}

type InferResult<'db> = ElabResult<Infer<'db>>;

fn infer_exp<'db>(_state: &mut ElabState<'db>, exp: &syntax::Expression) -> ElabResult<Infer<'db>> {
    match exp {
        _ => todo!(),
    }
}

struct ElabTy<'db> {
    ty: Rc<Value<'db>>,
    level: hwml_core::UniverseLevel,
}

type ElabTyResult<'db> = ElabResult<ElabTy<'db>>;

fn elab_ty<'db>(_state: &mut ElabState<'db>, exp: &syntax::Expression) -> ElabResult<Value<'db>> {
    match exp {
        // syntax::Expression::Pi(pi) => elab_pi_type(pi),
        _ => Err(ElabError::Unexpected(exp.clone(), Expected(vec!["type"]))),
    }
}
