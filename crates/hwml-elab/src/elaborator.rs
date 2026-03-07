use crate::engine::*;
use hwml_core::*;
use hwml_surface::syntax;
use std::rc::Rc;
use syn::Syntax;
use val::Value;

pub struct ElabSignature<'db> {
    env: val::GlobalEnv<'db>,
}

impl<'db> ElabSignature<'db> {
    pub fn resolve(&self, name: Name<'db>) -> Option<TypedSyntax<'db>> {
        // TODO: This should be returning a "boundary" (?).
        match self.env.constant(name) {
            Err(_) => None,
            Ok(_info) => Some(TypedSyntax {
                ty: todo!("info.ty.clone()"),
                subject: Syntax::constant_rc(name),
            }),
        }
    }
}

struct ElabLocals<'db> {
    names: Vec<Option<Name<'db>>>,
    tys: Vec<Rc<Value<'db>>>,
    values: Vec<Rc<Value<'db>>>,
}

impl<'db> ElabLocals<'db> {
    pub fn new() -> Self {
        ElabLocals {
            names: Vec::new(),
            tys: Vec::new(),
            values: Vec::new(),
        }
    }

    pub fn depth(&self) -> usize {
        self.names.len()
    }

    pub fn resolve_level(&self, name: &Name) -> Option<Level> {
        for i in (0..self.depth()).rev() {
            if let Some(n) = self.names[i] {
                if n == *name {
                    return Some(Level(i));
                }
            }
        }
        None
    }

    pub fn resolve_index(&self, name: &Name<'db>) -> Option<Index> {
        self.resolve_level(name)
            .map(|level| level.to_index(self.depth()))
    }

    pub fn name(&self, Level(i): Level) -> Option<Name<'db>> {
        self.names[i]
    }

    pub fn value(&self, Level(i): Level) -> &Rc<Value<'db>> {
        &self.values[i]
    }

    pub fn ty(&self, Level(i): Level) -> &Rc<Value<'db>> {
        &self.tys[i]
    }

    pub fn resolve(&self, name: &Name<'db>) -> Option<TypedSyntax<'db>> {
        match self.resolve_level(name) {
            Some(level) => {
                let ty = self.ty(level).clone();
                let subject = Syntax::variable_rc(level.to_index(self.depth()));
                Some(TypedSyntax { ty, subject })
            }
            None => None,
        }
    }

    pub fn bind(&mut self, name: &Name<'db>, ty: Rc<Value<'db>>) -> Level {
        let level = Level(self.depth());
        self.names.push(Some(*name));
        self.tys.push(ty.clone());
        self.values.push(Rc::new(Value::variable(level, ty)));
        level
    }
}

impl<'db> Into<val::LocalEnv<'db>> for &ElabLocals<'db> {
    fn into(self) -> val::LocalEnv<'db> {
        val::LocalEnv {
            locals: self.values.clone(),
        }
    }
}

struct ElabSink {}

pub struct ElabEnv<'db> {
    db: &'db Database,
    signature: ElabSignature<'db>,
    namespace: Path<'db>,
    locals: ElabLocals<'db>,
}

impl<'db> ElabEnv<'db> {
    pub fn new(db: &'db Database, signature: ElabSignature<'db>, namespace: Path<'db>) -> Self {
        ElabEnv {
            db,
            namespace,
            signature,
            locals: ElabLocals::new(),
        }
    }

    pub fn resolve_global(&self, name: Name<'db>) -> Option<TypedSyntax<'db>> {
        self.signature.resolve(name)
    }

    pub fn resolve_local(&self, name: Name<'db>) -> Option<TypedSyntax<'db>> {
        self.locals.resolve(&name)
    }

    pub fn resolve(&self, name: Name<'db>) -> Option<TypedSyntax<'db>> {
        if let Some(typed_stx) = self.locals.resolve(&name) {
            return Some(typed_stx);
        }
        self.signature.resolve(name)
    }

    pub async fn eval_env<'a>(&'a self) -> val::Environment<'db, 'a> {
        val::Environment {
            global: &self.signature.env,
            local: val::LocalEnv {
                locals: self.locals.values.clone(),
            },
        }
    }
}

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
