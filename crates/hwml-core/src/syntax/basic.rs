use crate::db::Index;
use std::rc::Rc;

#[derive(Copy, Clone, Debug)]
pub struct NameId(pub u32);

pub type RcSyntax = Rc<Syntax>;

pub type Tm = Syntax;
pub type Ty = Syntax;

/// A captured environment.
#[derive(Clone, Debug)]
pub struct Closure {
    /// The environment contains a vector of definitions.
    pub values: Vec<RcSyntax>,
}

#[derive(Clone, Debug)]
pub struct Environment {
    pub types: Vec<RcSyntax>,
}

#[derive(Clone, Debug)]
pub enum Syntax {
    Constant(Constant),
    Variable(Variable),
    Check(Check),
    Pi(Pi),
    Lambda(Lambda),
    Application(Application),
    Universe(Universe),
    MetaVariable(MetaVariable),
}

impl Syntax {
    pub fn constant(name: NameId) -> Syntax {
        Syntax::Constant(Constant::new(name))
    }

    pub fn constant_rc(name: NameId) -> RcSyntax {
        Rc::new(Syntax::constant(name))
    }

    pub fn variable(index: Index) -> Syntax {
        Syntax::Variable(Variable::new(index))
    }

    pub fn variable_rc(index: Index) -> RcSyntax {
        Rc::new(Syntax::variable(index))
    }

    pub fn check(ty: RcSyntax, term: RcSyntax) -> Syntax {
        Syntax::Check(Check::new(ty, term))
    }

    pub fn check_rc(ty: RcSyntax, term: RcSyntax) -> RcSyntax {
        Rc::new(Syntax::check(ty, term))
    }

    pub fn pi(source: RcSyntax, target: RcSyntax) -> Syntax {
        Syntax::Pi(Pi::new(source, target))
    }

    pub fn pi_rc(source: RcSyntax, target: RcSyntax) -> RcSyntax {
        Rc::new(Syntax::pi(source, target))
    }

    pub fn lambda(body: RcSyntax) -> Syntax {
        Syntax::Lambda(Lambda::new(body))
    }

    pub fn lambda_rc(body: RcSyntax) -> RcSyntax {
        Rc::new(Syntax::lambda(body))
    }

    pub fn application(fun: RcSyntax, arg: RcSyntax) -> Syntax {
        Syntax::Application(Application::new(fun, arg))
    }

    pub fn application_rc(fun: RcSyntax, arg: RcSyntax) -> RcSyntax {
        Rc::new(Syntax::application(fun, arg))
    }

    pub fn universe(level: UniverseLevel) -> Syntax {
        Syntax::Universe(Universe::new(level))
    }

    pub fn universe_rc(level: UniverseLevel) -> RcSyntax {
        Rc::new(Syntax::universe(level))
    }

    pub fn meta_variable(id: MetaVariableId, closure: Closure) -> Syntax {
        Syntax::MetaVariable(MetaVariable::new(id, closure))
    }

    pub fn meta_variable_rc(id: MetaVariableId, closure: Closure) -> RcSyntax {
        Rc::new(Syntax::meta_variable(id, closure))
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Constant {
    pub name: NameId,
}

impl Constant {
    pub fn new(name: NameId) -> Constant {
        Constant { name }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Variable {
    pub index: Index,
}

impl Variable {
    pub fn new(index: Index) -> Variable {
        Variable { index }
    }
}

#[derive(Clone, Debug)]
pub struct Check {
    pub ty: RcSyntax,
    pub term: RcSyntax,
}

impl Check {
    pub fn new(ty: RcSyntax, term: RcSyntax) -> Check {
        Check { ty, term }
    }
}

#[derive(Clone, Debug)]
pub struct Pi {
    pub source: RcSyntax,
    pub target: RcSyntax,
}

impl Pi {
    pub fn new(source: RcSyntax, target: RcSyntax) -> Pi {
        Pi { source, target }
    }
}

#[derive(Clone, Debug)]
pub struct Lambda {
    pub body: RcSyntax,
}

impl Lambda {
    pub fn new(body: RcSyntax) -> Lambda {
        Lambda { body }
    }
}

#[derive(Clone, Debug)]
pub struct Application {
    pub function: RcSyntax,
    pub argument: RcSyntax,
}

impl Application {
    pub fn new(function: RcSyntax, argument: RcSyntax) -> Application {
        Application { function, argument }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct UniverseLevel(pub u32);

#[derive(Clone, Copy, Debug)]
pub struct Universe {
    pub level: UniverseLevel,
}

impl Universe {
    pub fn new(level: UniverseLevel) -> Universe {
        Universe { level }
    }
}

/// The identifier of a meta variable.
#[derive(Copy, Clone, Debug)]
pub struct MetaVariableId(pub u32);

/// A hole in the syntax.
#[derive(Clone, Debug)]
pub struct MetaVariable {
    pub id: MetaVariableId,
    pub closure: Closure,
}

impl MetaVariable {
    pub fn new(id: MetaVariableId, closure: Closure) -> MetaVariable {
        MetaVariable { id, closure }
    }
}
