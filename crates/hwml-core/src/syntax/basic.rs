use crate::db::Index;
use serde::{Deserialize, Serialize};
use std::rc::Rc;

pub type RcSyntax = Rc<Syntax>;

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum Syntax {
    Variable(Variable),
    Check(Check),
    Pi(Pi),
    Lambda(Lambda),
    Application(Application),
    Universe(Universe),
}

impl Syntax {
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
}

#[derive(Clone, Copy, Debug, Deserialize, Serialize)]
pub struct Variable {
    pub index: Index,
}

impl Variable {
    pub fn new(index: Index) -> Variable {
        Variable { index }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Check {
    pub ty: RcSyntax,
    pub term: RcSyntax,
}

impl Check {
    pub fn new(ty: RcSyntax, term: RcSyntax) -> Check {
        Check { ty, term }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Pi {
    pub source: RcSyntax,
    pub target: RcSyntax,
}

impl Pi {
    pub fn new(source: RcSyntax, target: RcSyntax) -> Pi {
        Pi { source, target }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Lambda {
    pub body: RcSyntax,
}

impl Lambda {
    pub fn new(body: RcSyntax) -> Lambda {
        Lambda { body }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Application {
    pub function: RcSyntax,
    pub argument: RcSyntax,
}

impl Application {
    pub fn new(function: RcSyntax, argument: RcSyntax) -> Application {
        Application { function, argument }
    }
}

type UniverseLevel = u32;

#[derive(Clone, Copy, Debug, Deserialize, Serialize)]
pub struct Universe {
    pub level: UniverseLevel,
}

impl Universe {
    pub fn new(level: UniverseLevel) -> Universe {
        Universe { level }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Environment {
    pub variable_types: Vec<RcSyntax>,
}
