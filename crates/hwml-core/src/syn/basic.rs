use crate::common::{Index, Level, UniverseLevel};
use std::rc::Rc;

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone, Copy)]
pub struct NameId(pub u32);

pub type RcSyntax = Rc<Syntax>;

pub type Tm = Syntax;
pub type Ty = Syntax;

/// A captured environment.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Closure {
    /// The environment contains a vector of definitions.
    pub values: Vec<RcSyntax>,
}

impl Closure {
    pub fn new() -> Closure {
        Closure { values: Vec::new() }
    }
    pub fn with_values(values: Vec<RcSyntax>) -> Closure {
        Closure { values }
    }
    pub fn pop(&mut self) {
        self.values.pop();
    }
    pub fn truncate(&mut self, depth: usize) {
        self.values.truncate(depth);
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Environment {
    types: Vec<RcSyntax>,
}

impl Environment {
    pub fn new() -> Environment {
        Environment { types: Vec::new() }
    }
    pub fn depth(&self) -> usize {
        self.types.len()
    }
    pub fn to_index(&self, level: Level) -> Index {
        level.to_index(self.depth())
    }
    pub fn to_level(&self, index: Index) -> Level {
        index.to_level(self.depth())
    }
    pub fn extend(&mut self, ty: RcSyntax) -> Level {
        self.types.push(ty);
        Level::new(self.depth() - 1)
    }
    pub fn pop(&mut self) {
        self.types.pop();
    }
    pub fn truncate(&mut self, depth: usize) {
        self.types.truncate(depth);
    }
    pub fn lookup(&self, level: Level) -> RcSyntax {
        self.types.get(level.to_usize()).unwrap().clone()
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub enum Syntax {
    Constant(Constant),
    Variable(Variable),
    Check(Check),
    Pi(Pi),
    Lambda(Lambda),
    Application(Application),
    Universe(Universe),
    Metavariable(Metavariable),
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

    // Create a metavariable syntax node with a reference to an existing metavariable.
    pub fn metavariable(metavariable: MetavariableId, closure: Closure) -> Syntax {
        Syntax::Metavariable(Metavariable::new(metavariable, closure))
    }

    pub fn metavariable_rc(metavariable: MetavariableId, closure: Closure) -> RcSyntax {
        Rc::new(Syntax::metavariable(metavariable, closure))
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Constant {
    pub name: NameId,
}

impl Constant {
    pub fn new(name: NameId) -> Constant {
        Constant { name }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Variable {
    pub index: Index,
}

impl Variable {
    pub fn new(index: Index) -> Variable {
        Variable { index }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Check {
    pub ty: RcSyntax,
    pub term: RcSyntax,
}

impl Check {
    pub fn new(ty: RcSyntax, term: RcSyntax) -> Check {
        Check { ty, term }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Pi {
    pub source: RcSyntax,
    pub target: RcSyntax,
}

impl Pi {
    pub fn new(source: RcSyntax, target: RcSyntax) -> Pi {
        Pi { source, target }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Lambda {
    pub body: RcSyntax,
}

impl Lambda {
    pub fn new(body: RcSyntax) -> Lambda {
        Lambda { body }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Application {
    pub function: RcSyntax,
    pub argument: RcSyntax,
}

impl Application {
    pub fn new(function: RcSyntax, argument: RcSyntax) -> Application {
        Application { function, argument }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone, Copy)]
pub struct Universe {
    pub level: UniverseLevel,
}

impl Universe {
    pub fn new(level: UniverseLevel) -> Universe {
        Universe { level }
    }
}

// A reference to a metavariable. All metavariables have identity equality.
pub struct Metavariable {
    pub id: MetavariableId,
    pub closure: Closure,
}

impl Metavariable {
    pub fn new(id: MetavariableId, closure: Closure) -> Metavariable {
        Metavariable { id, closure }
    }
}

impl PartialEq for Metavariable {
    // Metavariables are identity equal.
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.id, &other.id)
    }
}

impl Eq for Metavariable {}

impl std::hash::Hash for Metavariable {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Hash based on the pointer address for identity equality
        (self.id.as_ref() as *const MetavariableData).hash(state);
    }
}

impl PartialOrd for Metavariable {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Metavariable {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Compare based on pointer addresses for consistent ordering
        let self_ptr = self.id.as_ref() as *const MetavariableData;
        let other_ptr = other.id.as_ref() as *const MetavariableData;
        self_ptr.cmp(&other_ptr)
    }
}

impl std::fmt::Debug for Metavariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let data_ptr = self.id.as_ref() as *const MetavariableData;
        f.debug_struct("Metavariable")
            .field("id", &format!("{:p}", data_ptr))
            .field("data", &self.id)
            .finish()
    }
}

impl Clone for Metavariable {
    fn clone(&self) -> Self {
        Metavariable {
            id: Rc::clone(&self.id),
            closure: self.closure.clone(),
        }
    }
}

/// This is the unique identifier for a metavariable, and its associated data.
pub type MetavariableId = Rc<MetavariableData>;

/// This represents the associated data for a metavariable.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct MetavariableData {}

impl MetavariableData {
    pub fn new() -> MetavariableData {
        MetavariableData {}
    }
}
