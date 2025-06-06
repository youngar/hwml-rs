use crate::common::{Level, UniverseLevel};
use crate::syntax::{NameId, RcSyntax};
use std::rc::Rc;

/// A closure represents a pending evaluation. A closure records the term to be
/// reduced by evaluation, as well as the environment it is to be evaluated under.
///
/// The closure is typically used when a substitution is pending. The substitution
/// can be performed simultaneously with reduction of the term by extending the
/// environment.
#[derive(Clone, Debug)]
pub struct Closure {
    pub environment: Environment,
    pub term: RcSyntax,
}

impl Closure {
    pub fn new(environment: Environment, term: RcSyntax) -> Closure {
        Closure { environment, term }
    }
}

/// A value in normal form.
#[derive(Clone, Debug)]
pub struct Normal {
    pub ty: Rc<Value>,
    pub value: Rc<Value>,
}

impl Normal {
    pub fn new(ty: Rc<Value>, value: Rc<Value>) -> Normal {
        Normal { ty, value }
    }
}

/// Fully normalized values in the semantic domain.
#[derive(Clone, Debug)]
pub enum Value {
    Pi(Pi),
    Lambda(Lambda),
    Universe(Universe),
    Neutral(Rc<Value>, Rc<Neutral>),
}

impl Value {
    pub fn pi(source: Rc<Value>, target: Closure) -> Value {
        Value::Pi(Pi::new(source, target))
    }

    pub fn lambda(body: Closure) -> Value {
        Value::Lambda(Lambda::new(body))
    }

    pub fn universe(level: UniverseLevel) -> Value {
        Value::Universe(Universe::new(level))
    }

    pub fn neutral(ty: Rc<Value>, neutral: Rc<Neutral>) -> Value {
        Value::Neutral(ty, neutral)
    }

    pub fn variable(ty: Rc<Value>, level: Level) -> Value {
        Value::neutral(ty, Rc::new(Neutral::variable(level)))
    }

    pub fn application(
        ty: Rc<Value>,
        function: Rc<Neutral>,
        argument_ty: Rc<Value>,
        argument: Rc<Value>,
    ) -> Value {
        let app = Neutral::application(function, argument_ty, argument);
        Value::neutral(ty, Rc::new(app))
    }
}

/// A dependent function type. Written `(x : source) -> target(x)`.
#[derive(Clone, Debug)]
pub struct Pi {
    /// The domain or source-type of this function type.
    pub source: Rc<Value>,

    /// The codomain or target-type of this function type.
    pub target: Closure,
}

impl Pi {
    pub fn new(source: Rc<Value>, target: Closure) -> Pi {
        Pi { source, target }
    }
}

/// A function. Written `\x => body`.
#[derive(Clone, Debug)]
pub struct Lambda {
    pub body: Closure,
}

impl Lambda {
    pub fn new(body: Closure) -> Lambda {
        Lambda { body }
    }
}

/// A universe, the "type of a type".
#[derive(Clone, Copy, Debug)]
pub struct Universe {
    pub level: UniverseLevel,
}

impl Universe {
    pub fn new(level: UniverseLevel) -> Universe {
        Universe { level }
    }
}

/// The neutrals represent stuck computations. They ARE in normal form, but are
/// not, per se, values in the sense that they are not composed of constructors.
///
/// Neutrals arise when an elimination form is applied to a variable. That
/// elimination form is "stuck", we cannot reduce it becaus
///
/// The structure of the neutral ensures that the prima.
#[derive(Clone, Debug)]
pub enum Neutral {
    Variable(Variable),
    Application(Application),
}

impl Neutral {
    pub fn variable(level: Level) -> Neutral {
        let var: Variable = Variable::new(level);
        Neutral::Variable(var)
    }

    pub fn application(
        function: Rc<Neutral>,
        argument_ty: Rc<Value>,
        argument: Rc<Value>,
    ) -> Neutral {
        Neutral::Application(Application::new(function, argument_ty, argument))
    }
}

/// A free variable.
#[derive(Clone, Copy, Debug)]
pub struct Variable {
    pub level: Level,
}

impl Variable {
    pub fn new(level: Level) -> Variable {
        Variable { level }
    }
}

/// Function application.
#[derive(Clone, Debug)]
pub struct Application {
    pub function: Rc<Neutral>,
    pub argument: Normal,
}

impl Application {
    pub fn new(function: Rc<Neutral>, argument_ty: Rc<Value>, argument: Rc<Value>) -> Application {
        Application {
            function,
            argument: Normal::new(argument_ty, argument),
        }
    }
}

/// A mapping from bound variables to associated values.
#[derive(Clone, Debug)]
pub struct Environment {
    /// Constant environment.
    const_env: Vec<Rc<Value>>,

    /// The typing environment.
    map: Vec<Rc<Value>>,
}

impl Environment {
    pub fn new() -> Environment {
        Environment {
            const_env: Vec::new(),
            map: Vec::new(),
        }
    }

    pub fn get(&self, level: Level) -> &Rc<Value> {
        &self.map[level.to_usize()]
    }

    pub fn variable_type(&self, variable: Variable) -> &Rc<Value> {
        self.get(variable.level)
    }

    pub fn constant(&self, name: NameId) -> &Rc<Value> {
        &self.const_env[name.0 as usize]
    }

    /// The number of bound variables in scope.
    pub fn depth(&self) -> usize {
        self.map.len() as usize
    }

    /// Extend the environment by pushing a definition onto the end.
    pub fn push(&mut self, value: Rc<Value>) {
        self.map.push(value);
    }

    /// Extend the environment by pushing a variable onto the end.
    pub fn push_var(&mut self, ty: Rc<Value>) -> Rc<Value> {
        let depth = self.depth();
        let value = Rc::new(Value::variable(ty, Level::new(depth)));
        self.push(value.clone());
        value
    }

    pub fn pop(&mut self) {
        self.map.pop();
    }
}

impl Extend<Rc<Value>> for Environment {
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = Rc<Value>>,
    {
        self.map.extend(iter);
    }
}
