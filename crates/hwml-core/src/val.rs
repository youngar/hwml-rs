use crate::common::{Level, UniverseLevel};
use crate::syn::{ConstantId, RcSyntax};
use std::collections::HashMap;
use std::rc::Rc;

/// A closure represents a pending evaluation. A closure records the term to be
/// reduced by evaluation, as well as the environment it is to be evaluated under.
///
/// The closure is typically used when a substitution is pending. The substitution
/// can be performed simultaneously with reduction of the term by extending the
/// environment.
#[derive(Clone, Debug)]
pub struct Closure<'db> {
    pub environment: Environment<'db>,
    pub term: RcSyntax<'db>,
}

impl<'db> Closure<'db> {
    pub fn new(environment: Environment<'db>, term: RcSyntax<'db>) -> Closure<'db> {
        Closure { environment, term }
    }
}

/// A value in normal form.
#[derive(Clone, Debug)]
pub struct Normal<'db> {
    pub ty: Rc<Value<'db>>,
    pub value: Rc<Value<'db>>,
}

impl<'db> Normal<'db> {
    pub fn new(ty: Rc<Value<'db>>, value: Rc<Value<'db>>) -> Normal<'db> {
        Normal { ty, value }
    }
}

/// Fully normalized values in the semantic domain.
#[derive(Clone, Debug)]
pub enum Value<'db> {
    Pi(Pi<'db>),
    Lambda(Lambda<'db>),
    Universe(Universe),
    Neutral(Rc<Value<'db>>, Rc<Neutral<'db>>),
}

impl<'db> Value<'db> {
    pub fn pi(source: Rc<Value<'db>>, target: Closure<'db>) -> Value<'db> {
        Value::Pi(Pi::new(source, target))
    }

    pub fn lambda(body: Closure<'db>) -> Value<'db> {
        Value::Lambda(Lambda::new(body))
    }

    pub fn universe(level: UniverseLevel) -> Value<'db> {
        Value::Universe(Universe::new(level))
    }

    pub fn neutral(ty: Rc<Value<'db>>, neutral: Rc<Neutral<'db>>) -> Value<'db> {
        Value::Neutral(ty, neutral)
    }

    pub fn variable(ty: Rc<Value<'db>>, level: Level) -> Value<'db> {
        Value::neutral(ty, Rc::new(Neutral::variable(level)))
    }

    pub fn application(
        ty: Rc<Value<'db>>,
        function: Rc<Neutral<'db>>,
        argument_ty: Rc<Value<'db>>,
        argument: Rc<Value<'db>>,
    ) -> Value<'db> {
        let app = Neutral::application(function, argument_ty, argument);
        Value::neutral(ty, Rc::new(app))
    }
}

/// A dependent function type. Written `(x : source) -> target(x)`.
#[derive(Clone, Debug)]
pub struct Pi<'db> {
    /// The domain or source-type of this function type.
    pub source: Rc<Value<'db>>,

    /// The codomain or target-type of this function type.
    pub target: Closure<'db>,
}

impl<'db> Pi<'db> {
    pub fn new(source: Rc<Value<'db>>, target: Closure<'db>) -> Pi<'db> {
        Pi { source, target }
    }
}

/// A function. Written `\x => body`.
#[derive(Clone, Debug)]
pub struct Lambda<'db> {
    pub body: Closure<'db>,
}

impl<'db> Lambda<'db> {
    pub fn new(body: Closure<'db>) -> Lambda<'db> {
        Lambda { body }
    }
}

/// A universe, the "type of a type".
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
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
pub enum Neutral<'db> {
    Variable(Variable),
    Application(Application<'db>),
}

impl<'db> Neutral<'db> {
    pub fn variable(level: Level) -> Neutral<'db> {
        let var: Variable = Variable::new(level);
        Neutral::Variable(var)
    }

    pub fn application(
        function: Rc<Neutral<'db>>,
        argument_ty: Rc<Value<'db>>,
        argument: Rc<Value<'db>>,
    ) -> Neutral<'db> {
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
pub struct Application<'db> {
    pub function: Rc<Neutral<'db>>,
    pub argument: Normal<'db>,
}

impl<'db> Application<'db> {
    pub fn new(
        function: Rc<Neutral<'db>>,
        argument_ty: Rc<Value<'db>>,
        argument: Rc<Value<'db>>,
    ) -> Application<'db> {
        Application {
            function,
            argument: Normal::new(argument_ty, argument),
        }
    }
}

/// A mapping from bound variables to associated values.
#[derive(Clone, Debug)]
pub struct Environment<'db> {
    /// Constant environment mapping ConstantId to values.
    const_env: HashMap<ConstantId<'db>, Rc<Value<'db>>>,

    /// The typing environment.
    map: Vec<Rc<Value<'db>>>,
}

impl<'db> Environment<'db> {
    pub fn new() -> Environment<'db> {
        Environment {
            const_env: HashMap::new(),
            map: Vec::new(),
        }
    }

    pub fn get(&self, level: Level) -> &Rc<Value<'db>> {
        let index: usize = level.into();
        &self.map[index]
    }

    pub fn variable_type(&self, variable: Variable) -> &Rc<Value<'db>> {
        self.get(variable.level)
    }

    pub fn constant(&self, name: ConstantId<'db>) -> Option<&Rc<Value<'db>>> {
        self.const_env.get(&name)
    }

    /// Add a constant to the environment.
    pub fn add_constant(&mut self, name: ConstantId<'db>, value: Rc<Value<'db>>) {
        self.const_env.insert(name, value);
    }

    /// The number of bound variables in scope.
    pub fn depth(&self) -> usize {
        self.map.len() as usize
    }

    /// Extend the environment by pushing a definition onto the end.
    pub fn push(&mut self, value: Rc<Value<'db>>) {
        self.map.push(value);
    }

    /// Extend the environment by pushing a variable onto the end.
    pub fn push_var(&mut self, ty: Rc<Value<'db>>) -> Rc<Value<'db>> {
        let depth = self.depth();
        let value = Rc::new(Value::variable(ty, Level::new(depth)));
        self.push(value.clone());
        value
    }

    pub fn pop(&mut self) {
        self.map.pop();
    }
}

impl<'db> Extend<Rc<Value<'db>>> for Environment<'db> {
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = Rc<Value<'db>>>,
    {
        self.map.extend(iter);
    }
}
