use crate::common::{Level, UniverseLevel};
use crate::syn::{ConstantId, RcSyntax};
use std::collections::HashMap;
use std::rc::Rc;

/// A closure represents a pending evaluation. A closure records the term to be
/// reduced by evaluation, as well as the local environment it is to be evaluated under.
///
/// The closure is typically used when a substitution is pending. The substitution
/// can be performed simultaneously with reduction of the term by extending the
/// local environment.
#[derive(Clone, Debug)]
pub struct Closure<'db> {
    pub local: LocalEnv<'db>,
    pub term: RcSyntax<'db>,
}

impl<'db> Closure<'db> {
    pub fn new(local: LocalEnv<'db>, term: RcSyntax<'db>) -> Closure<'db> {
        Closure { local, term }
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
    Constant(ConstantId<'db>),
    Pi(Pi<'db>),
    Lambda(Lambda<'db>),
    Universe(Universe),
    TypeConstructor(TypeConstructor<'db>),
    DataConstructor(DataConstructor<'db>),
    Neutral(Rc<Value<'db>>, Rc<Neutral<'db>>),
}

impl<'db> Value<'db> {
    pub fn constant(name: ConstantId<'db>) -> Value<'db> {
        Value::Constant(name)
    }

    pub fn pi(source: Rc<Value<'db>>, target: Closure<'db>) -> Value<'db> {
        Value::Pi(Pi::new(source, target))
    }

    pub fn lambda(body: Closure<'db>) -> Value<'db> {
        Value::Lambda(Lambda::new(body))
    }

    pub fn universe(level: UniverseLevel) -> Value<'db> {
        Value::Universe(Universe::new(level))
    }

    pub fn type_constructor(
        constructor: ConstantId<'db>,
        arguments: Vec<Rc<Value<'db>>>,
    ) -> Value<'db> {
        Value::TypeConstructor(TypeConstructor::new(constructor, arguments))
    }

    pub fn data_constructor(
        constructor: ConstantId<'db>,
        arguments: Vec<Rc<Value<'db>>>,
    ) -> Value<'db> {
        Value::DataConstructor(DataConstructor::new(constructor, arguments))
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

    pub fn case(
        ty: Rc<Value<'db>>,
        scrutinee: Rc<Neutral<'db>>,
        motive: Rc<Value<'db>>,
        branches: Vec<CaseBranch<'db>>,
    ) -> Value<'db> {
        let case = Neutral::case(scrutinee, motive, branches);
        Value::neutral(ty, Rc::new(case))
    }
}

#[derive(Clone, Debug)]
pub struct Constant<'db> {
    pub name: ConstantId<'db>,
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

#[derive(Clone, Debug)]
pub struct TypeConstructor<'db> {
    /// The constructor constant id.
    pub constructor: ConstantId<'db>,
    /// The argument values for this constructor instance
    pub arguments: Vec<Rc<Value<'db>>>,
}

impl<'db> TypeConstructor<'db> {
    pub fn new(
        constructor: ConstantId<'db>,
        arguments: Vec<Rc<Value<'db>>>,
    ) -> TypeConstructor<'db> {
        TypeConstructor {
            constructor,
            arguments,
        }
    }
}

/// A data constructor instance with its arguments.
#[derive(Clone, Debug)]
pub struct DataConstructor<'db> {
    /// The constructor constant id
    pub constructor: ConstantId<'db>,
    /// The argument values for this constructor instance
    pub arguments: Vec<Rc<Value<'db>>>,
}

impl<'db> DataConstructor<'db> {
    pub fn new(
        constructor: ConstantId<'db>,
        arguments: Vec<Rc<Value<'db>>>,
    ) -> DataConstructor<'db> {
        DataConstructor {
            constructor,
            arguments,
        }
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
    Case(Case<'db>),
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
        Neutral::Application(Application::new(
            function,
            Normal::new(argument_ty, argument),
        ))
    }

    pub fn case(
        scrutinee: Rc<Neutral<'db>>,
        motive: Rc<Value<'db>>,
        branches: Vec<CaseBranch<'db>>,
    ) -> Neutral<'db> {
        Neutral::Case(Case::new(scrutinee, motive, branches))
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
    pub fn new(function: Rc<Neutral<'db>>, argument: Normal<'db>) -> Application<'db> {
        Application { function, argument }
    }
}

#[derive(Clone, Debug)]
pub struct Case<'db> {
    pub scrutinee: Rc<Neutral<'db>>,
    pub motive: Rc<Value<'db>>,
    pub branches: Vec<CaseBranch<'db>>,
}

impl<'db> Case<'db> {
    pub fn new(
        scrutinee: Rc<Neutral<'db>>,
        motive: Rc<Value<'db>>,
        branches: Vec<CaseBranch<'db>>,
    ) -> Case<'db> {
        Case {
            scrutinee,
            motive,
            branches,
        }
    }
}

#[derive(Clone, Debug)]
pub struct CaseBranch<'db> {
    pub constructor: ConstantId<'db>,
    pub arity: usize,
    pub body: Normal<'db>,
}

impl<'db> CaseBranch<'db> {
    pub fn new(constructor: ConstantId<'db>, arity: usize, body: Normal<'db>) -> CaseBranch<'db> {
        CaseBranch {
            constructor,
            arity,
            body,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Environment<'db> {
    pub global: GlobalEnv<'db>,
    pub local: LocalEnv<'db>,
}

impl<'db> Environment<'db> {
    pub fn new() -> Self {
        Self {
            global: GlobalEnv::new(),
            local: LocalEnv::new(),
        }
    }

    // Forwarding methods to GlobalEnv

    /// Lookup a global constant by name.
    pub fn lookup(&self, name: ConstantId<'db>) -> Result<&Global<'db>, LookupError> {
        self.global.lookup(name)
    }

    /// Lookup a global definition by name.
    pub fn definition(&self, name: ConstantId<'db>) -> Result<&Rc<Value<'db>>, LookupError> {
        self.global.definition(name)
    }

    /// Add a definition to the global environment.
    pub fn add_definition(&mut self, name: ConstantId<'db>, value: Rc<Value<'db>>) {
        self.global.add_definition(name, value)
    }

    /// Lookup a type constructor by name.
    pub fn type_constructor(
        &self,
        name: ConstantId<'db>,
    ) -> Result<&TypeConstructorInfo<'db>, LookupError> {
        self.global.type_constructor(name)
    }

    /// Add a type constructor to the global environment.
    pub fn add_type_constructor(&mut self, name: ConstantId<'db>, info: TypeConstructorInfo<'db>) {
        self.global.add_type_constructor(name, info)
    }

    /// Lookup a data constructor by name.
    pub fn data_constructor(
        &self,
        name: ConstantId<'db>,
    ) -> Result<&DataConstructorInfo<'db>, LookupError> {
        self.global.data_constructor(name)
    }

    /// Add a data constructor to the global environment.
    pub fn add_data_constructor(&mut self, name: ConstantId<'db>, info: DataConstructorInfo<'db>) {
        self.global.add_data_constructor(name, info)
    }

    // Forwarding methods to LocalEnv

    /// Get a local variable by level.
    pub fn get(&self, level: Level) -> &Rc<Value<'db>> {
        self.local.get(level)
    }

    /// The number of bound variables in scope.
    pub fn depth(&self) -> usize {
        self.local.depth()
    }

    /// Extend the environment by pushing a definition onto the end.
    pub fn push(&mut self, value: Rc<Value<'db>>) {
        self.local.push(value)
    }

    /// Extend the environment by pushing a variable onto the end.
    pub fn push_var(&mut self, ty: Rc<Value<'db>>) -> Rc<Value<'db>> {
        self.local.push_var(ty)
    }
}

#[derive(Debug, Clone)]
pub enum LookupError {
    UnknownConstant,
    NotDefinition,
    NotTypeConstructor,
    NotDataConstructor,
}

#[derive(Clone, Debug)]
pub enum Global<'db> {
    Definition(Rc<Value<'db>>),
    TypeConstructor(TypeConstructorInfo<'db>),
    DataConstructor(DataConstructorInfo<'db>),
}

#[derive(Clone, Debug)]
pub struct GlobalEnv<'db> {
    /// Constant environment mapping ConstantId to values.
    constants: HashMap<ConstantId<'db>, Global<'db>>,
}

impl<'db> GlobalEnv<'db> {
    pub fn new() -> Self {
        Self {
            constants: HashMap::new(),
        }
    }

    /// Lookup a global constant by name.
    pub fn lookup(&self, name: ConstantId<'db>) -> Result<&Global<'db>, LookupError> {
        self.constants
            .get(&name)
            .ok_or(LookupError::UnknownConstant)
    }

    /// Lookup a global definition by name.
    pub fn definition(&self, name: ConstantId<'db>) -> Result<&Rc<Value<'db>>, LookupError> {
        match self.constants.get(&name) {
            Some(Global::Definition(value)) => Ok(value),
            Some(_) => Err(LookupError::NotDefinition),
            None => Err(LookupError::UnknownConstant),
        }
    }

    /// Add a definition to the global environment.
    pub fn add_definition(&mut self, name: ConstantId<'db>, value: Rc<Value<'db>>) {
        self.constants.insert(name, Global::Definition(value));
    }

    /// Lookup a type constructor by name.
    pub fn type_constructor(
        &self,
        name: ConstantId<'db>,
    ) -> Result<&TypeConstructorInfo<'db>, LookupError> {
        match self.constants.get(&name) {
            Some(Global::TypeConstructor(info)) => Ok(info),
            Some(_) => Err(LookupError::NotTypeConstructor),
            None => Err(LookupError::UnknownConstant),
        }
    }

    /// Add a type constructor to the global environment.
    pub fn add_type_constructor(&mut self, name: ConstantId<'db>, info: TypeConstructorInfo<'db>) {
        self.constants.insert(name, Global::TypeConstructor(info));
    }

    /// Lookup a data constructor by name.
    pub fn data_constructor(
        &self,
        name: ConstantId<'db>,
    ) -> Result<&DataConstructorInfo<'db>, LookupError> {
        match self.constants.get(&name) {
            Some(Global::DataConstructor(info)) => Ok(info),
            Some(_) => Err(LookupError::NotDataConstructor),
            None => Err(LookupError::UnknownConstant),
        }
    }

    /// Add a data constructor to the global environment.
    pub fn add_data_constructor(&mut self, name: ConstantId<'db>, info: DataConstructorInfo<'db>) {
        self.constants.insert(name, Global::DataConstructor(info));
    }
}

/// A mapping from bound variables to associated values.
#[derive(Clone, Debug)]
pub struct LocalEnv<'db> {
    /// The typing environment.
    locals: Vec<Rc<Value<'db>>>,
}

impl<'db> LocalEnv<'db> {
    pub fn new() -> LocalEnv<'db> {
        Self { locals: Vec::new() }
    }

    pub fn get(&self, level: Level) -> &Rc<Value<'db>> {
        let index: usize = level.into();
        &self.locals[index]
    }

    /// The number of bound variables in scope.
    pub fn depth(&self) -> usize {
        self.locals.len() as usize
    }

    /// Extend the environment by pushing a definition onto the end.
    pub fn push(&mut self, value: Rc<Value<'db>>) {
        self.locals.push(value);
    }

    /// Extend the environment by pushing a variable onto the end.
    pub fn push_var(&mut self, ty: Rc<Value<'db>>) -> Rc<Value<'db>> {
        let depth = self.depth();
        let value = Rc::new(Value::variable(ty, Level::new(depth)));
        self.push(value.clone());
        value
    }

    pub fn pop(&mut self) {
        self.locals.pop();
    }

    /// Extend the environment with multiple values.
    pub fn extend<T>(&mut self, values: T)
    where
        T: IntoIterator<Item = Rc<Value<'db>>>,
    {
        self.locals.extend(values);
    }
}

impl<'db> Extend<Rc<Value<'db>>> for Environment<'db> {
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = Rc<Value<'db>>>,
    {
        self.local.locals.extend(iter);
    }
}

#[derive(Clone, Debug)]
pub struct TypeConstructorInfo<'db> {
    pub ty: Rc<Value<'db>>,
}

impl<'db> TypeConstructorInfo<'db> {
    pub fn new(ty: Rc<Value<'db>>) -> Self {
        TypeConstructorInfo { ty }
    }
}

#[derive(Clone, Debug)]
pub struct DataConstructorInfo<'db> {
    pub ty: Rc<Value<'db>>,
}

impl<'db> DataConstructorInfo<'db> {
    pub fn new(ty: Rc<Value<'db>>) -> Self {
        DataConstructorInfo { ty }
    }
}
