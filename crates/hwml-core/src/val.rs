use crate::common::{Level, MetaVariableId, UniverseLevel};
use crate::syn::{ConstantId, RcSyntax, Telescope};
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
    /// Neutral headed by a metavariable.
    Flex(Flex<'db>),
    /// Neutral headed by a variable.
    Rigid(Rigid<'db>),
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

    pub fn rigid(head: Variable, spine: Spine<'db>, ty: Rc<Value<'db>>) -> Value<'db> {
        Value::Rigid(Rigid { head, spine, ty })
    }

    pub fn flex(head: MetaVariable<'db>, spine: Spine<'db>, ty: Rc<Value<'db>>) -> Value<'db> {
        Value::Flex(Flex { head, spine, ty })
    }

    pub fn variable(ty: Rc<Value<'db>>, level: Level) -> Value<'db> {
        Value::rigid(Variable::new(level), Spine::empty(), ty)
    }

    pub fn metavariable(id: MetaVariableId, local: LocalEnv<'db>) -> Value<'db> {
        Value::flex(
            MetaVariable::new(id, local),
            Spine::empty(),
            Rc::new(Value::universe(UniverseLevel::new(0))),
        )
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

    pub fn iter(&self) -> std::slice::Iter<'_, Rc<Value<'db>>> {
        self.arguments.iter()
    }
}

// Implement IntoIterator for &TypeConstructor to allow iteration by reference
impl<'a, 'db> IntoIterator for &'a TypeConstructor<'db> {
    type Item = &'a Rc<Value<'db>>;
    type IntoIter = std::slice::Iter<'a, Rc<Value<'db>>>;

    fn into_iter(self) -> Self::IntoIter {
        self.arguments.iter()
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

    pub fn iter(&self) -> std::slice::Iter<'_, Rc<Value<'db>>> {
        self.arguments.iter()
    }
}

// Implement IntoIterator for &DataConstructor to allow iteration by reference
impl<'a, 'db> IntoIterator for &'a DataConstructor<'db> {
    type Item = &'a Rc<Value<'db>>;
    type IntoIter = std::slice::Iter<'a, Rc<Value<'db>>>;

    fn into_iter(self) -> Self::IntoIter {
        self.arguments.iter()
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
pub struct Flex<'db> {
    pub head: MetaVariable<'db>,
    pub spine: Spine<'db>,
    pub ty: Rc<Value<'db>>,
}

impl<'db> Flex<'db> {
    pub fn new(head: MetaVariable<'db>, spine: Spine<'db>, ty: Rc<Value<'db>>) -> Flex<'db> {
        Flex { head, spine, ty }
    }

    /// Apply an eliminator to this flexible neutral, extending the spine.
    pub fn apply_eliminator(
        mut self,
        eliminator: Eliminator<'db>,
        ty: Rc<Value<'db>>,
    ) -> Flex<'db> {
        self.spine.push(eliminator);
        self.ty = ty;
        self
    }
}

#[derive(Clone, Debug)]
pub struct Rigid<'db> {
    pub head: Variable,
    pub spine: Spine<'db>,
    pub ty: Rc<Value<'db>>,
}

impl<'db> Rigid<'db> {
    pub fn new(head: Variable, spine: Spine<'db>, ty: Rc<Value<'db>>) -> Rigid<'db> {
        Rigid { head, spine, ty }
    }

    /// Apply an eliminator to this rigid neutral, extending the spine.
    pub fn apply_eliminator(
        mut self,
        eliminator: Eliminator<'db>,
        ty: Rc<Value<'db>>,
    ) -> Rigid<'db> {
        self.spine.push(eliminator);
        self.ty = ty;
        self
    }
}

#[derive(Debug, Clone)]
pub struct Spine<'db>(pub Vec<Eliminator<'db>>);

impl<'db> Spine<'db> {
    pub fn empty() -> Spine<'db> {
        Spine(Vec::new())
    }

    pub fn new(eliminators: Vec<Eliminator<'db>>) -> Spine<'db> {
        Spine(eliminators)
    }

    pub fn push(&mut self, eliminator: Eliminator<'db>) {
        self.0.push(eliminator);
    }

    pub fn iter(&self) -> std::slice::Iter<'_, Eliminator<'db>> {
        self.0.iter()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

#[derive(Debug, Clone)]
pub enum Eliminator<'db> {
    Application(Application<'db>),
    Case(Case<'db>),
}

impl<'db> Eliminator<'db> {
    pub fn application(argument: Normal<'db>) -> Eliminator<'db> {
        Eliminator::Application(Application::new(argument))
    }

    pub fn case(
        type_constructor: ConstantId<'db>,
        parameters: Vec<Rc<Value<'db>>>,
        motive: Closure<'db>,
        branches: Vec<CaseBranch<'db>>,
    ) -> Eliminator<'db> {
        Eliminator::Case(Case::new(type_constructor, parameters, motive, branches))
    }
}

/// A free variable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Variable {
    pub level: Level,
}

impl Variable {
    pub fn new(level: Level) -> Variable {
        Variable { level }
    }
}

#[derive(Clone, Debug)]
pub struct MetaVariable<'db> {
    pub id: MetaVariableId,
    pub local: LocalEnv<'db>,
}

impl<'db> PartialEq for MetaVariable<'db> {
    fn eq(&self, other: &Self) -> bool {
        // Two metavariables are equal if they have the same ID.
        // We ignore the local environment for equality comparison.
        self.id == other.id
    }
}

impl<'db> MetaVariable<'db> {
    pub fn new(id: MetaVariableId, local: LocalEnv<'db>) -> MetaVariable {
        MetaVariable { id, local }
    }
}

/// Function application.
#[derive(Clone, Debug)]
pub struct Application<'db> {
    pub argument: Normal<'db>,
}

impl<'db> Application<'db> {
    pub fn new(argument: Normal<'db>) -> Application<'db> {
        Application { argument }
    }
}

#[derive(Clone, Debug)]
pub struct Case<'db> {
    pub type_constructor: ConstantId<'db>,
    pub parameters: Vec<Rc<Value<'db>>>,
    pub motive: Closure<'db>,
    pub branches: Vec<CaseBranch<'db>>,
}

impl<'db> Case<'db> {
    pub fn new(
        type_constructor: ConstantId<'db>,
        parameters: Vec<Rc<Value<'db>>>,
        motive: Closure<'db>,
        branches: Vec<CaseBranch<'db>>,
    ) -> Case<'db> {
        Case {
            type_constructor,
            parameters,
            motive,
            branches,
        }
    }
}

#[derive(Clone, Debug)]
pub struct CaseBranch<'db> {
    pub constructor: ConstantId<'db>,
    pub arity: usize,
    pub body: Closure<'db>,
}

impl<'db> CaseBranch<'db> {
    pub fn new(constructor: ConstantId<'db>, arity: usize, body: Closure<'db>) -> CaseBranch<'db> {
        CaseBranch {
            constructor,
            arity,
            body,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Environment<'db, 'g> {
    pub global: &'g GlobalEnv<'db>,
    pub local: LocalEnv<'db>,
}

impl<'db, 'g> Environment<'db, 'g> {
    pub fn new(global: &'g GlobalEnv<'db>) -> Self {
        Self {
            global,
            local: LocalEnv::new(),
        }
    }

    // Forwarding methods to GlobalEnv

    // /// Lookup a global constant by name.
    // pub fn lookup(&self, name: ConstantId<'db>) -> Result<&Global<'db>, LookupError> {
    //     self.global.lookup(name)
    // }

    // /// Lookup a global definition by name.
    // pub fn definition(&self, name: ConstantId<'db>) -> Result<&Rc<Value<'db>>, LookupError> {
    //     self.global.definition(name)
    // }

    // /// Add a definition to the global environment.
    // pub fn add_definition(&mut self, name: ConstantId<'db>, value: Rc<Value<'db>>) {
    //     self.global.add_definition(name, value)
    // }

    /// Lookup a type constructor by name.
    pub fn type_constructor(
        &self,
        name: ConstantId<'db>,
    ) -> Result<&TypeConstructorInfo<'db>, LookupError> {
        self.global.type_constructor(name)
    }

    /// Add a type constructor to the global environment.
    // pub fn add_type_constructor(&mut self, name: ConstantId<'db>, info: TypeConstructorInfo<'db>) {
    //     self.global.add_type_constructor(name, info)
    // }

    /// Lookup a data constructor by name.
    pub fn data_constructor(
        &self,
        name: ConstantId<'db>,
    ) -> Result<&DataConstructorInfo<'db>, LookupError> {
        self.global.data_constructor(name)
    }

    /// Add a data constructor to the global environment.
    // pub fn add_data_constructor(&mut self, name: ConstantId<'db>, info: DataConstructorInfo<'db>) {
    //     self.global.add_data_constructor(name, info)
    // }

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

    /// Extend the environment with multiple variables.
    pub fn extend_vars<T>(&mut self, types: T)
    where
        T: IntoIterator<Item = Rc<Value<'db>>>,
    {
        self.local.extend_vars(types)
    }

    /// Pop the last value from the local environment.
    pub fn pop(&mut self) {
        self.local.pop()
    }

    /// Get the length of the local environment.
    pub fn len(&self) -> usize {
        self.local.depth()
    }

    /// Truncate the local environment to the given depth.
    pub fn truncate(&mut self, depth: usize) {
        self.local.truncate(depth)
    }
}

#[derive(Debug, Clone)]
pub enum LookupErrorKind {
    UnknownConstant,
    NotDefinition,
    NotTypeConstructor,
    NotDataConstructor,
}

#[derive(Debug, Clone)]
pub struct LookupError<'db> {
    pub kind: LookupErrorKind,
    pub id: ConstantId<'db>,
}

#[derive(Debug, Clone)]
pub struct MetavariableLookupError {
    pub id: MetaVariableId,
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
    /// Metavariable context mapping MetaVariableId to metavariable info.
    metavariables: HashMap<MetaVariableId, MetavariableInfo<'db>>,
}

impl<'db> GlobalEnv<'db> {
    pub fn new() -> Self {
        Self {
            constants: HashMap::new(),
            metavariables: HashMap::new(),
        }
    }

    /// Lookup a global constant by name.
    pub fn lookup(&self, name: ConstantId<'db>) -> Result<&Global<'db>, LookupError<'db>> {
        self.constants.get(&name).ok_or(LookupError {
            kind: LookupErrorKind::UnknownConstant,
            id: name,
        })
    }

    /// Lookup a global definition by name.
    pub fn definition(&self, name: ConstantId<'db>) -> Result<&Rc<Value<'db>>, LookupError<'db>> {
        match self.lookup(name)? {
            Global::Definition(value) => Ok(value),
            _ => Err(LookupError {
                kind: LookupErrorKind::NotDefinition,
                id: name,
            }),
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
    ) -> Result<&TypeConstructorInfo<'db>, LookupError<'db>> {
        match self.lookup(name)? {
            Global::TypeConstructor(info) => Ok(info),
            _ => Err(LookupError {
                kind: LookupErrorKind::NotTypeConstructor,
                id: name,
            }),
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
    ) -> Result<&DataConstructorInfo<'db>, LookupError<'db>> {
        match self.lookup(name)? {
            Global::DataConstructor(info) => Ok(info),
            _ => Err(LookupError {
                kind: LookupErrorKind::NotDataConstructor,
                id: name,
            }),
        }
    }

    /// Add a data constructor to the global environment.
    pub fn add_data_constructor(&mut self, name: ConstantId<'db>, info: DataConstructorInfo<'db>) {
        self.constants.insert(name, Global::DataConstructor(info));
    }

    /// Add a metavariable with its type to the global environment.
    pub fn add_metavariable<Args>(&mut self, id: MetaVariableId, args: Args, ty: RcSyntax<'db>)
    where
        Args: Into<Telescope<'db>>,
    {
        self.metavariables
            .insert(id, MetavariableInfo::new(args, ty));
    }

    /// Lookup metavariable info by id.
    pub fn metavariable(
        &self,
        id: MetaVariableId,
    ) -> Result<&MetavariableInfo<'db>, MetavariableLookupError> {
        self.metavariables
            .get(&id)
            .ok_or(MetavariableLookupError { id })
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

    /// Get an iterator over the values in the environment.
    pub fn iter(&self) -> std::slice::Iter<'_, Rc<Value<'db>>> {
        self.locals.iter()
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

    /// Truncate the environment to the given depth.
    pub fn truncate(&mut self, depth: usize) {
        self.locals.truncate(depth);
    }

    pub fn extend_vars<T>(&mut self, types: T)
    where
        T: IntoIterator<Item = Rc<Value<'db>>>,
    {
        for ty in types {
            self.push_var(ty);
        }
    }
}

impl<'db, 'g> Extend<Rc<Value<'db>>> for Environment<'db, 'g> {
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = Rc<Value<'db>>>,
    {
        self.local.locals.extend(iter);
    }
}

#[derive(Clone, Debug)]
pub struct TypeConstructorInfo<'db> {
    pub arguments: Telescope<'db>,
    pub num_parameters: usize,
    pub level: UniverseLevel,
}

impl<'db> TypeConstructorInfo<'db> {
    pub fn new<Args>(args: Args, num_parameters: usize, level: UniverseLevel) -> Self
    where
        Args: Into<Telescope<'db>>,
    {
        TypeConstructorInfo {
            arguments: args.into(),
            num_parameters,
            level,
        }
    }

    pub fn num_parameters(&self) -> usize {
        self.num_parameters
    }

    pub fn num_indices(&self) -> usize {
        self.arguments.len() - self.num_parameters
    }

    /// Get a slice of just the parameters.
    pub fn parameters(&self) -> &[RcSyntax<'db>] {
        &self.arguments.bindings[..self.num_parameters]
    }

    /// Get a slice of just the indices.
    pub fn indices(&self) -> &[RcSyntax<'db>] {
        &self.arguments.bindings[self.num_parameters..]
    }
}

#[derive(Clone, Debug)]
pub struct DataConstructorInfo<'db> {
    pub arguments: Telescope<'db>,
    pub ty: RcSyntax<'db>,
}

impl<'db> DataConstructorInfo<'db> {
    pub fn new<Args>(args: Args, ty: RcSyntax<'db>) -> Self
    where
        Args: Into<Telescope<'db>>,
    {
        DataConstructorInfo {
            arguments: args.into(),
            ty,
        }
    }
}

#[derive(Clone, Debug)]
pub struct MetavariableInfo<'db> {
    /// The telescope of argument types (the substitution).
    pub arguments: Telescope<'db>,
    /// The final type of the metavariable.
    pub ty: RcSyntax<'db>,
}

impl<'db> MetavariableInfo<'db> {
    pub fn new<Args>(args: Args, ty: RcSyntax<'db>) -> Self
    where
        Args: Into<Telescope<'db>>,
    {
        MetavariableInfo {
            arguments: args.into(),
            ty,
        }
    }
}

#[derive(Clone, Debug)]
pub struct SemTelescope<'db> {
    pub types: Vec<Rc<Value<'db>>>,
}
