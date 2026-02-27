use crate::*;
use std::{collections::HashMap, fmt, marker::PhantomData, rc::*};
use syn::{RcSyntax, Telescope};

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
    Universe(Universe<'db>),
    Lift(Lift<'db>),

    Pi(Pi<'db>),
    Lambda(Lambda<'db>),

    TypeConstructor(TypeConstructor<'db>),
    DataConstructor(DataConstructor<'db>),

    HardwareUniverse(HardwareUniverse<'db>),
    SLift(SLift<'db>),
    MLift(MLift<'db>),

    SignalUniverse(SignalUniverse<'db>),
    Bit(Bit<'db>),
    Zero(Zero<'db>),
    One(One<'db>),

    ModuleUniverse(ModuleUniverse<'db>),
    HArrow(HArrow<'db>),
    Module(Module<'db>),
    HApplication(HApplication<'db>),

    Prim(ConstantId<'db>),
    Constant(ConstantId<'db>),
    /// Neutral headed by a variable.
    Rigid(Rigid<'db>),
    /// Neutral headed by a metavariable.
    Flex(Flex<'db>),
}

impl<'db> Value<'db> {
    pub fn universe(level: UniverseLevel) -> Value<'db> {
        Value::Universe(Universe::new(level))
    }

    pub fn lift(ty: Rc<Value<'db>>) -> Value<'db> {
        Value::Lift(Lift::new(ty))
    }

    pub fn pi(source: Rc<Value<'db>>, target: Closure<'db>) -> Value<'db> {
        Value::Pi(Pi::new(source, target))
    }

    pub fn lambda(body: Closure<'db>) -> Value<'db> {
        Value::Lambda(Lambda::new(body))
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

    pub fn hardware_universe() -> Value<'db> {
        Value::HardwareUniverse(HardwareUniverse::new())
    }

    pub fn slift(ty: Rc<Value<'db>>) -> Value<'db> {
        Value::SLift(SLift::new(ty))
    }

    pub fn mlift(ty: Rc<Value<'db>>) -> Value<'db> {
        Value::MLift(MLift::new(ty))
    }

    pub fn signal_universe() -> Value<'db> {
        Value::SignalUniverse(SignalUniverse::new())
    }

    pub fn bit() -> Value<'db> {
        Value::Bit(Bit::new())
    }

    pub fn zero() -> Value<'db> {
        Value::Zero(Zero::new())
    }

    pub fn one() -> Value<'db> {
        Value::One(One::new())
    }

    pub fn module_universe() -> Value<'db> {
        Value::ModuleUniverse(ModuleUniverse::new())
    }

    pub fn harrow(source: Rc<Value<'db>>, target: Closure<'db>) -> Value<'db> {
        Value::HArrow(HArrow::new(source, target))
    }

    pub fn module(body: Closure<'db>) -> Value<'db> {
        Value::Module(Module::new(body))
    }

    pub fn happlication(
        module: Rc<Value<'db>>,
        module_ty: Rc<Value<'db>>,
        argument: Rc<Value<'db>>,
    ) -> Value<'db> {
        Value::HApplication(HApplication::new(module, module_ty, argument))
    }

    pub fn prim(name: ConstantId<'db>) -> Value<'db> {
        Value::Prim(name)
    }

    pub fn constant(name: ConstantId<'db>) -> Value<'db> {
        Value::Constant(name)
    }

    pub fn rigid(head: Variable, spine: Spine<'db>, ty: Rc<Value<'db>>) -> Value<'db> {
        Value::Rigid(Rigid { head, spine, ty })
    }

    pub fn variable(level: Level, ty: Rc<Value<'db>>) -> Value<'db> {
        Value::rigid(Variable::new(level), Spine::empty(), ty)
    }

    pub fn flex(head: MetaVariable<'db>, spine: Spine<'db>, ty: Rc<Value<'db>>) -> Value<'db> {
        Value::Flex(Flex { head, spine, ty })
    }

    pub fn metavariable(
        id: MetaVariableId,
        local: LocalEnv<'db>,
        ty: Rc<Value<'db>>,
    ) -> Value<'db> {
        Value::flex(MetaVariable::new(id, local), Spine::empty(), ty)
    }

    pub fn identity_closure(id: MetaVariableId, ty: Rc<Value<'db>>) -> Value<'db> {
        Value::flex(MetaVariable::new(id, LocalEnv::new()), Spine::empty(), ty)
    }
}

#[derive(Clone, Debug)]
pub struct Universe<'db> {
    pub level: UniverseLevel,
    _marker: PhantomData<&'db ()>,
}

impl<'db> Universe<'db> {
    pub fn new(level: UniverseLevel) -> Universe<'db> {
        Universe {
            level,
            _marker: PhantomData,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Lift<'db> {
    pub ty: Rc<Value<'db>>,
}

impl<'db> Lift<'db> {
    pub fn new(ty: Rc<Value<'db>>) -> Lift<'db> {
        Lift { ty }
    }
}

#[derive(Clone, Debug)]
pub struct Pi<'db> {
    pub source: Rc<Value<'db>>,
    pub target: Closure<'db>,
}

impl<'db> Pi<'db> {
    pub fn new(source: Rc<Value<'db>>, target: Closure<'db>) -> Pi<'db> {
        Pi { source, target }
    }
}

#[derive(Clone, Debug)]
pub struct Lambda<'db> {
    pub body: Closure<'db>,
}

impl<'db> Lambda<'db> {
    pub fn new(body: Closure<'db>) -> Lambda<'db> {
        Lambda { body }
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

#[derive(Debug, Clone)]
pub struct HardwareUniverse<'db> {
    _marker: PhantomData<&'db ()>,
}

impl<'db> HardwareUniverse<'db> {
    pub fn new() -> HardwareUniverse<'db> {
        HardwareUniverse {
            _marker: PhantomData,
        }
    }
}

#[derive(Debug, Clone)]
pub struct SLift<'db> {
    pub ty: Rc<Value<'db>>,
}

impl<'db> SLift<'db> {
    pub fn new(ty: Rc<Value<'db>>) -> SLift<'db> {
        SLift { ty }
    }
}

#[derive(Debug, Clone)]
pub struct MLift<'db> {
    pub ty: Rc<Value<'db>>,
}

impl<'db> MLift<'db> {
    pub fn new(ty: Rc<Value<'db>>) -> MLift<'db> {
        MLift { ty }
    }
}

#[derive(Debug, Clone)]
pub struct SignalUniverse<'db> {
    _marker: PhantomData<&'db ()>,
}

impl<'db> SignalUniverse<'db> {
    pub fn new() -> SignalUniverse<'db> {
        SignalUniverse {
            _marker: PhantomData,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Bit<'db> {
    _marker: PhantomData<&'db ()>,
}

impl<'db> Bit<'db> {
    pub fn new() -> Bit<'db> {
        Bit {
            _marker: PhantomData,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Zero<'db> {
    _marker: PhantomData<&'db ()>,
}

impl<'db> Zero<'db> {
    pub fn new() -> Zero<'db> {
        Zero {
            _marker: PhantomData,
        }
    }
}

#[derive(Debug, Clone)]
pub struct One<'db> {
    _marker: PhantomData<&'db ()>,
}

impl<'db> One<'db> {
    pub fn new() -> One<'db> {
        One {
            _marker: PhantomData,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ModuleUniverse<'db> {
    _marker: PhantomData<&'db ()>,
}

impl<'db> ModuleUniverse<'db> {
    pub fn new() -> ModuleUniverse<'db> {
        ModuleUniverse {
            _marker: PhantomData,
        }
    }
}

#[derive(Clone, Debug)]
pub struct HArrow<'db> {
    pub source: Rc<Value<'db>>,
    pub target: Closure<'db>,
}

impl<'db> HArrow<'db> {
    pub fn new(source: Rc<Value<'db>>, target: Closure<'db>) -> HArrow<'db> {
        HArrow { source, target }
    }
}

#[derive(Debug, Clone)]
pub struct Module<'db> {
    pub body: Closure<'db>,
}

impl<'db> Module<'db> {
    pub fn new(body: Closure<'db>) -> Module<'db> {
        Module { body }
    }
}

#[derive(Debug, Clone)]
pub struct HApplication<'db> {
    pub module: Rc<Value<'db>>,
    pub module_ty: Rc<Value<'db>>,
    pub argument: Rc<Value<'db>>,
}

impl<'db> HApplication<'db> {
    pub fn new(
        module: Rc<Value<'db>>,
        module_ty: Rc<Value<'db>>,
        argument: Rc<Value<'db>>,
    ) -> HApplication<'db> {
        HApplication {
            module,
            module_ty,
            argument,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Constant<'db> {
    pub name: ConstantId<'db>,
}

#[derive(Clone, Debug)]
pub struct Flex<'db> {
    pub ty: Rc<Value<'db>>,
    pub head: MetaVariable<'db>,
    pub spine: Spine<'db>,
}

impl<'db> Flex<'db> {
    pub fn new(head: MetaVariable<'db>, spine: Spine<'db>, ty: Rc<Value<'db>>) -> Flex<'db> {
        Flex { head, spine, ty }
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

#[derive(Clone, Debug)]
pub struct Rigid<'db> {
    pub ty: Rc<Value<'db>>,
    pub head: Variable,
    pub spine: Spine<'db>,
}

impl<'db> Rigid<'db> {
    pub fn new(head: Variable, spine: Spine<'db>, ty: Rc<Value<'db>>) -> Rigid<'db> {
        Rigid { head, spine, ty }
    }
}

#[derive(Clone, Debug)]
pub struct Variable {
    pub level: Level,
}

impl Variable {
    pub fn new(level: Level) -> Variable {
        Variable { level }
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

    /// Lookup a type constructor by name.
    pub fn type_constructor(
        &self,
        name: ConstantId<'db>,
    ) -> Result<&TypeConstructorInfo<'db>, LookupError> {
        self.global.type_constructor(name)
    }

    /// Lookup a data constructor by name.
    pub fn data_constructor(
        &self,
        name: ConstantId<'db>,
    ) -> Result<&DataConstructorInfo<'db>, LookupError> {
        self.global.data_constructor(name)
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
    NotConstant,
    NotTypeConstructor,
    NotDataConstructor,
    NotPrimitive,
}

impl<'db> fmt::Display for LookupErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownConstant => f.write_str("unknown constant"),
            Self::NotConstant => f.write_str("not a constant"),
            Self::NotTypeConstructor => f.write_str("not a type constructor"),
            Self::NotDataConstructor => f.write_str("not a data constructor"),
            Self::NotPrimitive => f.write_str("not a primitive"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct LookupError<'db> {
    pub kind: LookupErrorKind,
    pub id: ConstantId<'db>,
}

impl<'db> fmt::Display for LookupError<'db> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

/// Result type for looking up a specific kind of global definition.
#[derive(Debug, Clone)]
pub enum LookupResult<'a, T> {
    /// The lookup succeeded and found the expected type.
    Found(&'a T),
    /// The constant exists but is not of the expected type.
    WrongKind(LookupErrorKind),
    /// The constant does not exist.
    NotFound,
}

#[derive(Debug, Clone)]
pub struct MetaVariableLookupError {
    pub id: MetaVariableId,
}

impl fmt::Display for MetaVariableLookupError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "unknown metavariable: {}", self.id)
    }
}

#[derive(Clone, Debug)]
pub enum Global<'db> {
    Constant(ConstantInfo<'db>),
    Primitive(PrimitiveInfo<'db>),
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

    /// Lookup a constant by name.
    pub fn constant(&self, name: ConstantId<'db>) -> Result<&ConstantInfo<'db>, LookupError<'db>> {
        match self.constants.get(&name) {
            Some(Global::Constant(info)) => Ok(info),
            Some(_) => Err(LookupError {
                kind: LookupErrorKind::NotConstant,
                id: name,
            }),
            None => Err(LookupError {
                kind: LookupErrorKind::UnknownConstant,
                id: name,
            }),
        }
    }

    /// Add a constant to the global environment.
    pub fn add_constant(&mut self, name: ConstantId<'db>, info: ConstantInfo<'db>) {
        self.constants.insert(name, Global::Constant(info));
    }

    /// Lookup a primitive by name.
    pub fn primitive(
        &self,
        name: ConstantId<'db>,
    ) -> Result<&PrimitiveInfo<'db>, LookupError<'db>> {
        match self.constants.get(&name) {
            Some(Global::Primitive(info)) => Ok(info),
            Some(_) => Err(LookupError {
                kind: LookupErrorKind::NotPrimitive,
                id: name,
            }),
            None => Err(LookupError {
                kind: LookupErrorKind::UnknownConstant,
                id: name,
            }),
        }
    }

    /// Add a primitive to the global environment.
    pub fn add_primitive(&mut self, name: ConstantId<'db>, info: PrimitiveInfo<'db>) {
        self.constants.insert(name, Global::Primitive(info));
    }

    /// Lookup a type constructor by name.
    pub fn type_constructor(
        &self,
        name: ConstantId<'db>,
    ) -> Result<&TypeConstructorInfo<'db>, LookupError<'db>> {
        match self.constants.get(&name) {
            Some(Global::TypeConstructor(info)) => Ok(info),
            Some(_) => Err(LookupError {
                kind: LookupErrorKind::NotTypeConstructor,
                id: name,
            }),
            None => Err(LookupError {
                kind: LookupErrorKind::UnknownConstant,
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
        match self.constants.get(&name) {
            Some(Global::DataConstructor(info)) => Ok(info),
            Some(_) => Err(LookupError {
                kind: LookupErrorKind::NotDataConstructor,
                id: name,
            }),
            None => Err(LookupError {
                kind: LookupErrorKind::UnknownConstant,
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
    ) -> Result<&MetavariableInfo<'db>, MetaVariableLookupError> {
        self.metavariables
            .get(&id)
            .ok_or(MetaVariableLookupError { id })
    }
}

#[derive(Clone, Debug)]
pub struct ConstantInfo<'db> {
    pub ty: RcSyntax<'db>,
    pub value: RcSyntax<'db>,
}

impl<'db> ConstantInfo<'db> {
    pub fn new(ty: RcSyntax<'db>, value: RcSyntax<'db>) -> Self {
        ConstantInfo { ty, value }
    }
}

#[derive(Clone, Debug)]
pub struct PrimitiveInfo<'db> {
    pub ty: RcSyntax<'db>,
}

impl<'db> PrimitiveInfo<'db> {
    pub fn new(ty: RcSyntax<'db>) -> Self {
        PrimitiveInfo { ty }
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
        let value = Rc::new(Value::variable(Level::new(depth), ty));
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

    /// Iterate over the values in the environment.
    pub fn iter(&self) -> std::slice::Iter<'_, Rc<Value<'db>>> {
        self.locals.iter()
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
pub struct SemTelescope<'db> {
    pub types: Vec<Rc<Value<'db>>>,
}
