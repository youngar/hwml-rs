use crate::*;
use std::{collections::HashMap, fmt, marker::PhantomData, rc::*};
use syn::{ConstantId, RcSyntax, RcSyntax, Syntax, Telescope};

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
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value<'db> {
    Universe(Universe),

    Prim(ConstantId<'db>),
    Constant(ConstantId<'db>),

    Pi(Pi<'db>),
    Lambda(Lambda<'db>),

    TypeConstructor(TypeConstructor<'db>),
    DataConstructor(DataConstructor<'db>),

    Lift(Rc<Value<'db>>),
    Quote(Rc<Value<'db>>),

    // HardwareUniverse values (bit-level and function-level)
    Zero,
    One,
    HVariable(HVariable),
    HConstant(ConstantId<'db>),
    HPrim(ConstantId<'db>),
    Module(HClosure<'db>),
    HApp(Rc<Value<'db>>, Rc<Value<'db>>),
    Splice(RcSyntax<'db>),

    HardwareUniverse(HardwareUniverse<'db>),
    SignalUniverse(SignalUniverse<'db>),
    Bit(Bit<'db>),

    ModuleUniverse(ModuleUniverse<'db>),
    HArrow(HArrow<'db>),

    /// Neutral headed by a metavariable.
    Flex(Flex<'db>),
    /// Neutral headed by a variable.
    Rigid(Rigid<'db>),
}

impl<'db> Value<'db> {
    pub fn constant(name: ConstantId<'db>) -> Value<'db> {
        Value::Constant(name)
    }

    pub fn prim(name: ConstantId<'db>) -> Value<'db> {
        Value::Prim(name)
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

    pub fn variable(level: Level, ty: Rc<Value<'db>>) -> Value<'db> {
        Value::rigid(Variable::new(level), Spine::empty(), ty)
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

    pub fn lift(hw_type: Rc<Value<'db>>) -> Value<'db> {
        Value::Lift(hw_type)
    }

    pub fn quote(hw_value: Rc<Value<'db>>) -> Value<'db> {
        Value::Quote(hw_value)
    }

    // Constructors for hardware values in the unified domain
    pub fn zero() -> Value<'db> {
        Value::Zero
    }

    pub fn one() -> Value<'db> {
        Value::One
    }

    pub fn hvariable(level: Level) -> Value<'db> {
        Value::HVariable(HVariable::new(level))
    }

    pub fn splce(term: RcSyntax<'db>) -> Value<'db> {
        Value::Splice(term)
    }

    pub fn hconstant(name: ConstantId<'db>) -> Value<'db> {
        Value::HConstant(name)
    }

    pub fn hprim(name: ConstantId<'db>) -> Value<'db> {
        Value::HPrim(name)
    }

    pub fn Module(
        env: HEnvironment<'db>,
        local: LocalEnv<'db>,
        body: Rc<Syntax<'db>>,
    ) -> Value<'db> {
        Value::Module(HClosure::new(env, local, body))
    }

    pub fn happ(fun: Rc<Value<'db>>, arg: Rc<Value<'db>>) -> Value<'db> {
        Value::HApp(fun, arg)
    }

    pub fn HardwareUniverse() -> Value<'db> {
        Value::HardwareUniverse(HardwareUniverse::new())
    }

    pub fn signal_universe() -> Value<'db> {
        Value::SignalUniverse(SignalUniverse::new())
    }

    pub fn bit() -> Value<'db> {
        Value::Bit(Bit::new())
    }

    pub fn module_universe() -> Value<'db> {
        Value::ModuleUniverse(ModuleUniverse::new())
    }

    pub fn harrow(source: Rc<Value<'db>>, target: Rc<Value<'db>>) -> Value<'db> {
        Value::HArrow(HArrow::new(source, target))
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

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone, Copy)]
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

impl<'db> Default for HardwareUniverse<'db> {
    fn default() -> Self {
        HardwareUniverse::new()
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone, Copy)]
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

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone, Copy)]
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

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone, Copy)]
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

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone, Copy)]
pub struct HArrow<'db> {
    pub source: Rc<Value<'db>>,
    pub target: Rc<Value<'db>>,
}

impl<'db> HArrow<'db> {
    pub fn new(source: Rc<Value<'db>>, target: Rc<Value<'db>>) -> HArrow<'db> {
        HArrow { source, target }
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HVariable {
    pub level: Level,
}

impl HVariable {
    pub fn new(level: Level) -> HVariable {
        HVariable { level }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Module<'db> {
    pub env: HEnvironment<'db>,
    pub local: LocalEnv<'db>,
    pub body: Rc<Syntax<'db>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Splice<'db> {
    pub term: RcSyntax<'db>,
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
    NotConstant,
    NotTypeConstructor,
    NotDataConstructor,
    NotPrimitive,
    NotHardwarePrimitive,
    NotHardwareConstant,
}

impl<'db> fmt::Display for LookupErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownConstant => f.write_str("unknown constant"),
            Self::NotConstant => f.write_str("not a constant"),
            Self::NotTypeConstructor => f.write_str("not a type constructor"),
            Self::NotDataConstructor => f.write_str("not a data constructor"),
            Self::NotPrimitive => f.write_str("not a primitive"),
            Self::NotHardwarePrimitive => f.write_str("not a hardware primitive"),
            Self::NotHardwareConstant => f.write_str("not a hardware constant"),
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

    HardwareConstant(HardwareConstantInfo<'db>),
    HardwarePrimitive(HardwarePrimitiveInfo<'db>),
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

    /// Lookup a constant by name.
    pub fn constant(&self, name: ConstantId<'db>) -> Result<&ConstantInfo<'db>, LookupError<'db>> {
        match self.lookup(name)? {
            Global::Constant(info) => Ok(info),
            _ => Err(LookupError {
                kind: LookupErrorKind::NotConstant,
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
        match self.lookup(name)? {
            Global::Primitive(info) => Ok(info),
            _ => Err(LookupError {
                kind: LookupErrorKind::NotPrimitive,
                id: name,
            }),
        }
    }

    /// Add a primitive to the global environment.
    pub fn add_primitive(&mut self, name: ConstantId<'db>, info: PrimitiveInfo<'db>) {
        self.constants.insert(name, Global::Primitive(info));
    }

    /// Lookup a hardware primitive by name.
    pub fn hardware_primitive(
        &self,
        name: ConstantId<'db>,
    ) -> Result<&HardwarePrimitiveInfo<'db>, LookupError<'db>> {
        match self.lookup(name)? {
            Global::HardwarePrimitive(info) => Ok(info),
            _ => Err(LookupError {
                kind: LookupErrorKind::NotHardwarePrimitive,
                id: name,
            }),
        }
    }

    /// Add a hardware primitive to the global environment.
    pub fn add_hardware_primitive(
        &mut self,
        name: ConstantId<'db>,
        info: HardwarePrimitiveInfo<'db>,
    ) {
        self.constants.insert(name, Global::HardwarePrimitive(info));
    }

    /// Lookup a hardware constant by name.
    pub fn hardware_constant(
        &self,
        name: ConstantId<'db>,
    ) -> Result<&HardwareConstantInfo<'db>, LookupError<'db>> {
        match self.lookup(name)? {
            Global::HardwareConstant(info) => Ok(info),
            _ => Err(LookupError {
                kind: LookupErrorKind::NotHardwareConstant,
                id: name,
            }),
        }
    }

    /// Add a hardware constant to the global environment.
    pub fn add_hardware_constant(
        &mut self,
        name: ConstantId<'db>,
        info: HardwareConstantInfo<'db>,
    ) {
        self.constants.insert(name, Global::HardwareConstant(info));
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
    ) -> Result<&MetavariableInfo<'db>, MetaVariableLookupError> {
        self.metavariables
            .get(&id)
            .ok_or(MetaVariableLookupError { id })
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
pub struct HardwareConstantInfo<'db> {
    pub ty: RcSyntax<'db>,
    pub value: RcSyntax<'db>,
}

impl<'db> HardwareConstantInfo<'db> {
    pub fn new(ty: RcSyntax<'db>, value: RcSyntax<'db>) -> Self {
        HardwareConstantInfo { ty, value }
    }
}

#[derive(Clone, Debug)]
pub struct HardwarePrimitiveInfo<'db> {
    pub ty: RcSyntax<'db>,
}

impl<'db> HardwarePrimitiveInfo<'db> {
    pub fn new(ty: RcSyntax<'db>) -> Self {
        HardwarePrimitiveInfo { ty }
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

/// A closure for hardware lambdas.
/// Similar to meta-level `Closure` but for hardware terms.
///
/// Note: unlike the original design, hardware closures **do** capture the
/// meta-level local environment. This is required for correctness when
/// quotes produce hardware functions whose bodies contain splices that
/// reference meta-level variables (e.g. recursive generators like QueueGen).
#[derive(Clone, Debug)]
pub struct HClosure<'db> {
    /// The environment of hardware values
    pub env: HEnvironment<'db>,
    /// The captured meta-level local environment
    pub local: LocalEnv<'db>,
    /// The body of the lambda
    pub body: Rc<Syntax<'db>>,
}

impl<'db> HClosure<'db> {
    pub fn new(
        env: HEnvironment<'db>,
        local: LocalEnv<'db>,
        body: Rc<Syntax<'db>>,
    ) -> HClosure<'db> {
        HClosure { env, local, body }
    }
}

// We keep equality for HValue by defining equality for HClosure in terms of
// its hardware environment and body only. The captured meta environment is
// ignored for Eq/PartialEq – it is semantically relevant but not currently
// used in any equality-based reasoning or tests.
impl<'db> PartialEq for HClosure<'db> {
    fn eq(&self, other: &Self) -> bool {
        self.env == other.env && self.body == other.body
    }
}

impl<'db> Eq for HClosure<'db> {}

/// Environment for hardware evaluation.
/// Maps hardware variables (de Bruijn levels) to hardware values in the unified domain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HEnvironment<'db> {
    pub values: Vec<Rc<Value<'db>>>,
}

impl<'db> HEnvironment<'db> {
    pub fn new() -> HEnvironment<'db> {
        HEnvironment { values: Vec::new() }
    }

    pub fn push(&mut self, value: Rc<Value<'db>>) {
        self.values.push(value);
    }

    pub fn pop(&mut self) {
        self.values.pop();
    }

    pub fn get(&self, level: Level) -> Option<&Rc<Value<'db>>> {
        self.values.get(level.0)
    }

    pub fn len(&self) -> usize {
        self.values.len()
    }

    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    pub fn depth(&self) -> usize {
        self.values.len()
    }
}

impl<'db> Default for HEnvironment<'db> {
    fn default() -> Self {
        Self::new()
    }
}
