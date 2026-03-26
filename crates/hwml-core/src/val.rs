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

    /// Apply the closure to a value by extending the local environment and evaluating.
    pub fn apply(&self, global: &GlobalEnv<'db>, arg: &RcValue<'db>) -> RcValue<'db> {
        let mut env = Environment {
            global,
            local: self.local.clone(),
            transparent: TransparentEnv::new(),
        };
        env.local.push(arg.clone());
        // If evaluation fails, return a dummy value (this should not happen in well-typed programs)
        crate::eval::eval(&mut env, &self.term).unwrap_or_else(|_| Value::UniverseCode(0).into())
    }
}

/// A value in normal form.
#[derive(Clone, Debug)]
pub struct Normal<'db> {
    pub ty: RcValue<'db>,
    pub value: RcValue<'db>,
}

impl<'db> Normal<'db> {
    pub fn new(ty: RcValue<'db>, value: RcValue<'db>) -> Normal<'db> {
        Normal { ty, value }
    }
}

pub type RcValue<'db> = Rc<Value<'db>>;

/// Fully normalized values in the semantic domain.
#[derive(Clone, Debug)]
pub enum Value<'db> {
    // ========== Evaluated type codes ==========
    /// Evaluated type code: Universe at level `n`
    UniverseCode(usize),

    /// Evaluated type code: Dependent function type
    PiCode(RcValue<'db>, Closure<'db>),

    /// Evaluated type code: Universe lifting for cumulativity
    /// The evaluated, structural representation of a shifted type code.
    LiftCode(usize, RcValue<'db>),

    /// Evaluated type code: The Bit type
    BitCode,

    // ========== Terms ==========
    Lambda(Lambda<'db>),
    Let(Let<'db>),

    TypeConstructor(TypeConstructor<'db>),
    DataConstructor(DataConstructor<'db>),

    EqType(EqType<'db>),
    Refl(Refl<'db>),
    Transport(Transport<'db>),

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

    Prim(Prim<'db>),
    Constant(Constant<'db>),
    /// Neutral headed by a variable.
    Rigid(Rigid<'db>),
    /// Neutral headed by a metavariable.
    Flex(Flex<'db>),
}

impl<'db> Value<'db> {
    pub fn lambda(body: Closure<'db>) -> Value<'db> {
        Value::Lambda(Lambda::new(body))
    }

    pub fn lambda_rc(body: Closure<'db>) -> RcValue<'db> {
        Rc::new(Value::lambda(body))
    }

    pub fn let_expr(ty: RcValue<'db>, value: RcValue<'db>, body: RcValue<'db>) -> Value<'db> {
        Value::Let(Let::new(ty, value, body))
    }

    pub fn let_expr_rc(ty: RcValue<'db>, value: RcValue<'db>, body: RcValue<'db>) -> RcValue<'db> {
        Rc::new(Value::let_expr(ty, value, body))
    }

    pub fn type_constructor(
        constructor: QualifiedName<'db>,
        arguments: Vec<RcValue<'db>>,
    ) -> Value<'db> {
        Value::TypeConstructor(TypeConstructor::new(constructor, arguments))
    }

    pub fn type_constructor_rc(
        constructor: QualifiedName<'db>,
        arguments: Vec<RcValue<'db>>,
    ) -> RcValue<'db> {
        Rc::new(Value::type_constructor(constructor, arguments))
    }

    pub fn data_constructor(
        constructor: QualifiedName<'db>,
        arguments: Vec<RcValue<'db>>,
    ) -> Value<'db> {
        Value::DataConstructor(DataConstructor::new(constructor, arguments))
    }

    pub fn data_constructor_rc(
        constructor: QualifiedName<'db>,
        arguments: Vec<RcValue<'db>>,
    ) -> RcValue<'db> {
        Rc::new(Value::data_constructor(constructor, arguments))
    }

    pub fn eq(ty: RcValue<'db>, lhs: RcValue<'db>, rhs: RcValue<'db>) -> Value<'db> {
        Value::EqType(EqType::new(ty, lhs, rhs))
    }

    pub fn eq_rc(ty: RcValue<'db>, lhs: RcValue<'db>, rhs: RcValue<'db>) -> RcValue<'db> {
        Rc::new(Value::eq(ty, lhs, rhs))
    }

    pub fn refl() -> Value<'db> {
        Value::Refl(Refl::new())
    }

    pub fn refl_rc() -> RcValue<'db> {
        Rc::new(Value::refl())
    }

    pub fn transport(motive: Closure<'db>, proof: RcValue<'db>, value: RcValue<'db>) -> Value<'db> {
        Value::Transport(Transport::new(motive, proof, value))
    }

    pub fn transport_rc(
        motive: Closure<'db>,
        proof: RcValue<'db>,
        value: RcValue<'db>,
    ) -> RcValue<'db> {
        Rc::new(Value::transport(motive, proof, value))
    }

    pub fn hardware_universe() -> Value<'db> {
        Value::HardwareUniverse(HardwareUniverse::new())
    }

    pub fn hardware_universe_rc() -> RcValue<'db> {
        Rc::new(Value::hardware_universe())
    }

    pub fn slift(ty: RcValue<'db>) -> Value<'db> {
        Value::SLift(SLift::new(ty))
    }

    pub fn slift_rc(ty: RcValue<'db>) -> RcValue<'db> {
        Rc::new(Value::slift(ty))
    }

    pub fn mlift(ty: RcValue<'db>) -> Value<'db> {
        Value::MLift(MLift::new(ty))
    }

    pub fn mlift_rc(ty: RcValue<'db>) -> RcValue<'db> {
        Rc::new(Value::mlift(ty))
    }

    pub fn signal_universe() -> Value<'db> {
        Value::SignalUniverse(SignalUniverse::new())
    }

    pub fn signal_universe_rc() -> RcValue<'db> {
        Rc::new(Value::signal_universe())
    }

    pub fn bit() -> Value<'db> {
        Value::Bit(Bit::new())
    }

    pub fn bit_rc() -> RcValue<'db> {
        Rc::new(Value::bit())
    }

    pub fn zero() -> Value<'db> {
        Value::Zero(Zero::new())
    }

    pub fn zero_rc() -> RcValue<'db> {
        Rc::new(Value::zero())
    }

    pub fn one() -> Value<'db> {
        Value::One(One::new())
    }

    pub fn one_rc() -> RcValue<'db> {
        Rc::new(Value::one())
    }

    pub fn module_universe() -> Value<'db> {
        Value::ModuleUniverse(ModuleUniverse::new())
    }

    pub fn module_universe_rc() -> RcValue<'db> {
        Rc::new(Value::module_universe())
    }

    pub fn harrow(source: RcValue<'db>, target: Closure<'db>) -> Value<'db> {
        Value::HArrow(HArrow::new(source, target))
    }

    pub fn harrow_rc(source: RcValue<'db>, target: Closure<'db>) -> RcValue<'db> {
        Rc::new(Value::harrow(source, target))
    }

    pub fn module(body: Closure<'db>) -> Value<'db> {
        Value::Module(Module::new(body))
    }

    pub fn module_rc(body: Closure<'db>) -> RcValue<'db> {
        Rc::new(Value::module(body))
    }

    pub fn happlication(
        module: RcValue<'db>,
        module_ty: RcValue<'db>,
        argument: RcValue<'db>,
    ) -> Value<'db> {
        Value::HApplication(HApplication::new(module, module_ty, argument))
    }

    pub fn happlication_rc(
        module: RcValue<'db>,
        module_ty: RcValue<'db>,
        argument: RcValue<'db>,
    ) -> RcValue<'db> {
        Rc::new(Value::happlication(module, module_ty, argument))
    }

    pub fn prim(name: QualifiedName<'db>) -> Value<'db> {
        Value::Prim(Prim::new(name))
    }

    pub fn prim_rc(name: QualifiedName<'db>) -> RcValue<'db> {
        Rc::new(Value::prim(name))
    }

    pub fn constant(name: QualifiedName<'db>) -> Value<'db> {
        Value::Constant(Constant::new(name))
    }

    pub fn constant_rc(name: QualifiedName<'db>) -> RcValue<'db> {
        Rc::new(Value::constant(name))
    }

    pub fn rigid(head: Variable, spine: Spine<'db>, ty: RcValue<'db>) -> Value<'db> {
        Value::Rigid(Rigid { head, spine, ty })
    }

    pub fn rigid_rc(head: Variable, spine: Spine<'db>, ty: RcValue<'db>) -> RcValue<'db> {
        Rc::new(Value::rigid(head, spine, ty))
    }

    pub fn variable(level: Level, ty: RcValue<'db>) -> Value<'db> {
        Value::rigid(Variable::new(level), Spine::empty(), ty)
    }

    pub fn variable_rc(level: Level, ty: RcValue<'db>) -> RcValue<'db> {
        Rc::new(Value::variable(level, ty))
    }

    pub fn flex(head: MetaVariable<'db>, spine: Spine<'db>, ty: RcValue<'db>) -> Value<'db> {
        Value::Flex(Flex { head, spine, ty })
    }

    pub fn flex_rc(head: MetaVariable<'db>, spine: Spine<'db>, ty: RcValue<'db>) -> RcValue<'db> {
        Rc::new(Value::flex(head, spine, ty))
    }

    pub fn metavariable(id: MetaVariableId, local: LocalEnv<'db>, ty: RcValue<'db>) -> Value<'db> {
        Value::flex(MetaVariable::new(id, local), Spine::empty(), ty)
    }

    pub fn metavariable_rc(
        id: MetaVariableId,
        local: LocalEnv<'db>,
        ty: RcValue<'db>,
    ) -> RcValue<'db> {
        Rc::new(Value::metavariable(id, local, ty))
    }

    pub fn identity_closure(id: MetaVariableId, ty: RcValue<'db>) -> Value<'db> {
        Value::flex(MetaVariable::new(id, LocalEnv::new()), Spine::empty(), ty)
    }

    pub fn identity_closure_rc(id: MetaVariableId, ty: RcValue<'db>) -> RcValue<'db> {
        Rc::new(Value::identity_closure(id, ty))
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
pub struct Let<'db> {
    pub ty: RcValue<'db>,
    pub value: RcValue<'db>,
    pub body: RcValue<'db>,
}

impl<'db> Let<'db> {
    pub fn new(ty: RcValue<'db>, value: RcValue<'db>, body: RcValue<'db>) -> Let<'db> {
        Let { ty, value, body }
    }
}

#[derive(Clone, Debug)]
pub struct TypeConstructor<'db> {
    /// The constructor constant id.
    pub constructor: QualifiedName<'db>,
    /// The argument values for this constructor instance
    pub arguments: Vec<RcValue<'db>>,
}

impl<'db> TypeConstructor<'db> {
    pub fn new(
        constructor: QualifiedName<'db>,
        arguments: Vec<RcValue<'db>>,
    ) -> TypeConstructor<'db> {
        TypeConstructor {
            constructor,
            arguments,
        }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, RcValue<'db>> {
        self.arguments.iter()
    }
}

// Implement IntoIterator for &TypeConstructor to allow iteration by reference
impl<'a, 'db> IntoIterator for &'a TypeConstructor<'db> {
    type Item = &'a RcValue<'db>;
    type IntoIter = std::slice::Iter<'a, RcValue<'db>>;

    fn into_iter(self) -> Self::IntoIter {
        self.arguments.iter()
    }
}

/// A data constructor instance with its arguments.
#[derive(Clone, Debug)]
pub struct DataConstructor<'db> {
    /// The constructor constant id
    pub constructor: QualifiedName<'db>,
    /// The argument values for this constructor instance
    pub arguments: Vec<RcValue<'db>>,
}

impl<'db> DataConstructor<'db> {
    pub fn new(
        constructor: QualifiedName<'db>,
        arguments: Vec<RcValue<'db>>,
    ) -> DataConstructor<'db> {
        DataConstructor {
            constructor,
            arguments,
        }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, RcValue<'db>> {
        self.arguments.iter()
    }
}

// Implement IntoIterator for &DataConstructor to allow iteration by reference
impl<'a, 'db> IntoIterator for &'a DataConstructor<'db> {
    type Item = &'a RcValue<'db>;
    type IntoIter = std::slice::Iter<'a, RcValue<'db>>;

    fn into_iter(self) -> Self::IntoIter {
        self.arguments.iter()
    }
}

#[derive(Clone, Debug)]
pub struct EqType<'db> {
    pub ty: RcValue<'db>,
    pub lhs: RcValue<'db>,
    pub rhs: RcValue<'db>,
}

impl<'db> EqType<'db> {
    pub fn new(ty: RcValue<'db>, lhs: RcValue<'db>, rhs: RcValue<'db>) -> EqType<'db> {
        EqType { ty, lhs, rhs }
    }
}

#[derive(Clone, Debug)]
pub struct Refl<'db> {
    _marker: PhantomData<&'db ()>,
}

impl<'db> Refl<'db> {
    pub fn new() -> Refl<'db> {
        Refl {
            _marker: PhantomData,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Transport<'db> {
    pub motive: Closure<'db>,
    pub proof: RcValue<'db>,
    pub value: RcValue<'db>,
}

impl<'db> Transport<'db> {
    pub fn new(motive: Closure<'db>, proof: RcValue<'db>, value: RcValue<'db>) -> Transport<'db> {
        Transport {
            motive,
            proof,
            value,
        }
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
    pub ty: RcValue<'db>,
}

impl<'db> SLift<'db> {
    pub fn new(ty: RcValue<'db>) -> SLift<'db> {
        SLift { ty }
    }
}

#[derive(Debug, Clone)]
pub struct MLift<'db> {
    pub ty: RcValue<'db>,
}

impl<'db> MLift<'db> {
    pub fn new(ty: RcValue<'db>) -> MLift<'db> {
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
    pub source: RcValue<'db>,
    pub target: Closure<'db>,
}

impl<'db> HArrow<'db> {
    pub fn new(source: RcValue<'db>, target: Closure<'db>) -> HArrow<'db> {
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
    pub module: RcValue<'db>,
    pub module_ty: RcValue<'db>,
    pub argument: RcValue<'db>,
}

impl<'db> HApplication<'db> {
    pub fn new(
        module: RcValue<'db>,
        module_ty: RcValue<'db>,
        argument: RcValue<'db>,
    ) -> HApplication<'db> {
        HApplication {
            module,
            module_ty,
            argument,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Prim<'db> {
    pub name: QualifiedName<'db>,
    _marker: PhantomData<&'db ()>,
}

impl<'db> Prim<'db> {
    pub fn new(name: QualifiedName<'db>) -> Prim<'db> {
        Prim {
            name,
            _marker: PhantomData,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constant<'db> {
    pub name: QualifiedName<'db>,
    _marker: PhantomData<&'db ()>,
}

impl<'db> Constant<'db> {
    pub fn new(name: QualifiedName<'db>) -> Constant<'db> {
        Constant {
            name,
            _marker: PhantomData,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Flex<'db> {
    pub ty: RcValue<'db>,
    pub head: MetaVariable<'db>,
    pub spine: Spine<'db>,
}

impl<'db> Flex<'db> {
    pub fn new(head: MetaVariable<'db>, spine: Spine<'db>, ty: RcValue<'db>) -> Flex<'db> {
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
    pub fn new(id: MetaVariableId, local: LocalEnv<'db>) -> MetaVariable<'db> {
        MetaVariable { id, local }
    }
}

#[derive(Clone, Debug)]
pub struct Rigid<'db> {
    pub ty: RcValue<'db>,
    pub head: Variable,
    pub spine: Spine<'db>,
}

impl<'db> Rigid<'db> {
    pub fn new(head: Variable, spine: Spine<'db>, ty: RcValue<'db>) -> Rigid<'db> {
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
        type_constructor: QualifiedName<'db>,
        parameters: Vec<RcValue<'db>>,
        branches: Vec<CaseBranch<'db>>,
    ) -> Eliminator<'db> {
        Eliminator::Case(Case::new(type_constructor, parameters, branches))
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
    pub type_constructor: QualifiedName<'db>,
    pub parameters: Vec<RcValue<'db>>,
    pub branches: Vec<CaseBranch<'db>>,
}

impl<'db> Case<'db> {
    pub fn new(
        type_constructor: QualifiedName<'db>,
        parameters: Vec<RcValue<'db>>,
        branches: Vec<CaseBranch<'db>>,
    ) -> Case<'db> {
        Case {
            type_constructor,
            parameters,
            branches,
        }
    }
}

#[derive(Clone, Debug)]
pub struct CaseBranch<'db> {
    pub constructor: QualifiedName<'db>,
    pub arity: usize,
    pub body: Closure<'db>,
}

impl<'db> CaseBranch<'db> {
    pub fn new(
        constructor: QualifiedName<'db>,
        arity: usize,
        body: Closure<'db>,
    ) -> CaseBranch<'db> {
        CaseBranch {
            constructor,
            arity,
            body,
        }
    }
}

/// Tracks transparent bindings (Let-bound variables) for δ-reduction.
#[derive(Clone, Debug)]
pub struct TransparentEnv<'db> {
    bindings: im::Vector<Option<RcValue<'db>>>,
}

impl<'db> TransparentEnv<'db> {
    pub fn new() -> Self {
        Self {
            bindings: im::Vector::new(),
        }
    }

    pub fn lookup(&self, level: Level) -> Option<RcValue<'db>> {
        let index: usize = level.into();
        self.bindings.get(index).and_then(|opt| opt.clone())
    }

    pub fn push_transparent(&mut self, value: RcValue<'db>) {
        self.bindings.push_back(Some(value));
    }

    pub fn push_rigid(&mut self) {
        self.bindings.push_back(None);
    }

    pub fn pop(&mut self) {
        self.bindings.pop_back();
    }

    pub fn truncate(&mut self, depth: usize) {
        self.bindings.truncate(depth);
    }

    pub fn depth(&self) -> usize {
        self.bindings.len()
    }
}

#[derive(Clone, Debug)]
pub struct Environment<'db, 'g> {
    pub global: &'g GlobalEnv<'db>,
    pub local: LocalEnv<'db>,
    pub transparent: TransparentEnv<'db>,
}

impl<'db, 'g> Environment<'db, 'g> {
    pub fn new(global: &'g GlobalEnv<'db>) -> Self {
        Self {
            global,
            local: LocalEnv::new(),
            transparent: TransparentEnv::new(),
        }
    }

    // Forwarding methods to GlobalEnv

    /// Lookup a type constructor by name.
    pub fn type_constructor(
        &self,
        name: QualifiedName<'db>,
    ) -> Result<&TypeConstructorInfo<'db>, LookupError<'_>> {
        self.global.type_constructor(name)
    }

    /// Lookup a data constructor by name.
    pub fn data_constructor(
        &self,
        name: QualifiedName<'db>,
    ) -> Result<&DataConstructorInfo<'db>, LookupError<'_>> {
        self.global.data_constructor(name)
    }

    // Forwarding methods to LocalEnv

    /// Get a local variable by level.
    /// Returns the rigid variable representation.
    /// NOTE: Does NOT unfold transparent bindings - that's the job of the conversion checker!
    pub fn get(&self, level: Level) -> RcValue<'db> {
        self.local.get(level).clone()
    }

    pub fn set(&mut self, level: Level, value: RcValue<'db>) {
        self.local.set(level, value)
    }

    /// The number of bound variables in scope.
    pub fn depth(&self) -> usize {
        self.local.depth()
    }

    /// Extend the environment by pushing a definition onto the end.
    /// This is rigid (not transparent) by default.
    pub fn push(&mut self, value: RcValue<'db>) {
        self.transparent.push_rigid();
        self.local.push(value)
    }

    /// Extend the environment by pushing a variable onto the end.
    pub fn push_var(&mut self, ty: RcValue<'db>) -> RcValue<'db> {
        self.transparent.push_rigid();
        self.local.push_var(ty)
    }

    /// Extend the environment with multiple variables.
    pub fn extend_vars<T>(&mut self, types: T)
    where
        T: IntoIterator<Item = RcValue<'db>>,
    {
        for ty in types {
            self.push_var(ty);
        }
    }

    /// Push a transparent binding (for Let expressions).
    /// This adds both the variable to the local environment and tracks it as transparent.
    pub fn push_transparent(&mut self, ty: RcValue<'db>, value: RcValue<'db>) -> RcValue<'db> {
        let var = self.local.push_var(ty);
        self.transparent.push_transparent(value);
        var
    }

    /// Look up a transparent binding for a variable.
    pub fn lookup_transparent(&self, level: Level) -> Option<RcValue<'db>> {
        self.transparent.lookup(level)
    }

    /// Pop the last value from the local environment.
    pub fn pop(&mut self) {
        self.local.pop();
        self.transparent.pop();
    }

    /// Get the length of the local environment.
    pub fn len(&self) -> usize {
        self.local.depth()
    }

    /// Truncate the local environment to the given depth.
    pub fn truncate(&mut self, depth: usize) {
        self.local.truncate(depth);
        self.transparent.truncate(depth);
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
    pub id: QualifiedName<'db>,
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
    /// Constant environment mapping QualifiedName to values.
    constants: HashMap<QualifiedName<'db>, Global<'db>>,
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

    pub fn contains(&self, name: QualifiedName<'db>) -> bool {
        self.constants.contains_key(&name)
    }

    /// Lookup a constant by name.
    pub fn constant(
        &self,
        name: QualifiedName<'db>,
    ) -> Result<&ConstantInfo<'db>, LookupError<'db>> {
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
    pub fn add_constant(&mut self, name: QualifiedName<'db>, info: ConstantInfo<'db>) {
        self.constants.insert(name, Global::Constant(info));
    }

    /// Lookup a primitive by name.
    pub fn primitive(
        &self,
        name: QualifiedName<'db>,
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
    pub fn add_primitive(&mut self, name: QualifiedName<'db>, info: PrimitiveInfo<'db>) {
        self.constants.insert(name, Global::Primitive(info));
    }

    /// Lookup a type constructor by name.
    pub fn type_constructor(
        &self,
        name: QualifiedName<'db>,
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
    pub fn add_type_constructor(
        &mut self,
        name: QualifiedName<'db>,
        info: TypeConstructorInfo<'db>,
    ) {
        self.constants.insert(name, Global::TypeConstructor(info));
    }

    /// Lookup a data constructor by name.
    pub fn data_constructor(
        &self,
        name: QualifiedName<'db>,
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
    pub fn add_data_constructor(
        &mut self,
        name: QualifiedName<'db>,
        info: DataConstructorInfo<'db>,
    ) {
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

    /// Iterate over all metavariables in the global environment.
    pub fn iter_metavariables(
        &self,
    ) -> impl Iterator<Item = (&MetaVariableId, &MetavariableInfo<'db>)> {
        self.metavariables.iter()
    }

    /// Get the maximum metavariable ID in the global environment, or None if empty.
    pub fn max_metavariable_id(&self) -> Option<MetaVariableId> {
        self.metavariables.keys().max().copied()
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
    /// The data constructors belonging to this type constructor.
    pub constructors: Vec<QualifiedName<'db>>,
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
            constructors: Vec::new(),
        }
    }

    pub fn num_parameters(&self) -> usize {
        self.num_parameters
    }

    pub fn num_indices(&self) -> usize {
        self.arguments.len() - self.num_parameters
    }

    pub fn parameters(&self) -> &[RcSyntax<'db>] {
        &self.arguments.bindings[..self.num_parameters]
    }

    pub fn indices(&self) -> &[RcSyntax<'db>] {
        &self.arguments.bindings[self.num_parameters..]
    }

    pub fn constructors(&self) -> &[QualifiedName<'db>] {
        &self.constructors
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
    locals: Vec<RcValue<'db>>,
}

impl<'db> LocalEnv<'db> {
    pub fn new() -> LocalEnv<'db> {
        Self { locals: Vec::new() }
    }

    pub fn get(&self, level: Level) -> &RcValue<'db> {
        let index: usize = level.into();
        &self.locals[index]
    }

    /// Set the value at a specific level.
    ///
    /// Used by pattern matching to turn a variable into a transparent let-binding
    /// when we learn its value (e.g., `n ~ @zero`). After this, any evaluation
    /// that looks up this level will see the new value instead of a rigid variable.
    pub fn set(&mut self, level: Level, value: RcValue<'db>) {
        let index: usize = level.into();
        self.locals[index] = value;
    }

    /// The number of bound variables in scope.
    pub fn depth(&self) -> usize {
        self.locals.len() as usize
    }

    /// Extend the environment by pushing a definition onto the end.
    pub fn push(&mut self, value: RcValue<'db>) {
        self.locals.push(value);
    }

    /// Extend the environment by pushing a variable onto the end.
    pub fn push_var(&mut self, ty: RcValue<'db>) -> RcValue<'db> {
        let depth = self.depth();
        let value = Value::variable_rc(Level::new(depth), ty);
        self.push(value.clone());
        value
    }

    pub fn pop(&mut self) {
        self.locals.pop();
    }

    /// Extend the environment with multiple values.
    pub fn extend<T>(&mut self, values: T)
    where
        T: IntoIterator<Item = RcValue<'db>>,
    {
        self.locals.extend(values);
    }

    /// Truncate the environment to the given depth.
    pub fn truncate(&mut self, depth: usize) {
        self.locals.truncate(depth);
    }

    pub fn extend_vars<T>(&mut self, types: T)
    where
        T: IntoIterator<Item = RcValue<'db>>,
    {
        for ty in types {
            self.push_var(ty);
        }
    }

    /// Iterate over the values in the environment.
    pub fn iter(&self) -> std::slice::Iter<'_, RcValue<'db>> {
        self.locals.iter()
    }
}

impl<'db, 'g> Extend<RcValue<'db>> for Environment<'db, 'g> {
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = RcValue<'db>>,
    {
        self.local.locals.extend(iter);
    }
}

#[derive(Clone, Debug)]
pub struct SemTelescope<'db> {
    pub types: Vec<RcValue<'db>>,
}
