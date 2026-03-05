use crate::common::{Index, MetaVariableId, UniverseLevel};
use crate::ConstantId;
use hwml_support::IntoWithDb;
use std::{marker::PhantomData, rc::Rc};

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Telescope<'db> {
    pub bindings: Box<[RcSyntax<'db>]>,
}

impl<'db> Telescope<'db> {
    pub fn new<T>(bindings: T) -> Self
    where
        T: Into<Box<[RcSyntax<'db>]>>,
    {
        Telescope {
            bindings: bindings.into(),
        }
    }

    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    pub fn iter(&self) -> std::slice::Iter<'_, RcSyntax<'db>> {
        self.bindings.iter()
    }
}

impl<'db, T> From<T> for Telescope<'db>
where
    T: Into<Box<[RcSyntax<'db>]>>,
{
    fn from(bindings: T) -> Self {
        Telescope::new(bindings.into())
    }
}

impl<'db> FromIterator<RcSyntax<'db>> for Telescope<'db> {
    fn from_iter<T: IntoIterator<Item = RcSyntax<'db>>>(iter: T) -> Self {
        Vec::from_iter(iter).into()
    }
}

impl<'a, 'db> IntoIterator for &'a Telescope<'db> {
    type Item = &'a RcSyntax<'db>;
    type IntoIter = std::slice::Iter<'a, RcSyntax<'db>>;

    fn into_iter(self) -> Self::IntoIter {
        self.bindings.iter()
    }
}

pub type RcSyntax<'db> = Rc<Syntax<'db>>;

pub type Tm<'db> = Syntax<'db>;
pub type Ty<'db> = Syntax<'db>;

/// A closure in the syntax: [var] |- body
/// This represents a term with a single explicit variable binder.
/// Multiple binders like [%0 %1] |- body are represented as nested closures.
/// Used for transport motives and potentially other constructs.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Closure<'db> {
    /// The body term (may reference variable 0, or be another closure for multiple binders)
    pub body: RcSyntax<'db>,
}

impl<'db> Closure<'db> {
    pub fn new(body: RcSyntax<'db>) -> Closure<'db> {
        Closure { body }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub enum Syntax<'db> {
    Universe(Universe<'db>),
    Lift(Lift<'db>),

    Pi(Pi<'db>),
    Lambda(Lambda<'db>),
    Application(Application<'db>),

    TypeConstructor(TypeConstructor<'db>),
    DataConstructor(DataConstructor<'db>),
    Case(Case<'db>),

    Eq(EqType<'db>),
    Refl(Refl<'db>),
    Transport(Transport<'db>),
    Closure(Closure<'db>),

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
    Variable(Variable<'db>),
    Metavariable(Metavariable<'db>),

    Check(Check<'db>),
}

impl<'db> Syntax<'db> {
    pub fn universe(level: UniverseLevel) -> Syntax<'db> {
        Syntax::Universe(Universe::new(level))
    }

    pub fn universe_rc(level: UniverseLevel) -> RcSyntax<'db> {
        Rc::new(Syntax::universe(level))
    }

    pub fn lift(ty: RcSyntax<'db>) -> Syntax<'db> {
        Syntax::Lift(Lift::new(ty))
    }

    pub fn lift_rc(ty: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::lift(ty))
    }

    pub fn pi(source: RcSyntax<'db>, target: RcSyntax<'db>) -> Syntax<'db> {
        Syntax::Pi(Pi::new(source, target))
    }

    pub fn pi_rc(source: RcSyntax<'db>, target: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::pi(source, target))
    }

    pub fn lambda(body: RcSyntax<'db>) -> Syntax<'db> {
        Syntax::Lambda(Lambda::new(body))
    }

    pub fn lambda_rc(body: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::lambda(body))
    }

    pub fn application(fun: RcSyntax<'db>, arg: RcSyntax<'db>) -> Syntax<'db> {
        Syntax::Application(Application::new(fun, arg))
    }

    pub fn application_rc(fun: RcSyntax<'db>, arg: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::application(fun, arg))
    }

    pub fn type_constructor(name: ConstantId<'db>, arguments: Vec<RcSyntax<'db>>) -> Syntax<'db> {
        Syntax::TypeConstructor(TypeConstructor::new(name, arguments))
    }

    pub fn type_constructor_rc(
        name: ConstantId<'db>,
        arguments: Vec<RcSyntax<'db>>,
    ) -> RcSyntax<'db> {
        Rc::new(Syntax::type_constructor(name, arguments))
    }

    pub fn data_constructor(
        constructor: ConstantId<'db>,
        arguments: Vec<RcSyntax<'db>>,
    ) -> Syntax<'db> {
        Syntax::DataConstructor(DataConstructor::new(constructor, arguments))
    }

    pub fn data_constructor_rc(
        constructor: ConstantId<'db>,
        arguments: Vec<RcSyntax<'db>>,
    ) -> RcSyntax<'db> {
        Rc::new(Syntax::data_constructor(constructor, arguments))
    }

    pub fn case(scrutinee: Index, branches: Vec<CaseBranch<'db>>) -> Syntax<'db> {
        Syntax::Case(Case::new(Variable::new(scrutinee), branches))
    }

    pub fn case_rc(scrutinee: Index, branches: Vec<CaseBranch<'db>>) -> RcSyntax<'db> {
        Rc::new(Syntax::case(scrutinee, branches))
    }

    pub fn eq(ty: RcSyntax<'db>, lhs: RcSyntax<'db>, rhs: RcSyntax<'db>) -> Syntax<'db> {
        Syntax::Eq(EqType::new(ty, lhs, rhs))
    }

    pub fn eq_rc(ty: RcSyntax<'db>, lhs: RcSyntax<'db>, rhs: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::eq(ty, lhs, rhs))
    }

    pub fn refl() -> Syntax<'db> {
        Syntax::Refl(Refl::new())
    }

    pub fn refl_rc() -> RcSyntax<'db> {
        Rc::new(Syntax::refl())
    }

    pub fn transport(
        motive: Closure<'db>,
        proof: RcSyntax<'db>,
        value: RcSyntax<'db>,
    ) -> Syntax<'db> {
        Syntax::Transport(Transport::new(motive, proof, value))
    }

    pub fn transport_rc(
        motive: Closure<'db>,
        proof: RcSyntax<'db>,
        value: RcSyntax<'db>,
    ) -> RcSyntax<'db> {
        Rc::new(Syntax::transport(motive, proof, value))
    }

    pub fn closure(body: RcSyntax<'db>) -> Syntax<'db> {
        Syntax::Closure(Closure::new(body))
    }

    pub fn closure_rc(body: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::closure(body))
    }

    pub fn hardware() -> Syntax<'db> {
        Syntax::HardwareUniverse(HardwareUniverse::new())
    }

    pub fn hardware_rc() -> RcSyntax<'db> {
        Rc::new(Syntax::hardware())
    }

    pub fn slift(ty: RcSyntax<'db>) -> Syntax<'db> {
        Syntax::SLift(SLift::new(ty))
    }

    pub fn slift_rc(ty: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::slift(ty))
    }

    pub fn mlift(ty: RcSyntax<'db>) -> Syntax<'db> {
        Syntax::MLift(MLift::new(ty))
    }

    pub fn mlift_rc(ty: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::mlift(ty))
    }

    pub fn signal_universe() -> Syntax<'db> {
        Syntax::SignalUniverse(SignalUniverse::new())
    }

    pub fn signal_universe_rc() -> RcSyntax<'db> {
        Rc::new(Syntax::signal_universe())
    }

    pub fn bit() -> Syntax<'db> {
        Syntax::Bit(Bit::new())
    }

    pub fn bit_rc() -> RcSyntax<'db> {
        Rc::new(Syntax::bit())
    }

    pub fn zero() -> Syntax<'db> {
        Syntax::Zero(Zero::new())
    }

    pub fn zero_rc() -> RcSyntax<'db> {
        Rc::new(Syntax::zero())
    }

    pub fn one() -> Syntax<'db> {
        Syntax::One(One::new())
    }

    pub fn one_rc() -> RcSyntax<'db> {
        Rc::new(Syntax::one())
    }

    pub fn module_universe() -> Syntax<'db> {
        Syntax::ModuleUniverse(ModuleUniverse::new())
    }

    pub fn module_universe_rc() -> RcSyntax<'db> {
        Rc::new(Syntax::module_universe())
    }

    pub fn harrow(source: RcSyntax<'db>, target: RcSyntax<'db>) -> Syntax<'db> {
        Syntax::HArrow(HArrow::new(source, target))
    }

    pub fn harrow_rc(source: RcSyntax<'db>, target: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::harrow(source, target))
    }

    pub fn module(body: RcSyntax<'db>) -> Syntax<'db> {
        Syntax::Module(Module::new(body))
    }

    pub fn module_rc(body: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::module(body))
    }

    pub fn happlication(
        module: RcSyntax<'db>,
        module_ty: RcSyntax<'db>,
        argument: RcSyntax<'db>,
    ) -> Syntax<'db> {
        Syntax::HApplication(HApplication::new(module, module_ty, argument))
    }

    pub fn happlication_rc(
        module: RcSyntax<'db>,
        module_ty: RcSyntax<'db>,
        argument: RcSyntax<'db>,
    ) -> RcSyntax<'db> {
        Rc::new(Syntax::happlication(module, module_ty, argument))
    }

    pub fn prim(name: ConstantId<'db>) -> Syntax<'db> {
        Syntax::Prim(Prim::new(name))
    }

    pub fn prim_rc(name: ConstantId<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::prim(name))
    }

    pub fn prim_from<T, Db>(db: &'db Db, name: T) -> Syntax<'db>
    where
        T: IntoWithDb<'db, ConstantId<'db>>,
        Db: salsa::Database + ?Sized,
    {
        Syntax::prim(name.into_with_db(db))
    }

    pub fn prim_rc_from<T, Db>(db: &'db Db, name: T) -> Rc<Syntax<'db>>
    where
        T: IntoWithDb<'db, ConstantId<'db>>,
        Db: salsa::Database + ?Sized,
    {
        Syntax::prim_rc(name.into_with_db(db))
    }

    pub fn constant(name: ConstantId<'db>) -> Syntax<'db> {
        Syntax::Constant(Constant::new(name))
    }

    pub fn constant_rc(name: ConstantId<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::constant(name))
    }

    /// Create a constant from a string name, interning it in the database.
    pub fn constant_from<T, Db>(db: &'db Db, name: T) -> Syntax<'db>
    where
        T: IntoWithDb<'db, ConstantId<'db>>,
        Db: salsa::Database + ?Sized,
    {
        Syntax::constant(name.into_with_db(db))
    }

    /// Create a constant from a string name, interning it in the database.
    pub fn constant_rc_from<T, Db>(db: &'db Db, name: T) -> Rc<Syntax<'db>>
    where
        T: IntoWithDb<'db, ConstantId<'db>>,
        Db: salsa::Database + ?Sized,
    {
        Syntax::constant_rc(name.into_with_db(db))
    }

    pub fn variable(index: Index) -> Syntax<'db> {
        Syntax::Variable(Variable::new(index))
    }

    pub fn variable_rc(index: Index) -> RcSyntax<'db> {
        Rc::new(Syntax::variable(index))
    }

    pub fn metavariable(
        metavariable: MetaVariableId,
        substitution: Vec<RcSyntax<'db>>,
    ) -> Syntax<'db> {
        Syntax::Metavariable(Metavariable::new(metavariable, substitution))
    }

    pub fn metavariable_rc(
        metavariable: MetaVariableId,
        substitution: Vec<RcSyntax<'db>>,
    ) -> RcSyntax<'db> {
        Rc::new(Syntax::metavariable(metavariable, substitution))
    }

    pub fn check(ty: RcSyntax<'db>, term: RcSyntax<'db>) -> Syntax<'db> {
        Syntax::Check(Check::new(ty, term))
    }

    pub fn check_rc(ty: RcSyntax<'db>, term: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::check(ty, term))
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone, Copy)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
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

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Lift<'db> {
    pub ty: RcSyntax<'db>,
}

impl<'db> Lift<'db> {
    pub fn new(ty: RcSyntax<'db>) -> Lift<'db> {
        Lift { ty }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Pi<'db> {
    pub source: RcSyntax<'db>,
    pub target: RcSyntax<'db>,
}

impl<'db> Pi<'db> {
    pub fn new(source: RcSyntax<'db>, target: RcSyntax<'db>) -> Pi<'db> {
        Pi { source, target }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Lambda<'db> {
    pub body: RcSyntax<'db>,
}

impl<'db> Lambda<'db> {
    pub fn new(body: RcSyntax<'db>) -> Lambda<'db> {
        Lambda { body }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Application<'db> {
    pub function: RcSyntax<'db>,
    pub argument: RcSyntax<'db>,
}

impl<'db> Application<'db> {
    pub fn new(function: RcSyntax<'db>, argument: RcSyntax<'db>) -> Application<'db> {
        Application { function, argument }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct TypeConstructor<'db> {
    pub constructor: ConstantId<'db>,
    pub arguments: Vec<RcSyntax<'db>>,
}

impl<'db> TypeConstructor<'db> {
    pub fn new(
        constructor: ConstantId<'db>,
        arguments: Vec<RcSyntax<'db>>,
    ) -> TypeConstructor<'db> {
        TypeConstructor {
            constructor,
            arguments,
        }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, RcSyntax<'db>> {
        self.arguments.iter()
    }
}

// Implement IntoIterator for &TypeConstructor to allow iteration by reference
impl<'a, 'db> IntoIterator for &'a TypeConstructor<'db> {
    type Item = &'a RcSyntax<'db>;
    type IntoIter = std::slice::Iter<'a, RcSyntax<'db>>;

    fn into_iter(self) -> Self::IntoIter {
        self.arguments.iter()
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct DataConstructor<'db> {
    /// The constructor constant id
    pub constructor: ConstantId<'db>,
    /// The argument expressions for this constructor application
    pub arguments: Vec<RcSyntax<'db>>,
}

impl<'db> DataConstructor<'db> {
    pub fn new(
        constructor: ConstantId<'db>,
        arguments: Vec<RcSyntax<'db>>,
    ) -> DataConstructor<'db> {
        DataConstructor {
            constructor,
            arguments,
        }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, RcSyntax<'db>> {
        self.arguments.iter()
    }
}

// Implement IntoIterator for &DataConstructor to allow iteration by reference
impl<'a, 'db> IntoIterator for &'a DataConstructor<'db> {
    type Item = &'a RcSyntax<'db>;
    type IntoIter = std::slice::Iter<'a, RcSyntax<'db>>;

    fn into_iter(self) -> Self::IntoIter {
        self.arguments.iter()
    }
}

/// A case tree for pattern matching.
///
/// A case expression contains the variable being matched (scrutinee) and branches
/// that define the pattern matching behavior.
///
/// The scrutinee MUST be a variable (represented as a de Bruijn index). This is
/// essential for dependent pattern matching, where the pattern unifier needs to
/// know exactly which variable it is solving for. If the surface language allows
/// `match f x { ... }`, the elaborator must desugar it to `let y = f x in y case { ... }`.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Case<'db> {
    /// The scrutinee variable (de Bruijn index).
    pub scrutinee: Variable<'db>,
    /// The branches of the case tree
    pub branches: Vec<CaseBranch<'db>>,
}

impl<'db> Case<'db> {
    pub fn new(scrutinee: Variable<'db>, branches: Vec<CaseBranch<'db>>) -> Case<'db> {
        Case {
            scrutinee,
            branches,
        }
    }
}

/// A branch in a case tree.
///
/// Each branch represents a pattern and the corresponding body.
/// The pattern can be a constructor pattern, variable pattern, or wildcard.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct CaseBranch<'db> {
    /// The constructor name
    pub constructor: ConstantId<'db>,
    /// The number of arguments to bind
    pub arity: usize,
    /// The body expression for this branch
    pub body: RcSyntax<'db>,
}

impl<'db> CaseBranch<'db> {
    pub fn new(constructor: ConstantId<'db>, arity: usize, body: RcSyntax<'db>) -> CaseBranch<'db> {
        CaseBranch {
            constructor,
            arity,
            body,
        }
    }
}

/// Propositional equality type: Eq A x y
///
/// Represents the type of proofs that x and y are equal at type A.
/// This is the identity type from Martin-Löf type theory.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct EqType<'db> {
    /// The type at which equality is stated
    pub ty: RcSyntax<'db>,
    /// The left-hand side of the equality
    pub lhs: RcSyntax<'db>,
    /// The right-hand side of the equality
    pub rhs: RcSyntax<'db>,
}

impl<'db> EqType<'db> {
    pub fn new(ty: RcSyntax<'db>, lhs: RcSyntax<'db>, rhs: RcSyntax<'db>) -> EqType<'db> {
        EqType { ty, lhs, rhs }
    }
}

/// Reflexivity proof: refl
///
/// The canonical proof that any term is equal to itself.
/// This is the only constructor of the Eq type.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
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

/// Transport (rewrite) operator: transport motive proof value
///
/// Given:
/// - motive: A type family P : A → Type
/// - proof: A proof that x = y (of type Eq A x y)
/// - value: A value of type P x
///
/// Produces a value of type P y.
///
/// This is Axiom J (the eliminator for equality types).
/// When the proof evaluates to refl, the transport vanishes during evaluation.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Transport<'db> {
    /// The type family (motive): [%0] |- P
    /// Represents a closure with one variable binding
    /// Syntax: transport [%0] |- P proof value
    pub motive: Closure<'db>,
    /// The equality proof: h : Eq A x y
    pub proof: RcSyntax<'db>,
    /// The value to transport: v : P x
    pub value: RcSyntax<'db>,
}

impl<'db> Transport<'db> {
    pub fn new(motive: Closure<'db>, proof: RcSyntax<'db>, value: RcSyntax<'db>) -> Transport<'db> {
        Transport {
            motive,
            proof,
            value,
        }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
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

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct SLift<'db> {
    pub ty: RcSyntax<'db>,
}

impl<'db> SLift<'db> {
    pub fn new(ty: RcSyntax<'db>) -> SLift<'db> {
        SLift { ty }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct MLift<'db> {
    pub ty: RcSyntax<'db>,
}

impl<'db> MLift<'db> {
    pub fn new(ty: RcSyntax<'db>) -> MLift<'db> {
        MLift { ty }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
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

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
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

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
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

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
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

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
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

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct HArrow<'db> {
    pub source: RcSyntax<'db>,
    pub target: RcSyntax<'db>,
}

impl<'db> HArrow<'db> {
    pub fn new(source: RcSyntax<'db>, target: RcSyntax<'db>) -> HArrow<'db> {
        HArrow { source, target }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Module<'db> {
    pub body: RcSyntax<'db>,
}

impl<'db> Module<'db> {
    pub fn new(body: RcSyntax<'db>) -> Module<'db> {
        Module { body }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct HApplication<'db> {
    pub module: RcSyntax<'db>,
    pub module_ty: RcSyntax<'db>,
    pub argument: RcSyntax<'db>,
}

impl<'db> HApplication<'db> {
    pub fn new(
        module: RcSyntax<'db>,
        module_ty: RcSyntax<'db>,
        argument: RcSyntax<'db>,
    ) -> HApplication<'db> {
        HApplication {
            module,
            module_ty,
            argument,
        }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Prim<'db> {
    pub name: ConstantId<'db>,
}

impl<'db> Prim<'db> {
    pub fn new(name: ConstantId<'db>) -> Prim<'db> {
        Prim { name }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Constant<'db> {
    pub name: ConstantId<'db>,
}

impl<'db> Constant<'db> {
    pub fn new(name: ConstantId<'db>) -> Constant<'db> {
        Constant { name }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Variable<'db> {
    pub index: Index,
    _marker: PhantomData<&'db ()>,
}

impl<'db> Variable<'db> {
    pub fn new(index: Index) -> Variable<'db> {
        Variable {
            index,
            _marker: PhantomData,
        }
    }
}

// A reference to a metavariable with its substitution.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Metavariable<'db> {
    pub id: MetaVariableId,
    /// The substitution for the metavariable's context.
    pub substitution: Vec<RcSyntax<'db>>,
}

impl<'db> Metavariable<'db> {
    pub fn new(id: MetaVariableId, substitution: Vec<RcSyntax<'db>>) -> Metavariable<'db> {
        Metavariable { id, substitution }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, RcSyntax<'db>> {
        self.substitution.iter()
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Check<'db> {
    pub ty: RcSyntax<'db>,
    pub term: RcSyntax<'db>,
}

impl<'db> Check<'db> {
    pub fn new(ty: RcSyntax<'db>, term: RcSyntax<'db>) -> Check<'db> {
        Check { ty, term }
    }
}
