use crate::common::{Index, Location, MetaVariableId, UniverseLevel};
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

/// The outer wrapper that carries the provenance for error reporting.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Syntax<'db> {
    pub loc: Location,
    pub data: SyntaxData<'db>,
}

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

/// The purely mathematical variants of the Core IR.
/// This enum contains the structure of terms, with no location metadata.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub enum SyntaxData<'db> {
    Universe(Universe<'db>),
    Lift(Lift<'db>),

    Pi(Pi<'db>),
    Lambda(Lambda<'db>),
    Application(Application<'db>),
    Let(Let<'db>),

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
    // Universe constructors
    pub fn universe(loc: Location, level: UniverseLevel) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::Universe(Universe::new(level)),
        }
    }

    pub fn universe_rc(loc: Location, level: UniverseLevel) -> RcSyntax<'db> {
        Rc::new(Syntax::universe(loc, level))
    }

    // Lift constructors
    pub fn lift(loc: Location, ty: RcSyntax<'db>) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::Lift(Lift::new(ty)),
        }
    }

    pub fn lift_rc(loc: Location, ty: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::lift(loc, ty))
    }

    // Pi constructors
    pub fn pi(loc: Location, source: RcSyntax<'db>, target: RcSyntax<'db>) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::Pi(Pi::new(source, target)),
        }
    }

    pub fn pi_rc(loc: Location, source: RcSyntax<'db>, target: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::pi(loc, source, target))
    }

    // Lambda constructors
    pub fn lambda(loc: Location, body: RcSyntax<'db>) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::Lambda(Lambda::new(body)),
        }
    }

    pub fn lambda_rc(loc: Location, body: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::lambda(loc, body))
    }

    // Application constructors
    pub fn application(loc: Location, fun: RcSyntax<'db>, arg: RcSyntax<'db>) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::Application(Application::new(fun, arg)),
        }
    }

    pub fn application_rc(loc: Location, fun: RcSyntax<'db>, arg: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::application(loc, fun, arg))
    }

    // Let constructors
    pub fn let_expr(
        loc: Location,
        ty: RcSyntax<'db>,
        value: RcSyntax<'db>,
        body: RcSyntax<'db>,
    ) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::Let(Let::new(ty, value, body)),
        }
    }

    pub fn let_rc(
        loc: Location,
        ty: RcSyntax<'db>,
        value: RcSyntax<'db>,
        body: RcSyntax<'db>,
    ) -> RcSyntax<'db> {
        Rc::new(Syntax::let_expr(loc, ty, value, body))
    }

    // TypeConstructor constructors
    pub fn type_constructor(
        loc: Location,
        name: ConstantId<'db>,
        arguments: Vec<RcSyntax<'db>>,
    ) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::TypeConstructor(TypeConstructor::new(name, arguments)),
        }
    }

    pub fn type_constructor_rc(
        loc: Location,
        name: ConstantId<'db>,
        arguments: Vec<RcSyntax<'db>>,
    ) -> RcSyntax<'db> {
        Rc::new(Syntax::type_constructor(loc, name, arguments))
    }

    // DataConstructor constructors
    pub fn data_constructor(
        loc: Location,
        constructor: ConstantId<'db>,
        arguments: Vec<RcSyntax<'db>>,
    ) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::DataConstructor(DataConstructor::new(constructor, arguments)),
        }
    }

    pub fn data_constructor_rc(
        loc: Location,
        constructor: ConstantId<'db>,
        arguments: Vec<RcSyntax<'db>>,
    ) -> RcSyntax<'db> {
        Rc::new(Syntax::data_constructor(loc, constructor, arguments))
    }

    // Case constructors
    pub fn case(loc: Location, scrutinee: Index, branches: Vec<CaseBranch<'db>>) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::Case(Case::new(Variable::new(scrutinee), branches)),
        }
    }

    pub fn case_rc(
        loc: Location,
        scrutinee: Index,
        branches: Vec<CaseBranch<'db>>,
    ) -> RcSyntax<'db> {
        Rc::new(Syntax::case(loc, scrutinee, branches))
    }

    // Eq constructors
    pub fn eq(
        loc: Location,
        ty: RcSyntax<'db>,
        lhs: RcSyntax<'db>,
        rhs: RcSyntax<'db>,
    ) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::Eq(EqType::new(ty, lhs, rhs)),
        }
    }

    pub fn eq_rc(
        loc: Location,
        ty: RcSyntax<'db>,
        lhs: RcSyntax<'db>,
        rhs: RcSyntax<'db>,
    ) -> RcSyntax<'db> {
        Rc::new(Syntax::eq(loc, ty, lhs, rhs))
    }

    // Refl constructors
    pub fn refl(loc: Location) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::Refl(Refl::new()),
        }
    }

    pub fn refl_rc(loc: Location) -> RcSyntax<'db> {
        Rc::new(Syntax::refl(loc))
    }

    // Transport constructors
    pub fn transport(
        loc: Location,
        motive: Closure<'db>,
        proof: RcSyntax<'db>,
        value: RcSyntax<'db>,
    ) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::Transport(Transport::new(motive, proof, value)),
        }
    }

    pub fn transport_rc(
        loc: Location,
        motive: Closure<'db>,
        proof: RcSyntax<'db>,
        value: RcSyntax<'db>,
    ) -> RcSyntax<'db> {
        Rc::new(Syntax::transport(loc, motive, proof, value))
    }

    // Closure constructors
    pub fn closure(loc: Location, body: RcSyntax<'db>) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::Closure(Closure::new(body)),
        }
    }

    pub fn closure_rc(loc: Location, body: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::closure(loc, body))
    }

    // HardwareUniverse constructors
    pub fn hardware(loc: Location) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::HardwareUniverse(HardwareUniverse::new()),
        }
    }

    pub fn hardware_rc(loc: Location) -> RcSyntax<'db> {
        Rc::new(Syntax::hardware(loc))
    }

    // SLift constructors
    pub fn slift(loc: Location, ty: RcSyntax<'db>) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::SLift(SLift::new(ty)),
        }
    }

    pub fn slift_rc(loc: Location, ty: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::slift(loc, ty))
    }

    // MLift constructors
    pub fn mlift(loc: Location, ty: RcSyntax<'db>) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::MLift(MLift::new(ty)),
        }
    }

    pub fn mlift_rc(loc: Location, ty: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::mlift(loc, ty))
    }

    // SignalUniverse constructors
    pub fn signal_universe(loc: Location) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::SignalUniverse(SignalUniverse::new()),
        }
    }

    pub fn signal_universe_rc(loc: Location) -> RcSyntax<'db> {
        Rc::new(Syntax::signal_universe(loc))
    }

    // Bit constructors
    pub fn bit(loc: Location) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::Bit(Bit::new()),
        }
    }

    pub fn bit_rc(loc: Location) -> RcSyntax<'db> {
        Rc::new(Syntax::bit(loc))
    }

    // Zero constructors
    pub fn zero(loc: Location) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::Zero(Zero::new()),
        }
    }

    pub fn zero_rc(loc: Location) -> RcSyntax<'db> {
        Rc::new(Syntax::zero(loc))
    }

    // One constructors
    pub fn one(loc: Location) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::One(One::new()),
        }
    }

    pub fn one_rc(loc: Location) -> RcSyntax<'db> {
        Rc::new(Syntax::one(loc))
    }

    // ModuleUniverse constructors
    pub fn module_universe(loc: Location) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::ModuleUniverse(ModuleUniverse::new()),
        }
    }

    pub fn module_universe_rc(loc: Location) -> RcSyntax<'db> {
        Rc::new(Syntax::module_universe(loc))
    }

    // HArrow constructors
    pub fn harrow(loc: Location, source: RcSyntax<'db>, target: RcSyntax<'db>) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::HArrow(HArrow::new(source, target)),
        }
    }

    pub fn harrow_rc(loc: Location, source: RcSyntax<'db>, target: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::harrow(loc, source, target))
    }

    // Module constructors
    pub fn module(loc: Location, body: RcSyntax<'db>) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::Module(Module::new(body)),
        }
    }

    pub fn module_rc(loc: Location, body: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::module(loc, body))
    }

    // HApplication constructors
    pub fn happlication(
        loc: Location,
        module: RcSyntax<'db>,
        module_ty: RcSyntax<'db>,
        argument: RcSyntax<'db>,
    ) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::HApplication(HApplication::new(module, module_ty, argument)),
        }
    }

    pub fn happlication_rc(
        loc: Location,
        module: RcSyntax<'db>,
        module_ty: RcSyntax<'db>,
        argument: RcSyntax<'db>,
    ) -> RcSyntax<'db> {
        Rc::new(Syntax::happlication(loc, module, module_ty, argument))
    }

    // Prim constructors
    pub fn prim(loc: Location, name: ConstantId<'db>) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::Prim(Prim::new(name)),
        }
    }

    pub fn prim_rc(loc: Location, name: ConstantId<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::prim(loc, name))
    }

    pub fn prim_from<T, Db>(loc: Location, db: &'db Db, name: T) -> Syntax<'db>
    where
        T: IntoWithDb<'db, ConstantId<'db>>,
        Db: salsa::Database + ?Sized,
    {
        Syntax::prim(loc, name.into_with_db(db))
    }

    pub fn prim_rc_from<T, Db>(loc: Location, db: &'db Db, name: T) -> Rc<Syntax<'db>>
    where
        T: IntoWithDb<'db, ConstantId<'db>>,
        Db: salsa::Database + ?Sized,
    {
        Syntax::prim_rc(loc, name.into_with_db(db))
    }

    // Constant constructors
    pub fn constant(loc: Location, name: ConstantId<'db>) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::Constant(Constant::new(name)),
        }
    }

    pub fn constant_rc(loc: Location, name: ConstantId<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::constant(loc, name))
    }

    /// Create a constant from a string name, interning it in the database.
    pub fn constant_from<T, Db>(loc: Location, db: &'db Db, name: T) -> Syntax<'db>
    where
        T: IntoWithDb<'db, ConstantId<'db>>,
        Db: salsa::Database + ?Sized,
    {
        Syntax::constant(loc, name.into_with_db(db))
    }

    /// Create a constant from a string name, interning it in the database.
    pub fn constant_rc_from<T, Db>(loc: Location, db: &'db Db, name: T) -> Rc<Syntax<'db>>
    where
        T: IntoWithDb<'db, ConstantId<'db>>,
        Db: salsa::Database + ?Sized,
    {
        Syntax::constant_rc(loc, name.into_with_db(db))
    }

    // Variable constructors
    pub fn variable(loc: Location, index: Index) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::Variable(Variable::new(index)),
        }
    }

    pub fn variable_rc(loc: Location, index: Index) -> RcSyntax<'db> {
        Rc::new(Syntax::variable(loc, index))
    }

    // Metavariable constructors
    pub fn metavariable(
        loc: Location,
        metavariable: MetaVariableId,
        substitution: Vec<RcSyntax<'db>>,
    ) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::Metavariable(Metavariable::new(metavariable, substitution)),
        }
    }

    pub fn metavariable_rc(
        loc: Location,
        metavariable: MetaVariableId,
        substitution: Vec<RcSyntax<'db>>,
    ) -> RcSyntax<'db> {
        Rc::new(Syntax::metavariable(loc, metavariable, substitution))
    }

    // Check constructors
    pub fn check(loc: Location, ty: RcSyntax<'db>, term: RcSyntax<'db>) -> Syntax<'db> {
        Syntax {
            loc,
            data: SyntaxData::Check(Check::new(ty, term)),
        }
    }

    pub fn check_rc(loc: Location, ty: RcSyntax<'db>, term: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::check(loc, ty, term))
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
pub struct Let<'db> {
    pub ty: RcSyntax<'db>,
    pub value: RcSyntax<'db>,
    pub body: RcSyntax<'db>,
}

impl<'db> Let<'db> {
    pub fn new(ty: RcSyntax<'db>, value: RcSyntax<'db>, body: RcSyntax<'db>) -> Let<'db> {
        Let { ty, value, body }
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
