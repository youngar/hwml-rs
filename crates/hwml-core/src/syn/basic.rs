use crate::common::{Index, MetaVariableId, UniverseLevel};
use crate::symbol::InternedString;
use hwml_support::{FromWithDb, IntoWithDb, LineInfo};
use salsa::Database;
use std::{fmt, marker::PhantomData, rc::Rc};

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone, Copy)]
pub struct ConstantId<'db>(pub InternedString<'db>);

impl<'db> ConstantId<'db> {
    /// Create a new ConstantId from an interned string.
    pub fn new(interned: InternedString<'db>) -> Self {
        ConstantId(interned)
    }

    /// Get the interned string for this constant.
    pub fn interned(&self) -> InternedString<'db> {
        self.0
    }

    /// Get the string name for this constant.
    pub fn name(&self, db: &'db dyn Database) -> &str {
        self.0.text(db)
    }
}

impl<'db, T> FromWithDb<'db, T> for ConstantId<'db>
where
    T: IntoWithDb<'db, InternedString<'db>>,
{
    fn from_with_db<Db>(db: &'db Db, value: T) -> Self
    where
        Db: salsa::Database + ?Sized,
    {
        ConstantId::new(value.into_with_db(db))
    }
}

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

/// A captured environment.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Closure<'db> {
    /// The environment contains a vector of definitions.
    pub values: Vec<RcSyntax<'db>>,
}

impl<'db> Closure<'db> {
    pub fn new() -> Closure<'db> {
        Closure { values: Vec::new() }
    }

    pub fn with_values(values: Vec<RcSyntax<'db>>) -> Closure<'db> {
        Closure { values }
    }

    pub fn pop(&mut self) {
        self.values.pop();
    }

    pub fn truncate(&mut self, depth: usize) {
        self.values.truncate(depth);
    }

    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
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

    pub fn case(
        expr: RcSyntax<'db>,
        motive: RcSyntax<'db>,
        branches: Vec<CaseBranch<'db>>,
    ) -> Syntax<'db> {
        Syntax::Case(Case::new(expr, motive, branches))
    }

    pub fn case_rc(
        expr: RcSyntax<'db>,
        motive: RcSyntax<'db>,
        branches: Vec<CaseBranch<'db>>,
    ) -> RcSyntax<'db> {
        Rc::new(Syntax::case(expr, motive, branches))
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

    pub fn happlication(function: RcSyntax<'db>, argument: RcSyntax<'db>) -> Syntax<'db> {
        Syntax::HApplication(HApplication::new(function, argument))
    }

    pub fn happlication_rc(function: RcSyntax<'db>, argument: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::happlication(function, argument))
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
/// A case expression contains both the expression being matched (scrutinee) and the branches
/// that define the pattern matching behavior.
///
/// Type annotations should be provided using the Check syntax node to wrap the case expression.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Case<'db> {
    /// The expression being matched on (scrutinee)
    pub expr: RcSyntax<'db>,
    /// An expression which computes the resulting type of the case expression.
    pub motive: RcSyntax<'db>,
    /// The branches of the case tree
    pub branches: Vec<CaseBranch<'db>>,
}

impl<'db> Case<'db> {
    pub fn new(
        expr: RcSyntax<'db>,
        motive: RcSyntax<'db>,
        branches: Vec<CaseBranch<'db>>,
    ) -> Case<'db> {
        Case {
            expr,
            motive,
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
    pub function: RcSyntax<'db>,
    pub argument: RcSyntax<'db>,
}

impl<'db> HApplication<'db> {
    pub fn new(function: RcSyntax<'db>, argument: RcSyntax<'db>) -> HApplication<'db> {
        HApplication { function, argument }
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
