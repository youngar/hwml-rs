use crate::*;
use hwml_support::*;
use std::{marker::PhantomData, rc::Rc};

pub type RcSyntax<'db> = Rc<Syntax<'db>>;
pub type BindingSyntax<'db> = Binding<RcSyntax<'db>>;
pub type DynBindingSyntax<'db> = DynBinding<RcSyntax<'db>>;

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub enum Syntax<'db> {
    // ========== Type codes (types as first-class terms) ==========
    /// Type code: The universe of types at level `n`
    /// This is a TERM that evaluates to a type code value
    UniverseCode(usize),

    /// Type code: Dependent function type (source, target)
    /// This is a TERM that evaluates to a type code value
    PiCode(RcSyntax<'db>, BindingSyntax<'db>),

    /// Type code: Universe lifting for cumulativity
    /// LiftCode(n, inner) shifts a type code up by n universe levels
    /// Example: LiftCode(1, UniverseCode(0)) represents U_0 lifted to U_1
    /// This enables modular compilation where definitions compiled at lower
    /// universe levels can be reused at higher levels without recompilation.
    LiftCode(usize, RcSyntax<'db>),

    /// Type code: The Bit type (hardware primitive)
    BitCode,

    // ========== Equality types ==========
    Eq(EqType<'db>),
    Refl(Refl<'db>),
    Transport(Transport<'db>),

    // ========== Terms ==========
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

    Let(Let<'db>),
    Check(Check<'db>),
}

impl<'db> Syntax<'db> {
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
        motive: RcSyntax<'db>,
        proof: RcSyntax<'db>,
        value: RcSyntax<'db>,
    ) -> Syntax<'db> {
        Syntax::Transport(Transport::new(motive, proof, value))
    }

    pub fn transport_rc(
        motive: RcSyntax<'db>,
        proof: RcSyntax<'db>,
        value: RcSyntax<'db>,
    ) -> RcSyntax<'db> {
        Rc::new(Syntax::transport(motive, proof, value))
    }

    pub fn lambda(body: BindingSyntax<'db>) -> Syntax<'db> {
        Syntax::Lambda(Lambda::new(body))
    }

    pub fn lambda_rc(body: BindingSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::lambda(body))
    }

    pub fn application(fun: RcSyntax<'db>, arg: RcSyntax<'db>) -> Syntax<'db> {
        Syntax::Application(Application::new(fun, arg))
    }

    pub fn application_rc(fun: RcSyntax<'db>, arg: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::application(fun, arg))
    }

    pub fn type_constructor(
        name: QualifiedName<'db>,
        arguments: Vec<RcSyntax<'db>>,
    ) -> Syntax<'db> {
        Syntax::TypeConstructor(TypeConstructor::new(name, arguments))
    }

    pub fn type_constructor_rc(
        name: QualifiedName<'db>,
        arguments: Vec<RcSyntax<'db>>,
    ) -> RcSyntax<'db> {
        Rc::new(Syntax::type_constructor(name, arguments))
    }

    pub fn data_constructor(
        constructor: QualifiedName<'db>,
        arguments: Vec<RcSyntax<'db>>,
    ) -> Syntax<'db> {
        Syntax::DataConstructor(DataConstructor::new(constructor, arguments))
    }

    pub fn data_constructor_rc(
        constructor: QualifiedName<'db>,
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

    pub fn module(body: BindingSyntax<'db>) -> Syntax<'db> {
        Syntax::Module(Module::new(body))
    }

    pub fn module_rc(body: BindingSyntax<'db>) -> RcSyntax<'db> {
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

    pub fn prim(name: QualifiedName<'db>) -> Syntax<'db> {
        Syntax::Prim(Prim::new(name))
    }

    pub fn prim_rc(name: QualifiedName<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::prim(name))
    }

    pub fn prim_from<T, Db>(db: &'db Db, name: T) -> Syntax<'db>
    where
        T: IntoWithDb<'db, QualifiedName<'db>>,
        Db: ::salsa::Database + ?Sized,
    {
        Syntax::prim(name.into_with_db(db))
    }

    pub fn prim_rc_from<T, Db>(db: &'db Db, name: T) -> RcSyntax<'db>
    where
        T: IntoWithDb<'db, QualifiedName<'db>>,
        Db: ::salsa::Database + ?Sized,
    {
        Syntax::prim_rc(name.into_with_db(db))
    }

    pub fn constant(name: QualifiedName<'db>) -> Syntax<'db> {
        Syntax::Constant(Constant::new(name))
    }

    pub fn constant_rc(name: QualifiedName<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::constant(name))
    }

    pub fn constant_from<T, Db>(db: &'db Db, name: T) -> Syntax<'db>
    where
        T: IntoWithDb<'db, QualifiedName<'db>>,
        Db: ::salsa::Database + ?Sized,
    {
        Syntax::constant(name.into_with_db(db))
    }

    pub fn constant_rc_from<T, Db>(db: &'db Db, name: T) -> RcSyntax<'db>
    where
        T: IntoWithDb<'db, QualifiedName<'db>>,
        Db: ::salsa::Database + ?Sized,
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

    pub fn let_expr(
        ty: RcSyntax<'db>,
        value: RcSyntax<'db>,
        body: BindingSyntax<'db>,
    ) -> Syntax<'db> {
        Syntax::Let(Let::new(ty, value, body))
    }

    pub fn let_rc(
        ty: RcSyntax<'db>,
        value: RcSyntax<'db>,
        body: BindingSyntax<'db>,
    ) -> RcSyntax<'db> {
        Rc::new(Syntax::let_expr(ty, value, body))
    }

    pub fn check(ty: RcSyntax<'db>, term: RcSyntax<'db>) -> Syntax<'db> {
        Syntax::Check(Check::new(ty, term))
    }

    pub fn check_rc(ty: RcSyntax<'db>, term: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::check(ty, term))
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct EqType<'db> {
    pub ty: RcSyntax<'db>,
    pub lhs: RcSyntax<'db>,
    pub rhs: RcSyntax<'db>,
}

impl<'db> EqType<'db> {
    pub fn new(ty: RcSyntax<'db>, lhs: RcSyntax<'db>, rhs: RcSyntax<'db>) -> EqType<'db> {
        EqType { ty, lhs, rhs }
    }
}

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

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Transport<'db> {
    pub motive: RcSyntax<'db>,
    pub proof: RcSyntax<'db>,
    pub value: RcSyntax<'db>,
}

impl<'db> Transport<'db> {
    pub fn new(
        motive: RcSyntax<'db>,
        proof: RcSyntax<'db>,
        value: RcSyntax<'db>,
    ) -> Transport<'db> {
        Transport {
            motive,
            proof,
            value,
        }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Lambda<'db> {
    pub body: BindingSyntax<'db>,
}

impl<'db> Lambda<'db> {
    pub fn new(body: BindingSyntax<'db>) -> Lambda<'db> {
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
    pub constructor: QualifiedName<'db>,
    pub arguments: Vec<RcSyntax<'db>>,
}

impl<'db> TypeConstructor<'db> {
    pub fn new(
        constructor: QualifiedName<'db>,
        arguments: Vec<RcSyntax<'db>>,
    ) -> TypeConstructor<'db> {
        TypeConstructor {
            constructor,
            arguments,
        }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct DataConstructor<'db> {
    pub constructor: QualifiedName<'db>,
    pub arguments: Vec<RcSyntax<'db>>,
}

impl<'db> DataConstructor<'db> {
    pub fn new(
        constructor: QualifiedName<'db>,
        arguments: Vec<RcSyntax<'db>>,
    ) -> DataConstructor<'db> {
        DataConstructor {
            constructor,
            arguments,
        }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Case<'db> {
    pub scrutinee: Variable<'db>,
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

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct CaseBranch<'db> {
    pub constructor: QualifiedName<'db>,
    pub body: DynBindingSyntax<'db>,
}

impl<'db> CaseBranch<'db> {
    pub fn new(constructor: QualifiedName<'db>, body: DynBindingSyntax<'db>) -> CaseBranch<'db> {
        CaseBranch { constructor, body }
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
    pub body: BindingSyntax<'db>,
}

impl<'db> Module<'db> {
    pub fn new(body: BindingSyntax<'db>) -> Module<'db> {
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
    pub name: QualifiedName<'db>,
}

impl<'db> Prim<'db> {
    pub fn new(name: QualifiedName<'db>) -> Prim<'db> {
        Prim { name }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
pub struct Constant<'db> {
    pub name: QualifiedName<'db>,
}

impl<'db> Constant<'db> {
    pub fn new(name: QualifiedName<'db>) -> Constant<'db> {
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
pub struct Let<'db> {
    pub ty: RcSyntax<'db>,
    pub value: RcSyntax<'db>,
    pub body: BindingSyntax<'db>,
}

impl<'db> Let<'db> {
    pub fn new(ty: RcSyntax<'db>, value: RcSyntax<'db>, body: BindingSyntax<'db>) -> Let<'db> {
        Let { ty, value, body }
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
