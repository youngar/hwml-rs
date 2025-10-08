use crate::common::{Index, Level, UniverseLevel};
use crate::symbol::InternedString;
use salsa::Database;
use std::rc::Rc;

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone, Copy)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct ConstantId<'db>(pub InternedString<'db>);

impl<'db> ConstantId<'db> {
    /// Create a new ConstantId from an interned string.
    pub fn new(interned: InternedString<'db>) -> Self {
        ConstantId(interned)
    }

    /// Create a new ConstantId from a string, interning it in the database.
    pub fn from_str(db: &'db dyn Database, name: &str) -> Self {
        ConstantId(InternedString::new(db, name.to_string()))
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

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone, Copy)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct MetavariableId(pub usize);

impl std::fmt::Display for MetavariableId {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "?{}", self.0)
    }
}

pub type RcSyntax<'db> = Rc<Syntax<'db>>;

pub type Tm<'db> = Syntax<'db>;
pub type Ty<'db> = Syntax<'db>;

/// A captured environment.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
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
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum Syntax<'db> {
    Constant(Constant<'db>),
    Variable(Variable),
    Check(Check<'db>),
    Pi(Pi<'db>),
    Lambda(Lambda<'db>),
    Application(Application<'db>),
    Universe(Universe),
    Metavariable(Metavariable<'db>),
    Lift(Lift<'db>),
    Quote(Quote<'db>),
    HArrow(HArrow<'db>),
}

impl<'db> Syntax<'db> {
    pub fn constant(name: ConstantId<'db>) -> Syntax<'db> {
        Syntax::Constant(Constant::new(name))
    }

    pub fn constant_rc(name: ConstantId<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::constant(name))
    }

    /// Create a constant from a string name, interning it in the database.
    pub fn constant_from_str(db: &'db dyn Database, name: &str) -> Syntax<'db> {
        Syntax::constant(ConstantId::from_str(db, name))
    }

    /// Create a constant RC from a string name, interning it in the database.
    pub fn constant_from_str_rc(db: &'db dyn Database, name: &str) -> RcSyntax<'db> {
        Rc::new(Syntax::constant_from_str(db, name))
    }

    pub fn variable(index: Index) -> Syntax<'db> {
        Syntax::Variable(Variable::new(index))
    }

    pub fn variable_rc(index: Index) -> RcSyntax<'db> {
        Rc::new(Syntax::variable(index))
    }

    pub fn check(ty: RcSyntax<'db>, term: RcSyntax<'db>) -> Syntax<'db> {
        Syntax::Check(Check::new(ty, term))
    }

    pub fn check_rc(ty: RcSyntax<'db>, term: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::check(ty, term))
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

    pub fn universe(level: UniverseLevel) -> Syntax<'db> {
        Syntax::Universe(Universe::new(level))
    }

    pub fn universe_rc(level: UniverseLevel) -> RcSyntax<'db> {
        Rc::new(Syntax::universe(level))
    }

    // Create a metavariable syntax node with a reference to an existing metavariable.
    pub fn metavariable(metavariable: MetavariableId, closure: Closure<'db>) -> Syntax<'db> {
        Syntax::Metavariable(Metavariable::new(metavariable, closure))
    }

    pub fn metavariable_rc(metavariable: MetavariableId, closure: Closure<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::metavariable(metavariable, closure))
    }

    pub fn lift(tm: RcSyntax<'db>) -> Syntax<'db> {
        Syntax::Lift(Lift::new(tm))
    }

    pub fn lift_rc(tm: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::lift(tm))
    }

    pub fn quote(tm: RcHSyntax<'db>) -> Syntax<'db> {
        Syntax::Quote(Quote::new(tm))
    }

    pub fn quote_rc(tm: RcHSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::quote(tm))
    }

    pub fn harrow(source: RcSyntax<'db>, target: RcSyntax<'db>) -> Syntax<'db> {
        Syntax::HArrow(HArrow::new(source, target))
    }

    pub fn harrow_rc(source: RcSyntax<'db>, target: RcSyntax<'db>) -> RcSyntax<'db> {
        Rc::new(Syntax::harrow(source, target))
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
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
pub struct Variable {
    pub index: Index,
}

impl Variable {
    pub fn new(index: Index) -> Variable {
        Variable { index }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Check<'db> {
    pub ty: RcSyntax<'db>,
    pub term: RcSyntax<'db>,
}

impl<'db> Check<'db> {
    pub fn new(ty: RcSyntax<'db>, term: RcSyntax<'db>) -> Check<'db> {
        Check { ty, term }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
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
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Lambda<'db> {
    pub body: RcSyntax<'db>,
}

impl<'db> Lambda<'db> {
    pub fn new(body: RcSyntax<'db>) -> Lambda<'db> {
        Lambda { body }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Application<'db> {
    pub function: RcSyntax<'db>,
    pub argument: RcSyntax<'db>,
}

impl<'db> Application<'db> {
    pub fn new(function: RcSyntax<'db>, argument: RcSyntax<'db>) -> Application<'db> {
        Application { function, argument }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone, Copy)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Universe {
    pub level: UniverseLevel,
}

impl Universe {
    pub fn new(level: UniverseLevel) -> Universe {
        Universe { level }
    }
}

// A reference to a metavariable. All metavariables have identity equality.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Metavariable<'db> {
    pub id: MetavariableId,
    pub closure: Closure<'db>,
}

impl<'db> Metavariable<'db> {
    pub fn new(id: MetavariableId, closure: Closure<'db>) -> Metavariable<'db> {
        Metavariable { id, closure }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Lift<'db> {
    pub tm: RcSyntax<'db>,
}

impl<'db> Lift<'db> {
    pub fn new(tm: RcSyntax<'db>) -> Lift<'db> {
        Lift { tm }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Quote<'db> {
    pub tm: RcHSyntax<'db>,
}

impl<'db> Quote<'db> {
    pub fn new(tm: RcHSyntax<'db>) -> Quote<'db> {
        Quote { tm }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct HArrow<'db> {
    pub source: RcSyntax<'db>,
    pub target: RcSyntax<'db>,
}

impl<'db> HArrow<'db> {
    pub fn new(source: RcSyntax<'db>, target: RcSyntax<'db>) -> HArrow<'db> {
        HArrow { source, target }
    }
}

pub type RcHSyntax<'db> = Rc<HSyntax<'db>>;

pub type HTm<'db> = HSyntax<'db>;
pub type HTy<'db> = HSyntax<'db>;

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum HSyntax<'db> {
    HConstant(Constant<'db>),
    HVariable(Variable),
    HCheck(HCheck<'db>),
    HLambda(HLambda<'db>),
    HApplication(HApplication<'db>),
    Splice(Splice<'db>),
}

impl<'db> HSyntax<'db> {
    pub fn hconstant(name: ConstantId<'db>) -> HSyntax<'db> {
        HSyntax::HConstant(Constant::new(name))
    }

    pub fn hconstant_rc(name: ConstantId<'db>) -> RcHSyntax<'db> {
        Rc::new(HSyntax::hconstant(name))
    }

    /// Create an hconstant from a string name, interning it in the database.
    pub fn hconstant_from_str(db: &'db dyn Database, name: &str) -> HSyntax<'db> {
        HSyntax::hconstant(ConstantId::from_str(db, name))
    }

    /// Create an hconstant RC from a string name, interning it in the database.
    pub fn hconstant_from_str_rc(db: &'db dyn Database, name: &str) -> RcHSyntax<'db> {
        Rc::new(HSyntax::hconstant_from_str(db, name))
    }

    pub fn hvariable(index: Index) -> HSyntax<'db> {
        HSyntax::HVariable(Variable::new(index))
    }

    pub fn hvariable_rc(index: Index) -> RcHSyntax<'db> {
        Rc::new(HSyntax::hvariable(index))
    }

    pub fn hcheck(ty: RcHSyntax<'db>, term: RcHSyntax<'db>) -> HSyntax<'db> {
        HSyntax::HCheck(HCheck::new(ty, term))
    }

    pub fn hcheck_rc(ty: RcHSyntax<'db>, term: RcHSyntax<'db>) -> RcHSyntax<'db> {
        Rc::new(HSyntax::hcheck(ty, term))
    }

    pub fn hlambda(body: RcHSyntax<'db>) -> HSyntax<'db> {
        HSyntax::HLambda(HLambda::new(body))
    }

    pub fn hlambda_rc(body: RcHSyntax<'db>) -> RcHSyntax<'db> {
        Rc::new(HSyntax::hlambda(body))
    }

    pub fn happlication(function: RcHSyntax<'db>, argument: RcHSyntax<'db>) -> HSyntax<'db> {
        HSyntax::HApplication(HApplication::new(function, argument))
    }

    pub fn happlication_rc(function: RcHSyntax<'db>, argument: RcHSyntax<'db>) -> RcHSyntax<'db> {
        Rc::new(HSyntax::happlication(function, argument))
    }

    pub fn splice(term: RcSyntax<'db>) -> HSyntax<'db> {
        HSyntax::Splice(Splice::new(term))
    }

    pub fn splice_rc(term: RcSyntax<'db>) -> RcHSyntax<'db> {
        Rc::new(HSyntax::splice(term))
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct HCheck<'db> {
    pub ty: RcHSyntax<'db>,
    pub term: RcHSyntax<'db>,
}

impl<'db> HCheck<'db> {
    pub fn new(ty: RcHSyntax<'db>, term: RcHSyntax<'db>) -> HCheck<'db> {
        HCheck { ty, term }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct HLambda<'db> {
    pub body: RcHSyntax<'db>,
}

impl<'db> HLambda<'db> {
    pub fn new(body: RcHSyntax<'db>) -> HLambda<'db> {
        HLambda { body }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct HApplication<'db> {
    pub function: RcHSyntax<'db>,
    pub argument: RcHSyntax<'db>,
}

impl<'db> HApplication<'db> {
    pub fn new(function: RcHSyntax<'db>, argument: RcHSyntax<'db>) -> HApplication<'db> {
        HApplication { function, argument }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Splice<'db> {
    pub term: RcSyntax<'db>,
}

impl<'db> Splice<'db> {
    pub fn new(term: RcSyntax<'db>) -> Splice<'db> {
        Splice { term }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{Index, UniverseLevel};

    #[test]
    fn test_name_id_equality() {
        use crate::Database;
        let db = Database::default();
        let name1 = ConstantId::from_str(&db, "42");
        let name2 = ConstantId::from_str(&db, "42");
        let name3 = ConstantId::from_str(&db, "99");

        assert_eq!(name1, name2);
        assert_ne!(name1, name3);
    }

    #[test]
    fn test_constant_equality() {
        use crate::Database;
        let db = Database::default();
        let const1 = Constant::new(ConstantId::from_str(&db, "42"));
        let const2 = Constant::new(ConstantId::from_str(&db, "42"));
        let const3 = Constant::new(ConstantId::from_str(&db, "99"));

        assert_eq!(const1, const2);
        assert_ne!(const1, const3);
    }

    #[test]
    fn test_variable_equality() {
        let var1 = Variable::new(Index(0));
        let var2 = Variable::new(Index(0));
        let var3 = Variable::new(Index(1));

        assert_eq!(var1, var2);
        assert_ne!(var1, var3);
    }

    #[test]
    fn test_universe_equality() {
        let uni1 = Universe::new(UniverseLevel::new(0));
        let uni2 = Universe::new(UniverseLevel::new(0));
        let uni3 = Universe::new(UniverseLevel::new(1));

        assert_eq!(uni1, uni2);
        assert_ne!(uni1, uni3);
    }

    #[test]
    fn test_closure_equality() {
        let closure1 = Closure::new();
        let closure2 = Closure::new();
        assert_eq!(closure1, closure2);

        use crate::Database;
        let db = Database::default();
        let val1 = Syntax::constant_rc(ConstantId::from_str(&db, "42"));
        let val2 = Syntax::constant_rc(ConstantId::from_str(&db, "42"));
        let val3 = Syntax::constant_rc(ConstantId::from_str(&db, "99"));

        let closure3 = Closure::with_values(vec![val1.clone()]);
        let closure4 = Closure::with_values(vec![val2.clone()]);
        let closure5 = Closure::with_values(vec![val3.clone()]);

        assert_eq!(closure3, closure4);
        assert_ne!(closure3, closure5);
    }

    #[test]
    fn test_lambda_equality() {
        let body1 = Syntax::variable_rc(Index(0));
        let body2 = Syntax::variable_rc(Index(0));
        let body3 = Syntax::variable_rc(Index(1));

        let lambda1 = Lambda::new(body1);
        let lambda2 = Lambda::new(body2);
        let lambda3 = Lambda::new(body3);

        assert_eq!(lambda1, lambda2);
        assert_ne!(lambda1, lambda3);
    }

    #[test]
    fn test_application_equality() {
        use crate::Database;
        let db = Database::default();
        let fun1 = Syntax::constant_rc(ConstantId::from_str(&db, "42"));
        let fun2 = Syntax::constant_rc(ConstantId::from_str(&db, "42"));
        let fun3 = Syntax::constant_rc(ConstantId::from_str(&db, "99"));

        let arg1 = Syntax::variable_rc(Index(0));
        let arg2 = Syntax::variable_rc(Index(0));
        let arg3 = Syntax::variable_rc(Index(1));

        let app1 = Application::new(fun1.clone(), arg1.clone());
        let app2 = Application::new(fun2.clone(), arg2.clone());
        let app3 = Application::new(fun3.clone(), arg1.clone());
        let app4 = Application::new(fun1.clone(), arg3.clone());

        assert_eq!(app1, app2);
        assert_ne!(app1, app3); // different function
        assert_ne!(app1, app4); // different argument
    }

    #[test]
    fn test_pi_equality() {
        let source1 = Syntax::universe_rc(UniverseLevel::new(0));
        let source2 = Syntax::universe_rc(UniverseLevel::new(0));
        let source3 = Syntax::universe_rc(UniverseLevel::new(1));

        let target1 = Syntax::universe_rc(UniverseLevel::new(1));
        let target2 = Syntax::universe_rc(UniverseLevel::new(1));
        let target3 = Syntax::universe_rc(UniverseLevel::new(2));

        let pi1 = Pi::new(source1.clone(), target1.clone());
        let pi2 = Pi::new(source2.clone(), target2.clone());
        let pi3 = Pi::new(source3.clone(), target1.clone());
        let pi4 = Pi::new(source1.clone(), target3.clone());

        assert_eq!(pi1, pi2);
        assert_ne!(pi1, pi3); // different source
        assert_ne!(pi1, pi4); // different target
    }

    #[test]
    fn test_check_equality() {
        let ty1 = Syntax::universe_rc(UniverseLevel::new(0));
        let ty2 = Syntax::universe_rc(UniverseLevel::new(0));
        let ty3 = Syntax::universe_rc(UniverseLevel::new(1));

        use crate::Database;
        let db = Database::default();
        let term1 = Syntax::constant_rc(ConstantId::from_str(&db, "42"));
        let term2 = Syntax::constant_rc(ConstantId::from_str(&db, "42"));
        let term3 = Syntax::constant_rc(ConstantId::from_str(&db, "99"));

        let check1 = Check::new(ty1.clone(), term1.clone());
        let check2 = Check::new(ty2.clone(), term2.clone());
        let check3 = Check::new(ty3.clone(), term1.clone());
        let check4 = Check::new(ty1.clone(), term3.clone());

        assert_eq!(check1, check2);
        assert_ne!(check1, check3); // different type
        assert_ne!(check1, check4); // different term
    }

    #[test]
    fn test_metavariable_identity_equality() {
        // Metavariables use identity equality (id comparison)
        let meta_id1 = MetavariableId(0);
        let meta_id2 = MetavariableId(0);
        let meta_id3 = MetavariableId(1);

        let closure1 = Closure::new();
        let closure2 = Closure::new();

        let meta1 = Metavariable::new(meta_id1, closure1.clone());
        let meta2 = Metavariable::new(meta_id2, closure2.clone());
        let meta3 = Metavariable::new(meta_id3, closure1.clone());

        // Same identity, even with different closures
        assert_eq!(meta1, meta2);
        // Different identity, even with same closure
        assert_ne!(meta1, meta3);
    }

    #[test]
    fn test_syntax_constant_equality() {
        use crate::Database;
        let db = Database::default();
        let syn1 = Syntax::constant(ConstantId::from_str(&db, "42"));
        let syn2 = Syntax::constant(ConstantId::from_str(&db, "42"));
        let syn3 = Syntax::constant(ConstantId::from_str(&db, "99"));

        assert_eq!(syn1, syn2);
        assert_ne!(syn1, syn3);
    }

    #[test]
    fn test_syntax_variable_equality() {
        let syn1 = Syntax::variable(Index(0));
        let syn2 = Syntax::variable(Index(0));
        let syn3 = Syntax::variable(Index(1));

        assert_eq!(syn1, syn2);
        assert_ne!(syn1, syn3);
    }

    #[test]
    fn test_syntax_universe_equality() {
        let syn1 = Syntax::universe(UniverseLevel::new(0));
        let syn2 = Syntax::universe(UniverseLevel::new(0));
        let syn3 = Syntax::universe(UniverseLevel::new(1));

        assert_eq!(syn1, syn2);
        assert_ne!(syn1, syn3);
    }

    #[test]
    fn test_syntax_lambda_equality() {
        let body1 = Syntax::variable_rc(Index(0));
        let body2 = Syntax::variable_rc(Index(0));
        let body3 = Syntax::variable_rc(Index(1));

        let syn1 = Syntax::lambda(body1);
        let syn2 = Syntax::lambda(body2);
        let syn3 = Syntax::lambda(body3);

        assert_eq!(syn1, syn2);
        assert_ne!(syn1, syn3);
    }

    #[test]
    fn test_syntax_application_equality() {
        use crate::Database;
        let db = Database::default();
        let fun1 = Syntax::constant_rc(ConstantId::from_str(&db, "42"));
        let fun2 = Syntax::constant_rc(ConstantId::from_str(&db, "42"));
        let arg1 = Syntax::variable_rc(Index(0));
        let arg2 = Syntax::variable_rc(Index(0));

        let syn1 = Syntax::application(fun1.clone(), arg1.clone());
        let syn2 = Syntax::application(fun2.clone(), arg2.clone());

        assert_eq!(syn1, syn2);
    }

    #[test]
    fn test_syntax_pi_equality() {
        let source1 = Syntax::universe_rc(UniverseLevel::new(0));
        let source2 = Syntax::universe_rc(UniverseLevel::new(0));
        let target1 = Syntax::universe_rc(UniverseLevel::new(1));
        let target2 = Syntax::universe_rc(UniverseLevel::new(1));

        let syn1 = Syntax::pi(source1, target1);
        let syn2 = Syntax::pi(source2, target2);

        assert_eq!(syn1, syn2);
    }

    #[test]
    fn test_syntax_check_equality() {
        let ty1 = Syntax::universe_rc(UniverseLevel::new(0));
        let ty2 = Syntax::universe_rc(UniverseLevel::new(0));
        use crate::Database;
        let db = Database::default();
        let term1 = Syntax::constant_rc(ConstantId::from_str(&db, "42"));
        let term2 = Syntax::constant_rc(ConstantId::from_str(&db, "42"));

        let syn1 = Syntax::check(ty1, term1);
        let syn2 = Syntax::check(ty2, term2);

        assert_eq!(syn1, syn2);
    }

    #[test]
    fn test_syntax_metavariable_equality() {
        let meta_id1 = MetavariableId(0);
        let meta_id2 = MetavariableId(0);
        let meta_id3 = MetavariableId(1);

        let closure = Closure::new();

        let syn1 = Syntax::metavariable(meta_id1, closure.clone());
        let syn2 = Syntax::metavariable(meta_id2, closure.clone());
        let syn3 = Syntax::metavariable(meta_id3, closure.clone());

        assert_eq!(syn1, syn2);
        assert_ne!(syn1, syn3);
    }

    #[test]
    fn test_syntax_different_variants_not_equal() {
        use crate::Database;
        let db = Database::default();
        let constant = Syntax::constant(ConstantId::from_str(&db, "0"));
        let variable = Syntax::variable(Index(0));
        let universe = Syntax::universe(UniverseLevel::new(0));

        assert_ne!(constant, variable);
        assert_ne!(constant, universe);
        assert_ne!(variable, universe);
    }

    #[test]
    fn test_complex_nested_syntax_equality() {
        // Test: λ %0 → %0 applied to a constant
        // (λ %0 → %0) @42
        let lambda_body1 = Syntax::variable_rc(Index(0));
        let lambda1 = Syntax::lambda_rc(lambda_body1);
        use crate::Database;
        let db = Database::default();
        let arg1 = Syntax::constant_rc(ConstantId::from_str(&db, "42"));
        let app1 = Syntax::application(lambda1.clone(), arg1.clone());

        let lambda_body2 = Syntax::variable_rc(Index(0));
        let lambda2 = Syntax::lambda_rc(lambda_body2);
        let arg2 = Syntax::constant_rc(ConstantId::from_str(&db, "42"));
        let app2 = Syntax::application(lambda2.clone(), arg2.clone());

        assert_eq!(app1, app2);

        // Different argument
        let arg3 = Syntax::constant_rc(ConstantId::from_str(&db, "99"));
        let app3 = Syntax::application(lambda1, arg3);
        assert_ne!(app1, app3);
    }

    #[test]
    fn test_complex_pi_type_equality() {
        // Test: ∀(%0 : 𝒰0) → 𝒰1
        let source1 = Syntax::universe_rc(UniverseLevel::new(0));
        let target1 = Syntax::universe_rc(UniverseLevel::new(1));
        let pi1 = Syntax::pi(source1, target1);

        let source2 = Syntax::universe_rc(UniverseLevel::new(0));
        let target2 = Syntax::universe_rc(UniverseLevel::new(1));
        let pi2 = Syntax::pi(source2, target2);

        assert_eq!(pi1, pi2);

        // Nested pi: ∀(%0 : 𝒰0) (%1 : %0) → %1
        let outer_source1 = Syntax::universe_rc(UniverseLevel::new(0));
        let inner_source1 = Syntax::variable_rc(Index(0));
        let inner_target1 = Syntax::variable_rc(Index(1));
        let inner_pi1 = Syntax::pi_rc(inner_source1, inner_target1);
        let outer_pi1 = Syntax::pi(outer_source1, inner_pi1);

        let outer_source2 = Syntax::universe_rc(UniverseLevel::new(0));
        let inner_source2 = Syntax::variable_rc(Index(0));
        let inner_target2 = Syntax::variable_rc(Index(1));
        let inner_pi2 = Syntax::pi_rc(inner_source2, inner_target2);
        let outer_pi2 = Syntax::pi(outer_source2, inner_pi2);

        assert_eq!(outer_pi1, outer_pi2);
    }

    #[test]
    fn test_rc_syntax_equality() {
        // Test that RcSyntax (Rc<Syntax>) compares by value, not by pointer
        use crate::Database;
        let db = Database::default();
        let rc1 = Syntax::constant_rc(ConstantId::from_str(&db, "42"));
        let rc2 = Syntax::constant_rc(ConstantId::from_str(&db, "42"));
        let rc3 = Syntax::constant_rc(ConstantId::from_str(&db, "99"));

        assert_eq!(rc1, rc2); // Different Rc pointers, same value
        assert_ne!(rc1, rc3);

        // Test with Rc::clone
        let rc4 = Rc::clone(&rc1);
        assert_eq!(rc1, rc4); // Same Rc pointer
    }
}
