use crate::common::{Index, Level, UniverseLevel};
use std::rc::Rc;

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone, Copy)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct ConstantId(pub u32);

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone, Copy)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct MetavariableId(pub usize);

impl std::fmt::Display for MetavariableId {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "?{}", self.0)
    }
}

pub type RcSyntax = Rc<Syntax>;

pub type Tm = Syntax;
pub type Ty = Syntax;

/// A captured environment.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Closure {
    /// The environment contains a vector of definitions.
    pub values: Vec<RcSyntax>,
}

impl Closure {
    pub fn new() -> Closure {
        Closure { values: Vec::new() }
    }

    pub fn with_values(values: Vec<RcSyntax>) -> Closure {
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
pub struct Environment {
    types: Vec<RcSyntax>,
}

impl Environment {
    pub fn new() -> Environment {
        Environment { types: Vec::new() }
    }
    pub fn depth(&self) -> usize {
        self.types.len()
    }
    pub fn to_index(&self, level: Level) -> Index {
        level.to_index(self.depth())
    }
    pub fn to_level(&self, index: Index) -> Level {
        index.to_level(self.depth())
    }
    pub fn extend(&mut self, ty: RcSyntax) -> Level {
        self.types.push(ty);
        Level::new(self.depth() - 1)
    }
    pub fn pop(&mut self) {
        self.types.pop();
    }
    pub fn truncate(&mut self, depth: usize) {
        self.types.truncate(depth);
    }
    pub fn lookup(&self, level: Level) -> RcSyntax {
        let index: usize = level.into();
        self.types.get(index).unwrap().clone()
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum Syntax {
    Constant(Constant),
    Variable(Variable),
    Check(Check),
    Pi(Pi),
    Lambda(Lambda),
    Application(Application),
    Universe(Universe),
    Metavariable(Metavariable),
    Lift(Lift),
    Quote(Quote),
    HArrow(HArrow),
}

impl Syntax {
    pub fn constant(name: ConstantId) -> Syntax {
        Syntax::Constant(Constant::new(name))
    }

    pub fn constant_rc(name: ConstantId) -> RcSyntax {
        Rc::new(Syntax::constant(name))
    }

    pub fn variable(index: Index) -> Syntax {
        Syntax::Variable(Variable::new(index))
    }

    pub fn variable_rc(index: Index) -> RcSyntax {
        Rc::new(Syntax::variable(index))
    }

    pub fn check(ty: RcSyntax, term: RcSyntax) -> Syntax {
        Syntax::Check(Check::new(ty, term))
    }

    pub fn check_rc(ty: RcSyntax, term: RcSyntax) -> RcSyntax {
        Rc::new(Syntax::check(ty, term))
    }

    pub fn pi(source: RcSyntax, target: RcSyntax) -> Syntax {
        Syntax::Pi(Pi::new(source, target))
    }

    pub fn pi_rc(source: RcSyntax, target: RcSyntax) -> RcSyntax {
        Rc::new(Syntax::pi(source, target))
    }

    pub fn lambda(body: RcSyntax) -> Syntax {
        Syntax::Lambda(Lambda::new(body))
    }

    pub fn lambda_rc(body: RcSyntax) -> RcSyntax {
        Rc::new(Syntax::lambda(body))
    }

    pub fn application(fun: RcSyntax, arg: RcSyntax) -> Syntax {
        Syntax::Application(Application::new(fun, arg))
    }

    pub fn application_rc(fun: RcSyntax, arg: RcSyntax) -> RcSyntax {
        Rc::new(Syntax::application(fun, arg))
    }

    pub fn universe(level: UniverseLevel) -> Syntax {
        Syntax::Universe(Universe::new(level))
    }

    pub fn universe_rc(level: UniverseLevel) -> RcSyntax {
        Rc::new(Syntax::universe(level))
    }

    // Create a metavariable syntax node with a reference to an existing metavariable.
    pub fn metavariable(metavariable: MetavariableId, closure: Closure) -> Syntax {
        Syntax::Metavariable(Metavariable::new(metavariable, closure))
    }

    pub fn metavariable_rc(metavariable: MetavariableId, closure: Closure) -> RcSyntax {
        Rc::new(Syntax::metavariable(metavariable, closure))
    }

    pub fn lift(tm: RcSyntax) -> Syntax {
        Syntax::Lift(Lift::new(tm))
    }

    pub fn lift_rc(tm: RcSyntax) -> RcSyntax {
        Rc::new(Syntax::lift(tm))
    }

    pub fn quote(tm: RcHSyntax) -> Syntax {
        Syntax::Quote(Quote::new(tm))
    }

    pub fn quote_rc(tm: RcHSyntax) -> RcSyntax {
        Rc::new(Syntax::quote(tm))
    }

    pub fn harrow(source: RcSyntax, target: RcSyntax) -> Syntax {
        Syntax::HArrow(HArrow::new(source, target))
    }

    pub fn harrow_rc(source: RcSyntax, target: RcSyntax) -> RcSyntax {
        Rc::new(Syntax::harrow(source, target))
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Constant {
    pub name: ConstantId,
}

impl Constant {
    pub fn new(name: ConstantId) -> Constant {
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
pub struct Check {
    pub ty: RcSyntax,
    pub term: RcSyntax,
}

impl Check {
    pub fn new(ty: RcSyntax, term: RcSyntax) -> Check {
        Check { ty, term }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Pi {
    pub source: RcSyntax,
    pub target: RcSyntax,
}

impl Pi {
    pub fn new(source: RcSyntax, target: RcSyntax) -> Pi {
        Pi { source, target }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Lambda {
    pub body: RcSyntax,
}

impl Lambda {
    pub fn new(body: RcSyntax) -> Lambda {
        Lambda { body }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Application {
    pub function: RcSyntax,
    pub argument: RcSyntax,
}

impl Application {
    pub fn new(function: RcSyntax, argument: RcSyntax) -> Application {
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
pub struct Metavariable {
    pub id: MetavariableId,
    pub closure: Closure,
}

impl Metavariable {
    pub fn new(id: MetavariableId, closure: Closure) -> Metavariable {
        Metavariable { id, closure }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Lift {
    pub tm: RcSyntax,
}

impl Lift {
    pub fn new(tm: RcSyntax) -> Lift {
        Lift { tm }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Quote {
    pub tm: RcHSyntax,
}

impl Quote {
    pub fn new(tm: RcHSyntax) -> Quote {
        Quote { tm }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct HArrow {
    pub source: RcSyntax,
    pub target: RcSyntax,
}

impl HArrow {
    pub fn new(source: RcSyntax, target: RcSyntax) -> HArrow {
        HArrow { source, target }
    }
}

pub type RcHSyntax = Rc<HSyntax>;

pub type HTm = HSyntax;
pub type HTy = HSyntax;

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum HSyntax {
    HConstant(Constant),
    HVariable(Variable),
    HCheck(HCheck),
    HLambda(HLambda),
    HApplication(HApplication),
    Splice(Splice),
}

impl HSyntax {
    pub fn hconstant(name: ConstantId) -> HSyntax {
        HSyntax::HConstant(Constant::new(name))
    }

    pub fn hconstant_rc(name: ConstantId) -> RcHSyntax {
        Rc::new(HSyntax::hconstant(name))
    }

    pub fn hvariable(index: Index) -> HSyntax {
        HSyntax::HVariable(Variable::new(index))
    }

    pub fn hvariable_rc(index: Index) -> RcHSyntax {
        Rc::new(HSyntax::hvariable(index))
    }

    pub fn hcheck(ty: RcHSyntax, term: RcHSyntax) -> HSyntax {
        HSyntax::HCheck(HCheck::new(ty, term))
    }

    pub fn hcheck_rc(ty: RcHSyntax, term: RcHSyntax) -> RcHSyntax {
        Rc::new(HSyntax::hcheck(ty, term))
    }

    pub fn hlambda(body: RcHSyntax) -> HSyntax {
        HSyntax::HLambda(HLambda::new(body))
    }

    pub fn hlambda_rc(body: RcHSyntax) -> RcHSyntax {
        Rc::new(HSyntax::hlambda(body))
    }

    pub fn happlication(function: RcHSyntax, argument: RcHSyntax) -> HSyntax {
        HSyntax::HApplication(HApplication::new(function, argument))
    }

    pub fn happlication_rc(function: RcHSyntax, argument: RcHSyntax) -> RcHSyntax {
        Rc::new(HSyntax::happlication(function, argument))
    }

    pub fn splice(term: RcSyntax) -> HSyntax {
        HSyntax::Splice(Splice::new(term))
    }

    pub fn splice_rc(term: RcSyntax) -> RcHSyntax {
        Rc::new(HSyntax::splice(term))
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct HCheck {
    pub ty: RcHSyntax,
    pub term: RcHSyntax,
}

impl HCheck {
    pub fn new(ty: RcHSyntax, term: RcHSyntax) -> HCheck {
        HCheck { ty, term }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct HLambda {
    pub body: RcHSyntax,
}

impl HLambda {
    pub fn new(body: RcHSyntax) -> HLambda {
        HLambda { body }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct HApplication {
    pub function: RcHSyntax,
    pub argument: RcHSyntax,
}

impl HApplication {
    pub fn new(function: RcHSyntax, argument: RcHSyntax) -> HApplication {
        HApplication { function, argument }
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Splice {
    pub term: RcSyntax,
}

impl Splice {
    pub fn new(term: RcSyntax) -> Splice {
        Splice { term }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{Index, UniverseLevel};

    #[test]
    fn test_name_id_equality() {
        let name1 = ConstantId(42);
        let name2 = ConstantId(42);
        let name3 = ConstantId(99);

        assert_eq!(name1, name2);
        assert_ne!(name1, name3);
    }

    #[test]
    fn test_constant_equality() {
        let const1 = Constant::new(ConstantId(42));
        let const2 = Constant::new(ConstantId(42));
        let const3 = Constant::new(ConstantId(99));

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

        let val1 = Syntax::constant_rc(ConstantId(42));
        let val2 = Syntax::constant_rc(ConstantId(42));
        let val3 = Syntax::constant_rc(ConstantId(99));

        let closure3 = Closure::with_values(vec![val1.clone()]);
        let closure4 = Closure::with_values(vec![val2.clone()]);
        let closure5 = Closure::with_values(vec![val3.clone()]);

        assert_eq!(closure3, closure4);
        assert_ne!(closure3, closure5);
    }

    #[test]
    fn test_environment_equality() {
        let env1 = Environment::new();
        let env2 = Environment::new();
        assert_eq!(env1, env2);
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
        let fun1 = Syntax::constant_rc(ConstantId(42));
        let fun2 = Syntax::constant_rc(ConstantId(42));
        let fun3 = Syntax::constant_rc(ConstantId(99));

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

        let term1 = Syntax::constant_rc(ConstantId(42));
        let term2 = Syntax::constant_rc(ConstantId(42));
        let term3 = Syntax::constant_rc(ConstantId(99));

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
        let syn1 = Syntax::constant(ConstantId(42));
        let syn2 = Syntax::constant(ConstantId(42));
        let syn3 = Syntax::constant(ConstantId(99));

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
        let fun1 = Syntax::constant_rc(ConstantId(42));
        let fun2 = Syntax::constant_rc(ConstantId(42));
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
        let term1 = Syntax::constant_rc(ConstantId(42));
        let term2 = Syntax::constant_rc(ConstantId(42));

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
        let constant = Syntax::constant(ConstantId(0));
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
        let arg1 = Syntax::constant_rc(ConstantId(42));
        let app1 = Syntax::application(lambda1.clone(), arg1.clone());

        let lambda_body2 = Syntax::variable_rc(Index(0));
        let lambda2 = Syntax::lambda_rc(lambda_body2);
        let arg2 = Syntax::constant_rc(ConstantId(42));
        let app2 = Syntax::application(lambda2.clone(), arg2.clone());

        assert_eq!(app1, app2);

        // Different argument
        let arg3 = Syntax::constant_rc(ConstantId(99));
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
        let rc1 = Syntax::constant_rc(ConstantId(42));
        let rc2 = Syntax::constant_rc(ConstantId(42));
        let rc3 = Syntax::constant_rc(ConstantId(99));

        assert_eq!(rc1, rc2); // Different Rc pointers, same value
        assert_ne!(rc1, rc3);

        // Test with Rc::clone
        let rc4 = Rc::clone(&rc1);
        assert_eq!(rc1, rc4); // Same Rc pointer
    }
}
