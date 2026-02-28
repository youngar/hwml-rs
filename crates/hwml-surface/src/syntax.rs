use derive_new::new;
use std::ops::Range;

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Program {
    pub statements: Vec<Statement>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub enum Statement {
    Def(Def),
    Meta(Meta),
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Meta {
    pub id: Id,
    pub bindings: Bindings,
    pub ty: Option<Box<Expression>>,
    pub value: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Def {
    pub id: Id,
    pub bindings: Bindings,
    pub ty: Option<Box<Expression>>,
    pub value: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub enum Expression {
    Pi(Pi),
    Arrow(Arrow),
    FatArrow(FatArrow),
    App(App),
    Fun(Fun),
    LetIn(LetIn),
    Match(Match),
    Underscore(Underscore),
    Paren(Paren),
    Num(Num),
    Str(Str),
    Id(Id),
    Quote(Quote),
    Splice(Splice),
    Lift(Lift),
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Pi {
    pub bindings: TypedBindings,
    pub target: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Arrow {
    pub source: Box<Expression>,
    pub target: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct FatArrow {
    pub source: Box<Expression>,
    pub target: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct LetIn {
    pub id: Id,
    pub bindings: Bindings,
    pub ty: Option<Box<Expression>>,
    pub value: Box<Expression>,
    pub expr: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Fun {
    pub bindings: Bindings,
    pub expr: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Underscore {
    pub loc: Location,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Paren {
    pub expr: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub enum BindingGroup {
    Typed(TypedBindingGroup),
    Untyped(UntypedBindingGroup),
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Bindings {
    pub groups: Vec<BindingGroup>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct TypedBindings {
    pub groups: Vec<TypedBindingGroup>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct TypedBindingGroup {
    pub binders: Vec<Box<Expression>>,
    pub ty: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct UntypedBindingGroup {
    pub binders: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct App {
    pub elements: Vec<Box<Expression>>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Id {
    pub loc: Location,
    pub value: Box<[u8]>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Num {
    pub loc: Location,
    pub value: Box<[u8]>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Str {
    pub value: String,
}

type Location = Range<usize>;

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Match {
    pub scrutinee: Box<Expression>,
    pub clauses: Vec<MatchClause>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct MatchClause {
    pub pattern: Box<Expression>,
    pub body: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Quote {
    pub expr: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Splice {
    pub expr: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Lift {
    pub expr: Box<Expression>,
}
