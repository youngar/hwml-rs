use derive_new::new;
use std::ops::Range;

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Program {
    pub statements: Vec<Statement>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash)]
pub enum Statement {
    Namespace(Namespace),
    Def(Def),
    Meta(Meta),
    Prim(Prim),
    Inductive(Inductive),
    Open(Open),

    /// Invalid statement (parse error)
    Invalid(StatementError),
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Namespace {
    pub loc: Range<usize>,
    pub name: Id,
    pub statements: Vec<Statement>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub enum OpenModifier {
    Only(Range<usize>, Vec<Id>),
    Hiding(Range<usize>, Vec<Id>),
    Renaming(Range<usize>, Id, Id),
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Open {
    pub loc: Range<usize>,
    pub namespace: Id,
    pub modifiers: Vec<OpenModifier>,
    pub as_alias: Option<Id>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Meta {
    pub loc: Range<usize>,
    pub id: Id,
    pub bindings: Bindings,
    pub ty: Option<Box<Expression>>,
    pub value: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Def {
    pub loc: Range<usize>,
    pub id: Id,
    pub bindings: Bindings,
    pub ty: Option<Box<Expression>>,
    pub value: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Prim {
    pub loc: Range<usize>,
    pub id: Id,
    pub ty: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash)]
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
    Universe(Universe),
    Dot(Dot),

    /// Error node (parse error occurred)
    Error(ExpressionError),

    /// Hole (user-written '?hole' or '_')
    Hole(ExpressionHole),
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Universe {
    pub loc: Range<usize>,
    pub level: Option<u32>, // None means Type, Some(n) means Type n
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Pi {
    pub loc: Range<usize>,
    pub bindings: TypedBindings,
    pub target: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Arrow {
    pub loc: Range<usize>,
    pub source: Box<Expression>,
    pub target: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct FatArrow {
    pub loc: Range<usize>,
    pub source: Box<Expression>,
    pub target: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct LetIn {
    pub loc: Range<usize>,
    pub id: Id,
    pub bindings: Bindings,
    pub ty: Option<Box<Expression>>,
    pub value: Box<Expression>,
    pub expr: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Fun {
    pub loc: Range<usize>,
    pub bindings: Bindings,
    pub expr: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Underscore {
    pub loc: Range<usize>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Paren {
    pub expr: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Dot {
    pub loc: Range<usize>,
    pub receiver: Box<Expression>,
    pub field: Id,
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
    pub binders: Vec<Binder>,
    pub ty: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct UntypedBindingGroup {
    pub binders: Vec<Binder>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct App {
    pub loc: Range<usize>,
    pub elements: Vec<Box<Expression>>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Id {
    pub loc: Range<usize>,
    pub value: Box<str>,
}

impl Id {
    /// Iterator over the segments of a qualified identifier.
    /// For example, "Foo.Bar.Baz" yields ["Foo", "Bar", "Baz"]
    /// A simple identifier like "Foo" yields ["Foo"]
    pub fn segments(&self) -> impl Iterator<Item = &str> {
        self.value.split('.')
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Num {
    pub loc: Range<usize>,
    pub value: Box<str>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Str {
    pub value: String,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Match {
    pub scrutinee: Box<Expression>,
    pub clauses: Vec<MatchClause>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct MatchClause {
    pub pattern: Pattern,
    pub body: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Inductive {
    pub loc: Range<usize>,
    pub name: Id,
    pub parameters: TypedBindings,
    pub indices: TypedBindings,
    pub universe: Box<Expression>,
    pub constructors: Vec<Constructor>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Constructor {
    pub loc: Range<usize>,
    pub name: Id,
    pub ty: Box<Expression>,
}

// ===== Pattern AST (for surface syntax, unresolved) =====

/// Pattern - represents unresolved patterns in surface syntax
/// These will be resolved during scope checking to determine:
/// - Which identifiers are constructors vs variables
/// - How to structure mixfix operators
#[derive(Clone, Eq, PartialEq, Debug, Hash)]
pub enum Pattern {
    /// Identifier (could be constructor or variable - resolved in scope checker)
    /// Example: `x`, `Just`, `Cons`
    Id(Id),

    /// Application sequence (flat, not structured by precedence)
    /// Example: `Just x` parses as AppSeq([Id(Just), Id(x)])
    /// Example: `if x then y else z` parses as AppSeq([Id(if), Id(x), Id(then), Id(y), Id(else), Id(z)])
    AppSeq(AppSeq),

    /// As-pattern: name @ pattern
    /// Example: `xs @ (Cons x rest)`
    As(AsPattern),

    /// Wildcard underscore
    Underscore(Underscore),

    /// Parenthesized pattern
    Paren(ParenPattern),

    /// Literal number
    Num(Num),

    /// Literal string
    Str(Str),

    /// Error pattern (parse error)
    Error(PatternError),
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct AppSeq {
    pub loc: Range<usize>,
    /// Sequence of identifiers/atoms that make up this pattern
    /// The scope checker will resolve this into structured patterns
    pub items: Vec<Pattern>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct AsPattern {
    pub loc: Range<usize>,
    pub name: Id,
    pub pattern: Box<Pattern>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct ParenPattern {
    pub loc: Range<usize>,
    pub inner: Box<Pattern>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct PatternError {
    pub loc: Range<usize>,
    pub message: String,
}

// ===== Binder (replaces Expression in binding positions) =====

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Binder {
    pub loc: Range<usize>,
    pub pattern: Pattern,
}

// ===== Error and Hole Nodes =====

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct ExpressionError {
    pub loc: Range<usize>,
    pub message: String,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct ExpressionHole {
    pub loc: Range<usize>,
    pub name: Option<String>,  // Named hole like '?goal'
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct StatementError {
    pub loc: Range<usize>,
    pub message: String,
}


impl Expression {
    /// Get the location range of this expression
    pub fn loc(&self) -> Range<usize> {
        match self {
            Expression::Pi(pi) => pi.loc.clone(),
            Expression::Arrow(arrow) => arrow.loc.clone(),
            Expression::FatArrow(fa) => fa.loc.clone(),
            Expression::App(app) => app.loc.clone(),
            Expression::Fun(fun) => fun.loc.clone(),
            Expression::LetIn(let_in) => let_in.loc.clone(),
            Expression::Match(m) => {
                // Match doesn't have a loc field - use scrutinee loc
                m.scrutinee.loc()
            }
            Expression::Underscore(u) => u.loc.clone(),
            Expression::Paren(p) => p.expr.loc(),
            Expression::Num(n) => n.loc.clone(),
            Expression::Str(_) => {
                // Str doesn't have loc - return dummy range
                0..0
            }
            Expression::Id(id) => id.loc.clone(),
            Expression::Universe(u) => u.loc.clone(),
            Expression::Dot(d) => d.loc.clone(),
            Expression::Error(e) => e.loc.clone(),
            Expression::Hole(h) => h.loc.clone(),
        }
    }
}