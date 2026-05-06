use derive_new::new;
use std::ops::Range;

/// Source location in Line:Column format (0-based)
/// This is more convenient for creating hwml_core::Location later
#[derive(Clone, Copy, Eq, PartialEq, Debug, Hash)]
pub struct LineColRange {
    pub start_line: usize,
    pub start_column: usize,
    pub end_line: usize,
    pub end_column: usize,
}

impl LineColRange {
    pub fn new(start_line: usize, start_column: usize, end_line: usize, end_column: usize) -> Self {
        LineColRange {
            start_line,
            start_column,
            end_line,
            end_column,
        }
    }

    /// Create from a byte range using ParserContext
    pub fn from_byte_range(
        start: usize,
        end: usize,
        ctx: &mut crate::parsing::ParserContext,
    ) -> Self {
        let (start_line, start_column, end_line, end_column) = ctx.range_to_line_col(start, end);
        LineColRange::new(start_line, start_column, end_line, end_column)
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Program {
    pub statements: Vec<Statement>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub enum Statement {
    Namespace(Namespace),
    Def(Def),
    Meta(Meta),
    Prim(Prim),
    Inductive(Inductive),
    Open(Open),
}

#[derive(Clone, Eq, PartialEq, Debug, Hash)]
pub struct Namespace {
    pub loc: Range<usize>,      // Old byte range (for backward compat)
    pub line_col: LineColRange, // New line:column range
    pub name: Id,
    pub statements: Vec<Statement>,
}

impl Namespace {
    /// Old constructor using byte range (deprecated but kept for compatibility)
    pub fn new(loc: Range<usize>, name: Id, statements: Vec<Statement>) -> Self {
        // Default line_col to zeros - should be replaced with actual conversion
        Namespace {
            loc,
            line_col: LineColRange::new(0, 0, 0, 0),
            name,
            statements,
        }
    }

    /// New constructor using line:column range
    pub fn new_with_line_col(line_col: LineColRange, name: Id, statements: Vec<Statement>) -> Self {
        // Keep old loc as 0..0 for now - can be removed once all code migrated
        Namespace {
            loc: 0..0,
            line_col,
            name,
            statements,
        }
    }
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
    Universe(Universe),
    Dot(Dot),
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
    pub binders: Vec<Box<Expression>>,
    pub ty: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct UntypedBindingGroup {
    pub binders: Box<Expression>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct App {
    pub loc: Range<usize>,
    pub elements: Vec<Box<Expression>>,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Id {
    pub loc: Range<usize>,
    pub value: Box<[u8]>,
}

impl Id {
    /// Iterator over the segments of a qualified identifier.
    /// For example, "Foo.Bar.Baz" yields ["Foo", "Bar", "Baz"]
    /// A simple identifier like "Foo" yields ["Foo"]
    pub fn segments(&self) -> impl Iterator<Item = &[u8]> {
        self.value.split(|&b| b == b'.')
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, new)]
pub struct Num {
    pub loc: Range<usize>,
    pub value: Box<[u8]>,
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
    pub pattern: Box<Expression>,
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
