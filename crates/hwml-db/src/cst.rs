use crate::parsing::Token;
use derive_new::new;
use la_arena::Idx;
use std::ops::Range;

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct Program {
    pub stmt_indices: Vec<Idx<Node>>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash, new)]
pub enum Assoc {
    Left,
    Right,
    None,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct Def {
    pub id: Idx<Node>,
    pub assoc: Assoc,
    pub precedence: u8,
    pub bindings: Idx<Node>,
    pub value: Idx<Node>,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct Pi {
    pub bindings: Idx<Node>,
    pub expr: Idx<Node>,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct Fun {
    pub bindings: Idx<Node>,
    pub body: Idx<Node>,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct LetIn {
    pub id: Idx<Node>,
    pub value: Idx<Node>,
    pub expr: Idx<Node>,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct Lam {
    pub bindings: Idx<Node>,
    pub expr: Idx<Node>,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct Underscore {}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct Paren {
    pub expr: Idx<Node>,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct Bindings {
    pub groups: Vec<Idx<Node>>,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct BindingGroup {
    pub binders: Idx<Node>,
    pub ty: Idx<Node>,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct App {
    pub head: Idx<Node>,
    pub arg: Idx<Node>,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct Id {
    pub value: String,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct Num {
    pub value: String,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct Str {
    pub value: String,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub enum Node {
    Program(Program),
    // Statements.
    Def(Def),
    Error,

    // Syntax.
    Bindings(Bindings),
    BindingGroup(BindingGroup),

    // Expressions.
    Pi(Pi),
    Fun(Fun),
    App(App),
    Lam(Lam),
    LetIn(LetIn),
    Underscore(Underscore),
    Paren(Paren),
    Num(Num),
    Str(Str),
    Id(Id),
}

#[derive(Eq, PartialEq, Debug, Hash, new, Copy, Clone)]
pub struct Location {
    pub start: Idx<Token>,
    pub end: Idx<Token>,
}

impl Location {
    pub fn from_u32(start: u32, end: u32) -> Location {
        Location {
            start: Idx::from_raw(start.into()),
            end: Idx::from_raw(end.into()),
        }
    }
}
