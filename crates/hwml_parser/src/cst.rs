use derive_new::new;
use std::ops::Range;

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct Program {
    statements: Vec<Stmt>,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub enum Stmt {
    Def(Def),
    Error,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct Def {
    name: Id,
    args: Vec<BindingGroup>,
    expr: Box<Expr>,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub enum Expr {
    Pi(Pi),
    Fun(Fun),
    App(Vec<Box<Expr>>),
    Lam(Lam),
    LetIn(LetIn),
    Var(Id),
    Underscore(Underscore),
    Paren(Paren),
    Num(Num),
    Str(Str),
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct Pi {
    bindings: Vec<BindingGroup>,
    result: Box<Expr>,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct Fun {
    names: Vec<Box<Expr>>,
    result: Box<Expr>,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct LetIn {
    name: Id,
    value: Box<Expr>,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct Lam {
    bindings: Vec<BindingGroup>,
    body: Box<Expr>,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct Underscore {
    loc: Range<usize>,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct Paren {
    body: Box<Expr>,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct BindingGroup {
    app: Vec<Box<Expr>>,
    typ: Box<Expr>,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct Id {
    value: String,
    loc: Range<usize>,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct Num {
    value: i32,
    loc: Range<usize>,
}

#[derive(Eq, PartialEq, Debug, Hash, new)]
pub struct Str {
    value: String,
}
