#![allow(clippy::needless_borrow)]

use derive_new::new;

#[salsa::input]
pub struct SourceProgram {
    #[return_ref]
    pub text: String,
}

#[salsa::interned]
pub struct Identifier<'db> {
    #[return_ref]
    pub text: String,
}

#[salsa::tracked]
pub struct Program<'db> {
    #[tracked]
    #[return_ref]
    pub definitions: Vec<Definition<'db>>,
}

#[derive(Eq, PartialEq, Debug, Hash, new, salsa::Update)]
pub struct Definition<'db> {
    pub identifier: Identifier<'db>,
    pub value: Expression<'db>,
}

#[derive(Eq, PartialEq, Debug, Hash, new, salsa::Update)]
pub enum Expression<'db> {
    Variable(Identifier<'db>),
}
