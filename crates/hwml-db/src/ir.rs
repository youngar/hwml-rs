#![allow(clippy::needless_borrow)]

use derive_new::new;

#[salsa::tracked]
pub struct Program<'db> {
    #[tracked]
    #[return_ref]
    pub definitions: Vec<Definition>,
}

#[derive(Eq, PartialEq, Debug, Hash, new, salsa::Update)]
pub struct Definition {
    //pub identifier: Identifier<'db>,
    //pub value: Expression<'db>,
}
