pub mod binding;
pub mod check;
pub mod check_module;
pub mod common;
pub mod equal;
pub mod eval;
pub mod lower;
pub mod name;
pub mod pattern_unify;
pub mod quote;
pub mod syn;
pub mod test_utils;
pub mod typed;
pub mod unify;
pub mod val;
pub mod word;

pub use binding::*;
pub use common::*;
pub use name::*;
pub use typed::Typed;
pub use word::Word;

pub use syn::declaration::{
    CompilationUnit, ConstantDecl, DataConstructorDecl, Declaration, PrimitiveDecl,
    TypeConstructorDecl,
};
pub use syn::{parse_module, BindingSyntax, DynBindingSyntax, RcSyntax, Syntax};
pub use typed::*;
pub use val::{GlobalEnv, RcValue, Value};

#[salsa::db]
#[derive(Default, Clone)]
pub struct Database {
    storage: salsa::Storage<Self>,
}

#[salsa::db]
impl salsa::Database for Database {
    fn salsa_event(&self, _event: &dyn Fn() -> salsa::Event) {
        // No-op for simple database
    }
}

impl Database {
    pub fn new() -> Self {
        Self::default()
    }
}
