pub mod binding;
pub mod check;
pub mod check_module;
pub mod common;
pub mod equal;
pub mod eval;
pub mod global_env;
pub mod lower;
pub mod name;
pub mod pattern_unify;
pub mod quote;
pub mod source_range;
pub mod syn;
pub mod test_utils;
pub mod ty; // Semantic type system (type codes architecture)
pub mod typed;
pub mod val;
pub mod word;

pub use binding::*;
pub use common::*;
pub use global_env::*;
pub use name::*;
pub use source_range::*;
pub use syn::declaration::{
    CompilationUnit, ConstantDecl, DataConstructorDecl, Declaration, PrimitiveDecl,
    TypeConstructorDecl,
};
pub use syn::{parse_module, BindingSyntax, DynBindingSyntax, RcSyntax, Syntax};
pub use typed::Typed;
pub use typed::*;
pub use val::{RcValue, Value};
pub use word::Word;

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
