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
pub mod source_range;
pub mod syn;
pub mod test_utils;
pub mod ty; // Semantic type system (type codes architecture)
pub mod typed;
pub mod val;
pub mod word;

pub use binding::*;
pub use common::*;
pub use name::*;
pub use source_range::{
    HasSourceRange, Source, SourceFileId, SourceInfo, SourceRange, WithSourceRange,
};
pub use typed::Typed;
pub use word::Word;

pub use syn::declaration::{
    CompilationUnit, ConstantDecl, DataConstructorDecl, Declaration, PrimitiveDecl,
    TypeConstructorDecl,
};
pub use syn::{parse_module, BindingSyntax, DynBindingSyntax, RcSyntax, Syntax};
pub use syn::telescope::Cell;
pub use typed::*;
pub use val::{GlobalEnv, RcValue, Value};

/// Test-only database for hwml-core unit tests.
///
/// **For production use, use `hwml_db::HwmlDatabase` instead.**
///
/// This minimal database is provided only for testing hwml-core in isolation.
#[salsa::db]
#[derive(Default, Clone)]
pub struct TestDatabase {
    storage: salsa::Storage<Self>,
}

#[salsa::db]
impl salsa::Database for TestDatabase {
    fn salsa_event(&self, _event: &dyn Fn() -> salsa::Event) {
        // No-op for test database
    }
}
