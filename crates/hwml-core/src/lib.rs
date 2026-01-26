pub mod check;
pub mod check_module;
pub mod common;
pub mod declaration;
pub mod environment;
pub mod equal;
pub mod eval;
pub mod prelude;
pub mod quote;
pub mod symbol;
pub mod syn;
pub mod unify;
pub mod val;

pub use common::*;
pub use syn::Syntax;
pub use val::Value;

/// A simple database implementation for testing and parsing.
/// This is a minimal implementation that only supports string interning.
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
