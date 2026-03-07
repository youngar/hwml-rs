pub mod check;
pub mod check_module;
pub mod common;
pub mod declaration;
pub mod environment;
pub mod equal;
pub mod eval;
pub mod lower;
pub mod pattern_unify;
pub mod quote;
pub mod symbol;
pub mod syn;
pub mod unify;
pub mod val;

pub mod test_utils;

pub use common::*;
pub use declaration::{Constant, DataConstructor, Declaration, Module, Primitive, TypeConstructor};
pub use symbol::InternedString;
pub use syn::{parse_module, Syntax};
pub use val::{GlobalEnv, Value};
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
