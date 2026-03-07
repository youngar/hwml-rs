#![allow(clippy::elidable_lifetime_names)]
#![allow(clippy::missing_errors_doc)]
#![allow(clippy::missing_panics_doc)]
#![allow(clippy::must_use_candidate)]
#![allow(clippy::return_self_not_must_use)]
#![allow(clippy::module_name_repetitions)]
#![allow(clippy::similar_names)]
#![allow(clippy::too_many_lines)]
#![allow(clippy::uninlined_format_args)]
#![allow(clippy::doc_markdown)]
#![allow(clippy::needless_borrow)]
#![allow(clippy::unnecessary_wraps)]
#![allow(clippy::semicolon_if_nothing_returned)]
#![allow(clippy::single_match_else)]
#![allow(clippy::needless_pass_by_value)]
#![allow(clippy::explicit_iter_loop)]
#![allow(clippy::wildcard_imports)]
#![allow(clippy::from_over_into)]
#![allow(clippy::field_reassign_with_default)]
#![allow(clippy::used_underscore_binding)]
#![allow(clippy::match_same_arms)]
#![allow(clippy::new_without_default)]
#![allow(clippy::redundant_closure)]
#![allow(clippy::match_wildcard_for_single_variants)]
#![allow(clippy::cloned_instead_of_copied)]
#![allow(clippy::enum_variant_names)]
#![allow(clippy::manual_while_let_some)]
#![allow(clippy::extra_unused_lifetimes)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::trivially_copy_pass_by_ref)]
#![allow(clippy::len_without_is_empty)]
#![allow(clippy::match_single_binding)]
#![allow(clippy::unnecessary_cast)]
#![allow(clippy::iter_cloned_collect)]
#![allow(clippy::iter_without_into_iter)]
#![allow(clippy::explicit_deref_methods)]
#![allow(clippy::explicit_into_iter_loop)]
#![allow(clippy::inconsistent_struct_constructor)]
#![allow(clippy::needless_borrows_for_generic_args)]
#![allow(clippy::single_match)]
#![allow(clippy::assign_op_pattern)]
#![allow(clippy::while_let_loop)]
#![allow(clippy::enum_glob_use)]
#![allow(clippy::useless_conversion)]
#![allow(clippy::explicit_auto_deref)]
#![allow(clippy::ignored_unit_patterns)]

pub mod check;
pub mod check_module;
pub mod common;
pub mod declaration;
pub mod equal;
pub mod erased;
pub mod eval;
pub mod lower;
pub mod pattern_unify;
pub mod problem;
pub mod quote;
pub mod symbol;
pub mod syn;
pub mod test_utils;
pub mod typed;
pub mod unify;
pub mod val;

pub use common::*;
pub use declaration::{Constant, DataConstructor, Declaration, Module, Primitive, TypeConstructor};
pub use erased::{erase, Erased};
pub use problem::{Problem, QName};
pub use symbol::InternedString;
pub use syn::{parse_module, RcSyntax, Syntax};
pub use typed::{Typed, TypedSyntax, TypedValue};
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
