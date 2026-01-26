//! Low-level FFI bindings to CIRCT (Circuit IR Compilers and Tools)
//!
//! This crate provides unsafe Rust bindings to the CIRCT C API.
//! For safe, high-level bindings, use the `hwml_circt` crate instead.
//!
//! # Safety
//!
//! All functions in this crate are `unsafe` because they directly call into
//! C/C++ code. Improper use can lead to undefined behavior, memory corruption,
//! or crashes.
//!
//! # Installation
//!
//! This crate requires CIRCT to be installed on your system. See the README
//! for installation instructions.

#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(dead_code)]
#![allow(unsafe_code)]

// Include the generated bindings
include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

// Safe wrappers
pub mod mlir_context;

pub use mlir_context::{
    create_named_attribute, export_verilog, operation_result, run_lower_seq_to_sv,
    MlirAttributeWrapper, MlirBlockWrapper, MlirContextWrapper, MlirLocationWrapper,
    MlirModuleWrapper, MlirRegionWrapper, MlirTypeWrapper, MlirValueWrapper, OperationBuilder,
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bindings_exist() {
        // This test just verifies that the bindings were generated
        // We can't do much more without actually using CIRCT
        // The real tests will be in the hwml_circt crate
    }
}
