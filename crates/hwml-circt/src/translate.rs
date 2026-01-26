//! Translation from HWML AST to CIRCT IR (using raw MLIR C API).
//!
//! This module provides a simplified translation layer that uses the raw MLIR C API
//! instead of the melior Rust bindings.

// Re-export the main translation functions
pub use crate::translate_new::*;
