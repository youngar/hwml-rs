//! CIRCT backend for HWML
//!
//! This crate provides a backend that compiles HWML modules to Verilog
//! using CIRCT (Circuit IR Compilers and Tools).
//!
//! # Architecture
//!
//! The backend works in several stages:
//! 1. **Dialect Registration**: Register CIRCT dialects (HW, Comb, Seq) with MLIR context
//! 2. **Translation**: Convert HWML AST to CIRCT IR using the HW dialect
//! 3. **Export**: Export CIRCT IR to Verilog using CIRCT's export functionality
//!
//! # Example
//!
//! ```ignore
//! use hwml_circt::CirctBackend;
//! use hwml_core::declaration::Module;
//!
//! let backend = CirctBackend::new()?;
//! let verilog = backend.compile_to_verilog(&module)?;
//! println!("{}", verilog);
//! ```

pub mod context;
pub mod dialects;
pub mod error;
pub mod export;
pub mod translate;
mod translate_new;

pub use context::CirctContext;
pub use error::{Error, Result};

use hwml_core::declaration::Module;

/// The main CIRCT backend for compiling HWML to Verilog.
pub struct CirctBackend {
    // We'll add fields as needed
}

impl CirctBackend {
    /// Create a new CIRCT backend.
    pub fn new() -> Result<Self> {
        Ok(CirctBackend {})
    }

    /// Compile an HWML module to Verilog.
    pub fn compile_to_verilog<'db>(
        &self,
        db: &'db dyn salsa::Database,
        module: &Module<'db>,
    ) -> Result<String> {
        // Create MLIR context with CIRCT dialects
        let ctx = CirctContext::new()?;

        // Translate HWML module to CIRCT IR
        let mlir_module = translate::translate_module(&ctx, db, module)?;

        // Export to Verilog
        export::export_verilog(&mlir_module)
    }

    /// Compile an HWML module to CIRCT IR (for debugging/inspection).
    pub fn compile_to_mlir<'db>(
        &self,
        db: &'db dyn salsa::Database,
        module: &Module<'db>,
    ) -> Result<String> {
        let ctx = CirctContext::new()?;
        let mlir_module = translate::translate_module(&ctx, db, module)?;
        Ok(format!("{:?}", mlir_module))
    }
}

impl Default for CirctBackend {
    fn default() -> Self {
        Self::new().expect("Failed to create CIRCT backend")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_backend_creation() {
        let backend = CirctBackend::new();
        assert!(backend.is_ok());
    }
}
