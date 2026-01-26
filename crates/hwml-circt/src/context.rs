//! MLIR context management with CIRCT dialect registration.

use crate::error::Result;
use hwml_circt_sys::{MlirContextWrapper, MlirLocationWrapper, MlirModuleWrapper};

/// A wrapper around MLIR Context that ensures CIRCT dialects are registered.
pub struct CirctContext {
    context: MlirContextWrapper,
}

impl CirctContext {
    /// Create a new MLIR context and register CIRCT dialects.
    pub fn new() -> Result<Self> {
        let context = MlirContextWrapper::new();

        // Load all available dialects (includes standard MLIR dialects)
        context.load_all_available_dialects();

        // Register CIRCT dialects using the C API
        unsafe {
            Self::register_circt_dialects(&context)?;
        }

        Ok(CirctContext { context })
    }

    /// Register CIRCT dialects with the MLIR context.
    ///
    /// # Safety
    ///
    /// This function calls into the CIRCT C API. The context must be valid.
    unsafe fn register_circt_dialects(context: &MlirContextWrapper) -> Result<()> {
        use hwml_circt_sys::*;

        let ctx_raw = context.as_raw();

        // Get dialect handles from CIRCT
        // Note: The exact function names depend on CIRCT's C API version
        // These are the standard patterns used by CIRCT

        // Register HW dialect (hardware structural)
        let hw_handle = mlirGetDialectHandle__hw__();
        mlirDialectHandleLoadDialect(hw_handle, ctx_raw);
        mlirDialectHandleRegisterDialect(hw_handle, ctx_raw);

        // Register Comb dialect (combinational logic)
        let comb_handle = mlirGetDialectHandle__comb__();
        mlirDialectHandleLoadDialect(comb_handle, ctx_raw);
        mlirDialectHandleRegisterDialect(comb_handle, ctx_raw);

        // Register Seq dialect (sequential logic)
        let seq_handle = mlirGetDialectHandle__seq__();
        mlirDialectHandleLoadDialect(seq_handle, ctx_raw);
        mlirDialectHandleRegisterDialect(seq_handle, ctx_raw);

        // Load all available dialects (including SV which is needed for Verilog export)
        // This ensures the SV dialect is available even though it doesn't have a C API handle
        mlirContextLoadAllAvailableDialects(ctx_raw);

        Ok(())
    }

    /// Get a reference to the underlying MLIR context.
    pub fn context(&self) -> &MlirContextWrapper {
        &self.context
    }

    /// Create an unknown location for this context.
    pub fn unknown_location(&self) -> MlirLocationWrapper {
        MlirLocationWrapper::unknown(&self.context)
    }

    /// Create a new empty MLIR module.
    pub fn create_module(&self, location: MlirLocationWrapper) -> MlirModuleWrapper {
        unsafe {
            let module_raw = hwml_circt_sys::mlirModuleCreateEmpty(location.as_raw());
            MlirModuleWrapper::from_raw(module_raw)
        }
    }

    /// Get the raw MLIR context pointer (for FFI).
    ///
    /// # Safety
    ///
    /// The returned pointer is only valid as long as this CirctContext exists.
    pub unsafe fn to_raw(&self) -> hwml_circt_sys::MlirContext {
        self.context.as_raw()
    }
}

impl Default for CirctContext {
    fn default() -> Self {
        Self::new().expect("Failed to create CIRCT context")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_context_creation() {
        let ctx = CirctContext::new();
        assert!(ctx.is_ok());
    }
}
