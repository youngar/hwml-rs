//! Sequential (Seq) dialect operations.
//!
//! The Seq dialect provides operations for sequential logic:
//! - Registers
//! - Clocks
//! - Resets
//! - Finite state machines

use hwml_circt_sys::{MlirContextWrapper, MlirTypeWrapper};

/// Create a clock type for sequential logic.
pub fn clock_type(context: &MlirContextWrapper) -> MlirTypeWrapper {
    unsafe {
        let raw_type = hwml_circt_sys::seqClockTypeGet(context.as_raw());
        MlirTypeWrapper::from_raw(raw_type)
    }
}

/// Register types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegisterType {
    /// Simple register (no reset)
    Simple,
    /// Register with synchronous reset
    SyncReset,
    /// Register with asynchronous reset
    AsyncReset,
}

/// Reset polarity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResetPolarity {
    /// Active high reset
    ActiveHigh,
    /// Active low reset
    ActiveLow,
}

#[cfg(test)]
mod tests {
    use super::*;
    use hwml_circt_sys::MlirContextWrapper;

    #[test]
    fn test_register_types() {
        assert_eq!(RegisterType::Simple, RegisterType::Simple);
        assert_ne!(RegisterType::Simple, RegisterType::SyncReset);
    }

    #[test]
    fn test_reset_polarity() {
        assert_eq!(ResetPolarity::ActiveHigh, ResetPolarity::ActiveHigh);
        assert_ne!(ResetPolarity::ActiveHigh, ResetPolarity::ActiveLow);
    }

    #[test]
    fn test_clock_type() {
        let context = MlirContextWrapper::new();
        context.load_all_available_dialects();
        // Load the seq dialect
        unsafe {
            let seq_handle = hwml_circt_sys::mlirGetDialectHandle__seq__();
            hwml_circt_sys::mlirDialectHandleLoadDialect(seq_handle, context.as_raw());
        }
        let _ty = clock_type(&context);
        // Basic smoke test - clock type should be created
    }
}
