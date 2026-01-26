//! HardwareUniverse (HW) dialect operations.
//!
//! The HW dialect represents structural hardware: modules, ports, instances, etc.

use hwml_circt_sys::{MlirContextWrapper, MlirTypeWrapper};

/// Create an integer type with the specified bit width.
pub fn int_type(context: &MlirContextWrapper, width: u32) -> MlirTypeWrapper {
    unsafe {
        let raw_type = hwml_circt_sys::mlirIntegerTypeGet(context.as_raw(), width);
        MlirTypeWrapper::from_raw(raw_type)
    }
}

/// Create a 1-bit type (commonly used for single wires).
pub fn bit_type(context: &MlirContextWrapper) -> MlirTypeWrapper {
    int_type(context, 1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use hwml_circt_sys::MlirContextWrapper;

    #[test]
    fn test_int_type() {
        let context = MlirContextWrapper::new();
        let ty = int_type(&context, 32);
        // Basic smoke test
    }

    #[test]
    fn test_bit_type() {
        let context = MlirContextWrapper::new();
        let ty = bit_type(&context);
        // Basic smoke test
    }
}
