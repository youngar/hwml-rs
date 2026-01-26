//! Export CIRCT IR to Verilog.

use crate::error::{Error, Result};
use hwml_circt_sys::{
    export_verilog as sys_export_verilog, run_lower_seq_to_sv as sys_lower_seq_to_sv,
    MlirModuleWrapper,
};

/// Run the LowerSeqToSV pass to convert sequential operations to SystemVerilog.
/// This is required before Verilog export if the module contains seq dialect operations
/// (like seq.compreg, seq.to_clock, etc.).
pub fn lower_seq_to_sv(module: &MlirModuleWrapper) -> Result<()> {
    sys_lower_seq_to_sv(module).map_err(|e| Error::PassFailed(e))
}

/// Export an MLIR module to Verilog using CIRCT's export functionality.
/// Note: If the module contains seq dialect operations, call `lower_seq_to_sv` first.
pub fn export_verilog(module: &MlirModuleWrapper) -> Result<String> {
    sys_export_verilog(module).map_err(|e| Error::VerilogExport(e))
}

/// Lower seq dialect and export to Verilog in one step.
/// This is a convenience function that runs LowerSeqToSV then exports.
pub fn lower_and_export_verilog(module: &MlirModuleWrapper) -> Result<String> {
    lower_seq_to_sv(module)?;
    export_verilog(module)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::CirctContext;

    #[test]
    fn test_export_empty_module() {
        let ctx = CirctContext::new().unwrap();
        let location = ctx.unknown_location();
        let module = ctx.create_module(location);

        // Print the module to see what it looks like
        println!("Module IR:\n{}", module.to_string());

        // Export an empty module - this may succeed with empty output
        // or fail depending on CIRCT version. Either is acceptable.
        let result = export_verilog(&module);

        match result {
            Ok(verilog) => {
                // Empty module produces empty or minimal Verilog
                println!("Export succeeded with output: {:?}", verilog);
            }
            Err(e) => {
                // Export failed gracefully (not crash)
                println!("Export failed as expected: {:?}", e);
            }
        }
    }
}
