//! Safe wrappers around MLIR context and basic operations.
//!
//! This module provides minimal safe wrappers around the MLIR C API,
//! specifically for what we need in the CIRCT backend.

use crate::*;

/// A safe wrapper around MlirContext.
///
/// This automatically manages the lifetime of the MLIR context,
/// destroying it when dropped.
pub struct MlirContextWrapper {
    raw: MlirContext,
}

impl MlirContextWrapper {
    /// Create a new MLIR context.
    pub fn new() -> Self {
        unsafe {
            let raw = mlirContextCreate();
            MlirContextWrapper { raw }
        }
    }

    /// Get the raw MLIR context pointer.
    ///
    /// # Safety
    ///
    /// The returned pointer is only valid as long as this wrapper exists.
    pub fn as_raw(&self) -> MlirContext {
        self.raw
    }

    /// Load all available dialects into this context.
    pub fn load_all_available_dialects(&self) {
        unsafe {
            mlirContextLoadAllAvailableDialects(self.raw);
        }
    }

    /// Get the number of loaded dialects.
    pub fn num_loaded_dialects(&self) -> isize {
        unsafe { mlirContextGetNumLoadedDialects(self.raw) }
    }
}

impl Default for MlirContextWrapper {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for MlirContextWrapper {
    fn drop(&mut self) {
        unsafe {
            mlirContextDestroy(self.raw);
        }
    }
}

/// A safe wrapper around MlirModule.
#[derive(Debug)]
pub struct MlirModuleWrapper {
    raw: MlirModule,
}

impl MlirModuleWrapper {
    /// Create a module wrapper from a raw MlirModule.
    ///
    /// # Safety
    ///
    /// The caller must ensure the MlirModule is valid.
    pub unsafe fn from_raw(raw: MlirModule) -> Self {
        MlirModuleWrapper { raw }
    }

    /// Get the raw MlirModule.
    pub fn as_raw(&self) -> MlirModule {
        self.raw
    }

    /// Get the module as an operation.
    pub fn as_operation(&self) -> MlirOperation {
        unsafe { mlirModuleGetOperation(self.raw) }
    }

    /// Verify the module.
    pub fn verify(&self) -> bool {
        unsafe {
            let op = self.as_operation();
            mlirOperationVerify(op)
        }
    }

    /// Print the module to a string.
    pub fn to_string(&self) -> String {
        unsafe {
            let op = self.as_operation();
            let mut result = String::new();

            // Use MLIR's string callback mechanism
            extern "C" fn string_callback(string: MlirStringRef, user_data: *mut std::ffi::c_void) {
                unsafe {
                    let result = &mut *(user_data as *mut String);
                    let slice = std::slice::from_raw_parts(string.data as *const u8, string.length);
                    if let Ok(s) = std::str::from_utf8(slice) {
                        result.push_str(s);
                    }
                }
            }

            mlirOperationPrintWithFlags(
                op,
                mlirOpPrintingFlagsCreate(),
                Some(string_callback),
                &mut result as *mut String as *mut std::ffi::c_void,
            );

            result
        }
    }
}

impl Drop for MlirModuleWrapper {
    fn drop(&mut self) {
        unsafe {
            mlirModuleDestroy(self.raw);
        }
    }
}

/// A safe wrapper around MlirLocation.
#[derive(Clone, Copy)]
pub struct MlirLocationWrapper {
    raw: MlirLocation,
}

impl MlirLocationWrapper {
    /// Create an unknown location.
    pub fn unknown(context: &MlirContextWrapper) -> Self {
        unsafe {
            let raw = mlirLocationUnknownGet(context.as_raw());
            MlirLocationWrapper { raw }
        }
    }

    /// Get the raw MlirLocation.
    pub fn as_raw(&self) -> MlirLocation {
        self.raw
    }
}

/// A safe wrapper around MlirType.
#[derive(Clone, Copy, Debug)]
pub struct MlirTypeWrapper {
    raw: MlirType,
}

impl MlirTypeWrapper {
    /// Create a type wrapper from a raw MlirType.
    ///
    /// # Safety
    ///
    /// The caller must ensure the MlirType is valid.
    pub unsafe fn from_raw(raw: MlirType) -> Self {
        MlirTypeWrapper { raw }
    }

    /// Get the raw MlirType.
    pub fn as_raw(&self) -> MlirType {
        self.raw
    }

    /// Create a function type.
    pub fn function(
        context: &MlirContextWrapper,
        inputs: &[MlirTypeWrapper],
        outputs: &[MlirTypeWrapper],
    ) -> Self {
        unsafe {
            let input_types: Vec<MlirType> = inputs.iter().map(|t| t.as_raw()).collect();
            let output_types: Vec<MlirType> = outputs.iter().map(|t| t.as_raw()).collect();
            let raw = mlirFunctionTypeGet(
                context.as_raw(),
                input_types.len() as isize,
                input_types.as_ptr(),
                output_types.len() as isize,
                output_types.as_ptr(),
            );
            MlirTypeWrapper { raw }
        }
    }
}

/// A safe wrapper around MlirValue.
#[derive(Clone, Copy)]
pub struct MlirValueWrapper {
    raw: MlirValue,
}

impl MlirValueWrapper {
    /// Create a value wrapper from a raw MlirValue.
    ///
    /// # Safety
    ///
    /// The caller must ensure the MlirValue is valid.
    pub unsafe fn from_raw(raw: MlirValue) -> Self {
        MlirValueWrapper { raw }
    }

    /// Get the raw MlirValue.
    pub fn as_raw(&self) -> MlirValue {
        self.raw
    }
}

/// A safe wrapper around MlirBlock.
pub struct MlirBlockWrapper {
    raw: MlirBlock,
    // Note: Blocks are owned by regions, so we don't destroy them
}

impl MlirBlockWrapper {
    /// Create a new empty block.
    pub fn new() -> Self {
        unsafe {
            let raw = mlirBlockCreate(0, std::ptr::null_mut(), std::ptr::null());
            MlirBlockWrapper { raw }
        }
    }

    /// Create a block wrapper from a raw MlirBlock.
    ///
    /// # Safety
    ///
    /// The caller must ensure the MlirBlock is valid.
    pub unsafe fn from_raw(raw: MlirBlock) -> Self {
        MlirBlockWrapper { raw }
    }

    /// Get the raw MlirBlock.
    pub fn as_raw(&self) -> MlirBlock {
        self.raw
    }

    /// Append an operation to this block.
    pub fn append_operation(&self, operation: MlirOperation) {
        unsafe {
            mlirBlockAppendOwnedOperation(self.raw, operation);
        }
    }
}

impl Default for MlirBlockWrapper {
    fn default() -> Self {
        Self::new()
    }
}

/// A safe wrapper around MlirRegion.
pub struct MlirRegionWrapper {
    raw: MlirRegion,
    // Note: Regions are owned by operations, so we don't destroy them
}

impl MlirRegionWrapper {
    /// Create a new empty region.
    pub fn new() -> Self {
        unsafe {
            let raw = mlirRegionCreate();
            MlirRegionWrapper { raw }
        }
    }

    /// Create a region wrapper from a raw MlirRegion.
    ///
    /// # Safety
    ///
    /// The caller must ensure the MlirRegion is valid.
    pub unsafe fn from_raw(raw: MlirRegion) -> Self {
        MlirRegionWrapper { raw }
    }

    /// Get the raw MlirRegion.
    pub fn as_raw(&self) -> MlirRegion {
        self.raw
    }

    /// Append a block to this region.
    pub fn append_block(&self, block: MlirBlock) {
        unsafe {
            mlirRegionAppendOwnedBlock(self.raw, block);
        }
    }
}

impl Default for MlirRegionWrapper {
    fn default() -> Self {
        Self::new()
    }
}

/// A safe wrapper around MlirAttribute.
#[derive(Clone, Copy)]
pub struct MlirAttributeWrapper {
    raw: MlirAttribute,
}

impl MlirAttributeWrapper {
    /// Create an attribute wrapper from a raw MlirAttribute.
    ///
    /// # Safety
    ///
    /// The caller must ensure the MlirAttribute is valid.
    pub unsafe fn from_raw(raw: MlirAttribute) -> Self {
        MlirAttributeWrapper { raw }
    }

    /// Get the raw MlirAttribute.
    pub fn as_raw(&self) -> MlirAttribute {
        self.raw
    }

    /// Create a string attribute.
    pub fn string(context: &MlirContextWrapper, value: &str) -> Self {
        unsafe {
            let c_str = std::ffi::CString::new(value).unwrap();
            let string_ref = MlirStringRef {
                data: c_str.as_ptr(),
                length: value.len(),
            };
            let raw = mlirStringAttrGet(context.as_raw(), string_ref);
            MlirAttributeWrapper { raw }
        }
    }

    /// Create an integer attribute.
    pub fn integer(ty: MlirTypeWrapper, value: i64) -> Self {
        unsafe {
            let raw = mlirIntegerAttrGet(ty.as_raw(), value);
            MlirAttributeWrapper { raw }
        }
    }

    /// Create a type attribute.
    pub fn type_attr(ty: MlirTypeWrapper) -> Self {
        unsafe {
            let raw = mlirTypeAttrGet(ty.as_raw());
            MlirAttributeWrapper { raw }
        }
    }

    /// Create an array attribute from a slice of attributes.
    pub fn array(context: &MlirContextWrapper, elements: &[MlirAttributeWrapper]) -> Self {
        unsafe {
            let raw_elements: Vec<MlirAttribute> = elements.iter().map(|a| a.as_raw()).collect();
            let raw = mlirArrayAttrGet(
                context.as_raw(),
                raw_elements.len() as isize,
                raw_elements.as_ptr(),
            );
            MlirAttributeWrapper { raw }
        }
    }

    /// Create a dense i32 array attribute from a slice of i32 values.
    /// This is used for attributes like `operandSegmentSizes`.
    pub fn dense_i32_array(context: &MlirContextWrapper, values: &[i32]) -> Self {
        unsafe {
            let raw =
                mlirDenseI32ArrayGet(context.as_raw(), values.len() as isize, values.as_ptr());
            MlirAttributeWrapper { raw }
        }
    }
}

/// Helper to create a named attribute.
pub fn create_named_attribute(
    context: &MlirContextWrapper,
    name: &str,
    attribute: MlirAttributeWrapper,
) -> MlirNamedAttribute {
    unsafe {
        let c_str = std::ffi::CString::new(name).unwrap();
        let string_ref = MlirStringRef {
            data: c_str.as_ptr(),
            length: name.len(),
        };
        let name_id = mlirIdentifierGet(context.as_raw(), string_ref);
        MlirNamedAttribute {
            name: name_id,
            attribute: attribute.as_raw(),
        }
    }
}

/// Helper for building MLIR operations.
pub struct OperationBuilder {
    name: String,
    location: MlirLocation,
    operands: Vec<MlirValue>,
    results: Vec<MlirType>,
    attributes: Vec<MlirNamedAttribute>,
    regions: Vec<MlirRegion>,
}

impl OperationBuilder {
    /// Create a new operation builder.
    pub fn new(name: &str, location: MlirLocationWrapper) -> Self {
        OperationBuilder {
            name: name.to_string(),
            location: location.as_raw(),
            operands: Vec::new(),
            results: Vec::new(),
            attributes: Vec::new(),
            regions: Vec::new(),
        }
    }

    /// Add operands to the operation.
    pub fn add_operands(mut self, operands: &[MlirValueWrapper]) -> Self {
        self.operands.extend(operands.iter().map(|v| v.as_raw()));
        self
    }

    /// Add result types to the operation.
    pub fn add_results(mut self, results: &[MlirTypeWrapper]) -> Self {
        self.results.extend(results.iter().map(|t| t.as_raw()));
        self
    }

    /// Add attributes to the operation.
    pub fn add_attributes(mut self, attributes: Vec<MlirNamedAttribute>) -> Self {
        self.attributes.extend(attributes);
        self
    }

    /// Add regions to the operation.
    pub fn add_regions(mut self, regions: Vec<MlirRegionWrapper>) -> Self {
        self.regions.extend(regions.iter().map(|r| r.as_raw()));
        self
    }

    /// Build the operation.
    pub fn build(self) -> Result<MlirOperation, String> {
        unsafe {
            let c_name = std::ffi::CString::new(self.name).unwrap();
            let name_ref = MlirStringRef {
                data: c_name.as_ptr(),
                length: c_name.as_bytes().len(),
            };

            let state = mlirOperationStateGet(name_ref, self.location);
            let mut state = state;

            // Add operands
            if !self.operands.is_empty() {
                mlirOperationStateAddOperands(
                    &mut state,
                    self.operands.len() as isize,
                    self.operands.as_ptr(),
                );
            }

            // Add results
            if !self.results.is_empty() {
                mlirOperationStateAddResults(
                    &mut state,
                    self.results.len() as isize,
                    self.results.as_ptr(),
                );
            }

            // Add attributes
            if !self.attributes.is_empty() {
                mlirOperationStateAddAttributes(
                    &mut state,
                    self.attributes.len() as isize,
                    self.attributes.as_ptr(),
                );
            }

            // Add regions
            if !self.regions.is_empty() {
                mlirOperationStateAddOwnedRegions(
                    &mut state,
                    self.regions.len() as isize,
                    self.regions.as_ptr(),
                );
            }

            let op = mlirOperationCreate(&mut state);
            // Check if operation is valid by checking if it's null
            // MLIR operations are pointers, so we can check for null
            if op.ptr.is_null() {
                Err("Failed to create operation".to_string())
            } else {
                Ok(op)
            }
        }
    }
}

/// Helper functions for working with operations.
pub fn operation_result(op: MlirOperation, index: isize) -> Result<MlirValueWrapper, String> {
    unsafe {
        let num_results = mlirOperationGetNumResults(op);
        if index >= num_results {
            return Err(format!(
                "Result index {} out of bounds (operation has {} results)",
                index, num_results
            ));
        }
        let value = mlirOperationGetResult(op, index);
        Ok(MlirValueWrapper::from_raw(value))
    }
}

/// Run the lowering passes required for Verilog export.
/// This includes LowerSeqToSV and PrepareForEmission passes.
pub fn run_lower_seq_to_sv(module: &MlirModuleWrapper) -> Result<(), String> {
    unsafe {
        // Get the context from the module
        let module_op = mlirModuleGetOperation(module.as_raw());
        let ctx = mlirOperationGetContext(module_op);

        // Create a pass manager
        let pm = mlirPassManagerCreate(ctx);

        // Get the top-level OpPassManager (cast PassManager to OpPassManager)
        let opm = mlirPassManagerGetAsOpPassManager(pm);

        // Add LowerSeqToSV pass - converts seq dialect to SV
        let lower_seq_pass = mlirCreateCIRCTConversionLowerSeqToSV();
        mlirOpPassManagerAddOwnedPass(opm, lower_seq_pass);

        // Add PrepareForEmission pass - prepares for Verilog output
        let prepare_pass = mlirCreateCIRCTConversionPrepareForEmission();
        mlirOpPassManagerAddOwnedPass(opm, prepare_pass);

        // Run the pass manager
        let result = mlirPassManagerRunOnOp(pm, module_op);

        // Destroy the pass manager
        mlirPassManagerDestroy(pm);

        // Check result
        if result.value != 0 {
            Err("Lowering passes failed".to_string())
        } else {
            Ok(())
        }
    }
}

/// Export a module to Verilog using CIRCT's export functionality.
///
/// Returns the Verilog code as a String, or an error message if export fails.
pub fn export_verilog(module: &MlirModuleWrapper) -> Result<String, String> {
    use std::os::raw::c_void;

    // String to collect the output
    let mut output = String::new();

    // Callback function that appends string chunks to our output
    unsafe extern "C" fn string_callback(string_ref: MlirStringRef, user_data: *mut c_void) {
        let output = &mut *(user_data as *mut String);
        let slice = std::slice::from_raw_parts(string_ref.data as *const u8, string_ref.length);
        if let Ok(s) = std::str::from_utf8(slice) {
            output.push_str(s);
        }
    }

    // Verify the module first
    let module_op = unsafe { mlirModuleGetOperation(module.as_raw()) };
    let is_valid = unsafe { mlirOperationVerify(module_op) };

    if !is_valid {
        return Err(
            "Module verification failed before Verilog export (check stderr for details)"
                .to_string(),
        );
    }

    // Call the CIRCT export function
    let result = unsafe {
        mlirExportVerilog(
            module.as_raw(),
            Some(string_callback),
            &mut output as *mut String as *mut c_void,
        )
    };

    // Check if export succeeded
    // Note: CIRCT may return non-zero even when producing valid output (e.g., for warnings)
    // So we check if we got output first
    if !output.is_empty() {
        Ok(output)
    } else if result.value != 0 {
        Err(format!(
            "Verilog export failed with code: {} (check stderr for MLIR diagnostics)",
            result.value
        ))
    } else {
        Err("Verilog export produced no output".to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_context_creation() {
        let ctx = MlirContextWrapper::new();
        // Context should be created successfully
        drop(ctx);
    }

    #[test]
    fn test_load_dialects() {
        let ctx = MlirContextWrapper::new();
        ctx.load_all_available_dialects();
        // Should have loaded some dialects
        assert!(ctx.num_loaded_dialects() > 0);
    }
}
