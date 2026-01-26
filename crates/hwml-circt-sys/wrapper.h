// CIRCT C API Headers
// These headers provide the C interface to CIRCT dialects and functionality

// Core CIRCT dialects for hardware description
#include "circt-c/Dialect/Comb.h" // Combinational logic operations
#include "circt-c/Dialect/HW.h"   // HardwareUniverse structural dialect
#include "circt-c/Dialect/SV.h"   // SystemVerilog dialect
#include "circt-c/Dialect/Seq.h"  // Sequential logic (registers, etc.)

// Conversion passes (e.g., LowerSeqToSV)
#include "circt-c/Conversion.h"

// Export functionality
#include "circt-c/ExportVerilog.h" // Export CIRCT IR to Verilog

// MLIR C API (needed for context, modules, operations)
#include "mlir-c/BuiltinAttributes.h"
#include "mlir-c/BuiltinTypes.h"
#include "mlir-c/IR.h"
#include "mlir-c/Pass.h" // Pass infrastructure
