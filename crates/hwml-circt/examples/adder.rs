//! Example: Building a simple adder circuit.
//!
//! This example demonstrates how to:
//! 1. Create a CIRCT context with registered dialects
//! 2. Define hardware types (bit vectors)
//! 3. Plan for building hardware modules
//!
//! Note: Full module creation with operations is a work in progress.
//! This example shows the foundation for building hardware circuits.

use hwml_circt::{dialects, CirctContext};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║         HWML CIRCT Example: 8-bit Adder Types             ║");
    println!("╚════════════════════════════════════════════════════════════╝");
    println!();

    // Create CIRCT context
    println!("Creating CIRCT context...");
    let ctx = CirctContext::new()?;
    println!("✓ Context created with CIRCT dialects registered");
    println!();

    // Define types
    println!("Defining hardware types...");
    let i1_type = dialects::hw::bit_type(ctx.context());
    let i8_type = dialects::hw::int_type(ctx.context(), 8);
    let i16_type = dialects::hw::int_type(ctx.context(), 16);
    let i32_type = dialects::hw::int_type(ctx.context(), 32);

    println!("  - 1-bit type (bit):   {:?}", i1_type);
    println!("  - 8-bit type (byte):  {:?}", i8_type);
    println!("  - 16-bit type (half): {:?}", i16_type);
    println!("  - 32-bit type (word): {:?}", i32_type);
    println!();

    // Show what the module signature would look like
    println!("Planned module signature for Adder8:");
    println!("  Inputs:");
    println!("    - a: i8 (8-bit integer)");
    println!("    - b: i8 (8-bit integer)");
    println!("  Outputs:");
    println!("    - sum: i8 (8-bit integer)");
    println!();

    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║         Expected Verilog Output                            ║");
    println!("╚════════════════════════════════════════════════════════════╝");
    println!();
    println!("module Adder8(");
    println!("  input  [7:0] a,");
    println!("  input  [7:0] b,");
    println!("  output [7:0] sum");
    println!(");");
    println!("  assign sum = a + b;");
    println!("endmodule");
    println!();

    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║         Next Steps                                         ║");
    println!("╚════════════════════════════════════════════════════════════╝");
    println!();
    println!("To build complete hardware modules:");
    println!("  1. Implement OperationBuilder for hw.module operations");
    println!("  2. Add comb.add operation builder for addition");
    println!("  3. Implement hw.output operation for module outputs");
    println!("  4. Complete Verilog export in export.rs");
    println!();
    println!("Current status:");
    println!("  ✓ CIRCT context creation");
    println!("  ✓ Dialect registration (HW, Comb, Seq)");
    println!("  ✓ Type creation (integer types)");
    println!("  ⧗ Module creation (in progress)");
    println!("  ⧗ Operation builders (in progress)");
    println!("  ⧗ Verilog export (in progress)");
    println!();

    Ok(())
}
