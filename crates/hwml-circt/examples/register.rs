//! Example: Translate a register expression to CIRCT.
//!
//! This example demonstrates translating a simple register operation
//! `$reg clk input` into a CIRCT seq.compreg operation.

use hwml_circt::{translate, CirctContext};
use hwml_core::syn::{ConstantId, Syntax};
use hwml_core::Database;
use hwml_support::salsa::FromWithDb;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║    HWML CIRCT: Register Translation Example                ║");
    println!("╚════════════════════════════════════════════════════════════╝");
    println!();

    // Create database for interning
    let db = Database::new();

    // Create CIRCT context
    println!("Step 1: Creating CIRCT context...");
    let ctx = CirctContext::new()?;
    println!("✓ Context created");
    println!();

    // Create a register expression: $reg clk input
    // For testing purposes, we'll use constants as placeholders for clock and input
    println!("Step 2: Creating Syntax expression...");

    // Create the clock signal (for simplicity, using '1' as a placeholder)
    let clk = Syntax::one_rc();
    // Create the data input (using '0')
    let input = Syntax::zero_rc();

    // Create the $reg primitive
    let reg_name = ConstantId::from_with_db(&db, "reg");
    let reg = Syntax::hprim_rc(reg_name);

    // Apply $reg to clock and input: ($reg clk) input
    let reg_clk = Syntax::happlication_rc(reg, clk);
    let reg_clk_input = Syntax::happlication_rc(reg_clk, input);

    println!("  Expression: ($reg clk input)");
    println!("  This creates a register clocked by 'clk' with 'input' as data");
    println!();

    // Translate Syntax to CIRCT
    println!("Step 3: Translating to CIRCT...");
    let mlir_module = translate::translate_hsyntax_to_top(&ctx, &db, &reg_clk_input)?;
    println!("✓ Translation successful");
    println!();

    // Verify the module
    println!("Step 4: Verifying MLIR module...");
    if mlir_module.verify() {
        println!("✓ Module is valid");
    } else {
        println!("✗ Module verification failed");
        return Err("Module verification failed".into());
    }
    println!();

    // Print the MLIR
    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║    Generated MLIR IR                                       ║");
    println!("╚════════════════════════════════════════════════════════════╝");
    println!();
    println!("{}", mlir_module.to_string());
    println!();

    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║    Expected MLIR Operations                                ║");
    println!("╚════════════════════════════════════════════════════════════╝");
    println!();
    println!("The generated MLIR should contain:");
    println!("  - hw.constant 1 : i1  (clock placeholder)");
    println!("  - hw.constant 0 : i1  (input data)");
    println!("  - seq.compreg %input, %clk : i1  (register operation)");
    println!();

    Ok(())
}

