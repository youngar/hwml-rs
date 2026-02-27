//! Example: Translate a register expression to CIRCT.
//!
//! This example demonstrates translating a simple register operation
//! `$reg clk input` into a CIRCT seq.compreg operation.
//!
//! Note: The HApplication syntax is `f<T>(x)` where T is the module type.
//! For hardware primitives, we use `Syntax::prim_rc` and apply with
//! `Syntax::happlication_rc(module, module_ty, argument)`.

use hwml_circt::{translate, CirctContext};
use hwml_core::syn::Syntax;
use hwml_core::{ConstantId, Database};
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

    // Create a register expression: @reg<T>(clk, input)
    // For testing purposes, we'll use constants as placeholders for clock and input
    println!("Step 2: Creating Syntax expression...");

    // Create the clock signal (for simplicity, using '1' as a placeholder)
    let clk = Syntax::one_rc();
    // Create the data input (using '0')
    let input = Syntax::zero_rc();

    // Create the $reg primitive
    let reg_name = ConstantId::from_with_db(&db, "reg");
    let reg = Syntax::prim_rc(reg_name);

    // Create a placeholder type for the module type annotation
    // In a real scenario, this would be the actual hardware type ($Bit -> $Bit -> $Bit)
    let bit_ty = Syntax::bit_rc();
    let harrow_ty = Syntax::harrow_rc(
        bit_ty.clone(),
        Syntax::harrow_rc(bit_ty.clone(), bit_ty.clone()),
    );

    // Apply @reg<T>(clk): @reg applied to clock with type annotation
    let reg_clk = Syntax::happlication_rc(reg, harrow_ty.clone(), clk);
    // Apply (@reg<T>(clk))<T'>(input): the result applied to input
    let reg_clk_input = Syntax::happlication_rc(
        reg_clk,
        Syntax::harrow_rc(bit_ty.clone(), bit_ty.clone()),
        input,
    );

    println!("  Expression: @reg<$Bit → $Bit → $Bit>(1)<$Bit → $Bit>(0)");
    println!("  This creates a register clocked by '1' with '0' as data input");
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
