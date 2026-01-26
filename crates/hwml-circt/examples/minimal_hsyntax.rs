//! Minimal example: Translate HSyntax (Zero, One, Xor) to CIRCT.
//!
//! This example demonstrates translating a simple hardware expression
//! like `Xor One Zero` into a CIRCT HW module named "Top".

use hwml_circt::{translate, CirctContext};
use hwml_core::syn::HSyntax;
use hwml_core::Database;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║    HWML CIRCT: Minimal HSyntax Translation Example        ║");
    println!("╚════════════════════════════════════════════════════════════╝");
    println!();

    // Create database for interning
    let db = Database::new();

    // Create CIRCT context
    println!("Step 1: Creating CIRCT context...");
    let ctx = CirctContext::new()?;
    println!("✓ Context created");
    println!();

    // Create a simple HSyntax expression: Xor One Zero
    println!("Step 2: Creating HSyntax expression...");
    let zero = HSyntax::zero_rc();
    let one = HSyntax::one_rc();

    // Create the xor primitive using the database for interning
    use hwml_core::syn::ConstantId;
    use hwml_support::salsa::FromWithDb;
    let xor_name = ConstantId::from_with_db(&db, "xor");
    let xor = HSyntax::hprim_rc(xor_name);

    // Xor is a binary operation, so we apply it to two arguments
    // In HSyntax, this would be: (Xor One) Zero
    let xor_one = HSyntax::happlication_rc(xor, one);
    let xor_one_zero = HSyntax::happlication_rc(xor_one, zero);

    println!("  Expression: (Xor One Zero)");
    println!("  Expected result: 1 XOR 0 = 1");
    println!();

    // Translate HSyntax to CIRCT
    println!("Step 3: Translating to CIRCT...");
    let mlir_module = translate::translate_hsyntax_to_top(&ctx, &db, &xor_one_zero)?;
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
    println!("║    Expected Verilog Output                                 ║");
    println!("╚════════════════════════════════════════════════════════════╝");
    println!();
    println!("module Top(");
    println!("  output out");
    println!(");");
    println!("  assign out = 1'b1 ^ 1'b0;  // = 1'b1");
    println!("endmodule");
    println!();

    Ok(())
}
