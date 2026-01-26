//! Basic example of using the CIRCT backend to compile HWML to Verilog.

use hwml_circt::CirctBackend;
use hwml_core::declaration::Module;
use hwml_core::Database;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("HWML CIRCT Backend Example");
    println!("===========================\n");

    // Create a database for interning
    let db = Database::new();

    // Create a simple HWML module
    let module = Module::new();

    println!("Created empty HWML module");
    println!("Declarations: {}", module.declarations.len());

    // Create the CIRCT backend
    println!("\nInitializing CIRCT backend...");
    let backend = CirctBackend::new()?;
    println!("✓ CIRCT backend initialized");

    // Compile to MLIR (for inspection)
    println!("\nCompiling to MLIR IR...");
    match backend.compile_to_mlir(&db, &module) {
        Ok(mlir) => {
            println!("✓ MLIR compilation successful");
            println!("\nMLIR Output:");
            println!("{}", mlir);
        }
        Err(e) => {
            println!("✗ MLIR compilation failed: {}", e);
        }
    }

    // Compile to Verilog
    println!("\nCompiling to Verilog...");
    match backend.compile_to_verilog(&db, &module) {
        Ok(verilog) => {
            println!("✓ Verilog compilation successful");
            println!("\nVerilog Output:");
            println!("{}", verilog);
        }
        Err(e) => {
            println!("✗ Verilog compilation failed: {}", e);
            println!("  (This is expected - Verilog export is not yet fully implemented)");
        }
    }

    Ok(())
}
