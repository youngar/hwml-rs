//! Demonstration of eval and quote functionality in hwml-core.
//!
//! This example can be run with:
//! ```
//! cargo run --package hwml_core --example eval_quote_demo
//! ```

use hwml_core::examples::*;

fn main() {
    println!("╔═══════════════════════════════════════════════════════════════╗");
    println!("║  HWML-Core: Eval and Quote Examples                          ║");
    println!("╚═══════════════════════════════════════════════════════════════╝");
    println!();
    println!("This demo shows how to use the eval and quote functions to:");
    println!("  • Evaluate syntax terms to semantic values");
    println!("  • Quote semantic values back to normalized syntax");
    println!("  • Perform normalization (eval + quote)");
    println!();
    
    run_all_examples();
    
    println!();
    println!("╔═══════════════════════════════════════════════════════════════╗");
    println!("║  Demo Complete!                                               ║");
    println!("╚═══════════════════════════════════════════════════════════════╝");
}

