// Standalone test to verify module printing works correctly
// Run with: rustc --edition 2021 test_print_module.rs --crate-type bin -L target/debug/deps -L target/debug --extern hwml_core=target/debug/libhwml_core.rlib --extern hwml_db=target/debug/libhwml_db.rlib

fn main() {
    let db = hwml_db::HwmlDatabase::new();
    
    // Test input with a type constructor that has parameters and indices
    let input = r#"
tcon @Vec (%A : (U0 : UniverseType)) : (%n : #[@Nat]) -> (U0 : UniverseType) where
  dcon @VNil : #[@Vec %A @Zero]
  dcon @VCons (%n : #[@Nat]) (%x : %A) (%xs : #[@Vec %A %n]) : #[@Vec %A (@Succ %n)];

tcon @Nat : -> (U0 : UniverseType) where
  dcon @Zero : #[@Nat]
  dcon @Succ (%n : #[@Nat]) : #[@Nat];
"#;

    match hwml_core::syn::parse_module(&db, input) {
        Ok(module) => {
            println!("Module:");
            println!("{}", hwml_core::syn::print::print_module_to_string(&db, &module));
        }
        Err(e) => {
            println!("Parse error: {:#?}", e);
        }
    }
}
