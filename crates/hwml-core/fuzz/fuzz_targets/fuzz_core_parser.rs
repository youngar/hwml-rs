#![no_main]

use hwml_core::syn::parse_syntax;
use hwml_core::Database;
use libfuzzer_sys::fuzz_target;

/// Fuzz the syntax parser.
fuzz_target!(|content: String| {
    let db = Database::new();
    let _ = parse_syntax(&db, &content);
});
