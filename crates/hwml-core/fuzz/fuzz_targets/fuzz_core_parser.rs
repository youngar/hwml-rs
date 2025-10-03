#![no_main]

use hwml_core::syn::parse_syntax;
use libfuzzer_sys::fuzz_target;

/// Fuzz the syntax parser.
fuzz_target!(|content: String| {
    parse_syntax(&content);
});
