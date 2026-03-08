#![no_main]

use hwml_core::syn::{parse_syntax, print_syntax_to_string, Syntax};
use hwml_core::Database;
use libfuzzer_sys::fuzz_target;

/// Round trip syntax through the printer and parser.
fuzz_target!(|syntax: Syntax| {
    let db = Database::new();
    let printed = print_syntax_to_string(&db, &syntax);
    match parse_syntax(&db, &printed) {
        Ok(parsed) => {
            assert_eq!(
                *parsed, syntax,
                "Round-trip failed!\nOriginal: {:?}\nPrinted: {}\nParsed: {:?}",
                syntax, printed, parsed
            );
        }
        Err(err) => {
            panic!(
                "Failed to parse printed syntax!\nOriginal: {:?}\nPrinted: {}\nError: {:?}",
                syntax, printed, err
            );
        }
    }
});
