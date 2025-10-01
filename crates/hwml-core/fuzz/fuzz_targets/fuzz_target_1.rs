#![no_main]

use hwml_core::syn::{parse_syntax, print_syntax_to_string, Syntax};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|syntax: Syntax| {
    // Skip metavariables as they don't have a stable string representation
    // (they print as "?helpme" which can't be parsed back)
    if matches!(syntax, Syntax::Metavariable(_)) {
        return;
    }

    // Print the syntax to a string
    let printed = print_syntax_to_string(&syntax);

    // Parse it back
    match parse_syntax(&printed) {
        Ok(parsed) => {
            // Compare the original and parsed syntax
            // They should be equal
            assert_eq!(
                *parsed, syntax,
                "Round-trip failed!\nOriginal: {:?}\nPrinted: {}\nParsed: {:?}",
                syntax, printed, parsed
            );
        }
        Err(err) => {
            // If parsing fails, it's a bug - either in printing or parsing
            panic!(
                "Failed to parse printed syntax!\nOriginal: {:?}\nPrinted: {}\nError: {:?}",
                syntax, printed, err
            );
        }
    }
});
