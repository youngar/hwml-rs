# Fuzzing for hwml_core

This directory contains fuzzing targets for the `hwml_core` crate.

## Fuzz Targets

### `fuzz_core_roundtrip` - Syntax Round-trip Testing

This fuzzer tests the round-trip property of the Syntax printer and parser:
1. Generate an arbitrary `Syntax` node using the `arbitrary` crate
2. Print it to a string using `print_syntax_to_string()`
3. Parse it back using `parse_syntax()`
4. Compare the original and parsed syntax - they should be equal

These issues indicate that the printer and parser are not fully compatible, which is valuable information for improving the implementation.

## Running the Fuzzer

### Prerequisites

- Nightly Rust toolchain
- `cargo-fuzz` installed: `cargo install cargo-fuzz`

### Running

```bash
cd crates/hwml-core/fuzz
cargo fuzz run fuzz_core_roundtrip
```

To run for a specific amount of time:

```bash
cargo fuzz run fuzz_core_roundtrip -- -max_total_time=60
```

## Building Without Running

```bash
cargo build --manifest-path crates/hwml-core/fuzz/Cargo.toml
```

## Known Issues

The fuzzer currently skips `Metavariable` nodes because they print as `?helpme` which cannot be parsed back. This is expected behavior as metavariables are internal constructs.

## Future Work

- Fix the arrow symbol mismatch between printer and parser
- Ensure all syntax nodes can round-trip correctly
- Add more sophisticated fuzzing targets (e.g., type checking, evaluation)

