# Salsa-Based SourceRange Architecture

HWML uses a Salsa-interned location system that provides MLIR-style provenance
tracking with rich diagnostic capabilities. The Core IR treats locations as
opaque identifiers and never inspects their contents, while the elaborator and
error reporting code can query Salsa to extract source file information and
exact code snippets.

## Core Types

The location system is built around three main types, all defined in
`hwml-support/src/location.rs`.

`SourceFile` is a Salsa input that represents a source file with its path and
text. When the file's text changes, Salsa will invalidate anything that depends
on it.

`LocationData` is an enum with two variants: `Physical { file, start, end }`
for real source code spans, and `Unknown` for synthetic or generated code.

`SourceRange` is a Salsa-interned ID that wraps LocationData. It's Copy-able and
lightweight (just a u32 internally), but can be queried through Salsa to get
the full data.

## None

The special constant `None` is a sentinel value (ID 0) that
doesn't require a database. It's used for quotation (semantic to syntax
conversion), elaboration (fresh metavariables), renaming (unification
inversion), and tests (programmatic AST construction). Salsa guarantees
deterministic interning, so `LocationData::Unknown` will always get ID 0, making
this safe.

## Usage

In the parser, create a SourceFile and use `SourceRange::physical()` to create
locations for parsed syntax:

```rust
let file = SourceFile::new(db, path, text);
let loc = SourceRange::physical(db, file, start_offset, end_offset);
let syntax = Syntax::lambda_rc(loc, body);
```

In the Core IR (tests, quotation, etc.), use `None` directly. No
database needed:

```rust
let loc = None;
let syntax = Syntax::universe_rc(loc, level);
```

In the elaborator, use `location.snippet(db)` to extract the exact source code
that caused an error, or `location.display(db)` to get file and position info:

```rust
match core_error {
    TypeError { loc, expected, got } => {
        if let Some(snippet) = loc.snippet(db) {
            eprintln!("Error in code: `{}`", snippet);
        }
        eprintln!("SourceRange: {}", loc.display(db));
    }
}
```

## Benefits

SourceRange metadata changes don't invalidate Core IR caches, keeping Salsa happy.
Core IR pattern matching ignores locations, keeping the semantics mathematically
pure. The elaborator can extract exact source snippets for errors, giving rich
diagnostics. SourceRange changes don't trigger full recompilation. And
`None` works without a database, making tests easy to write.

## Implementation Details

The core location types are defined in `hwml-support/src/location.rs`.
`hwml-core/src/common.rs` re-exports `SourceRange`, and `hwml-elab/src/lib.rs`
also re-exports the location types for convenience.

The `SourceRange` type is automatically integrated into any Salsa database that
includes the `hwml-support` jar. No manual setup required.

Tests can use `None` without creating a database:

```rust
#[test]
fn test_type_checking() {
    let loc = None;
    let term = Syntax::lambda_rc(loc, body);
    // ... test logic
}
```

For tests that need real locations, create a database and use
`SourceRange::physical()`:

```rust
#[test]
fn test_error_messages() {
    let db = Database::new();
    let file = SourceFile::new(&db, "test.hwml".into(), "λx. x".into());
    let loc = SourceRange::physical(&db, file, 0, 6);
    // ... test logic
}
```

## Future Work

We should add line and column information to `LocationData::Physical` at some
point. It would also be nice to implement `Display` for better error messages,
add source highlighting in diagnostics, and support for macro expansion
tracking.

