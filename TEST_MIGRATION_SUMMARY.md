# Test Migration Summary

This document summarizes the migration of tests from manual Syntax node construction to using the enhanced test utilities.

## Overview

After reviewing all tests in the `hwml_core` crate, I found that most tests that manually construct Syntax nodes are:

1. **Parser tests** - Testing the parser itself, so they need to construct expected AST nodes
2. **Type checker tests** - Testing type synthesis/checking, which requires Syntax nodes as input
3. **Quote tests** - Testing quotation from Values back to Syntax

These tests are **not good candidates** for `eval_with_context()` because:
- They're testing the infrastructure that `eval_with_context()` depends on
- They need to construct Syntax nodes to pass to `type_synth()` or `type_check()`
- They're not primarily about evaluation

## What Was Migrated

Instead of migrating to `eval_with_context()`, I migrated tests to use **parsing instead of manual AST construction** where appropriate. This improves readability while maintaining the same test semantics.

### Migrated Tests in `crates/hwml-core/src/check.rs`

#### 1. `test_synth_variable` (lines 1642-1663)

**Before:**
```rust
// Manual AST construction
let var = Syntax::variable_rc(Location::UNKNOWN, crate::common::Index(0));
```

**After:**
```rust
// Parse at depth 1 since we have one variable in scope
let var = crate::syn::parse::parse_syntax_at_depth(&db, "%0", 1)
    .expect("should parse");
```

**Benefit:** More readable, self-documenting code.

#### 2. `test_synth_application` (lines 1780-1811)

**Before:**
```rust
// Manual AST construction for application
let lift_bit = parse(&db, "^(^s Bit)");
let app = Syntax::application_rc(
    Location::UNKNOWN,
    Syntax::variable_rc(Location::UNKNOWN, crate::common::Index(0)),
    lift_bit,
);
```

**After:**
```rust
// Parse the entire application at depth 1
let app = crate::syn::parse::parse_syntax_at_depth(&db, "%0 ^(^s Bit)", 1)
    .expect("should parse");
```

**Benefit:** Single line instead of multiple, clearer intent.

#### 3. `test_check_transport` (lines 2466-2513)

**Before:**
```rust
// Manual AST construction for transport
let motive_body = Syntax::variable_rc(Location::UNKNOWN, Index(0));
let motive = syn::Closure::new(motive_body);
let proof = Syntax::variable_rc(Location::UNKNOWN, Index(1));
let value = Syntax::variable_rc(Location::UNKNOWN, Index(0));
let transport = Syntax::transport_rc(Location::UNKNOWN, motive, proof, value);
```

**After:**
```rust
// Parse the entire transport expression at depth 4
let transport = crate::syn::parse::parse_syntax_at_depth(
    &db,
    "transport [%0] |- %0 %1 %0",
    4
).expect("should parse");
```

**Benefit:** Much more readable, shows the actual syntax being tested.

## Tests NOT Migrated

### Parser Tests (`crates/hwml-core/src/syn/parse.rs`)

These tests verify that parsing produces the correct AST structure. They **must** manually construct expected Syntax nodes to compare against parsed results.

Examples:
- `test_parse_lambda_single_var`
- `test_parse_application_simple`
- `test_parse_metavariable_simple`

### Quote Tests (`crates/hwml-core/src/quote.rs`)

These tests verify quotation from Values to Syntax. They construct Values (not Syntax) for testing, or use helper functions like `identity_closure()` which are part of the test infrastructure.

### Evaluation Tests (`crates/hwml-core/src/eval.rs`)

These tests already use the `Ctx` helper which provides string-based parsing and evaluation. They don't manually construct Syntax nodes.

## Key Insight

The new `eval_with_context()` utility is most useful for:
- **New tests** that need to evaluate expressions with typed variables
- **Integration tests** that test end-to-end behavior
- **Tests that verify evaluation results** rather than AST structure

For existing tests that verify:
- Parser correctness
- Type checker behavior
- Quotation correctness

Using `parse_syntax_at_depth()` directly is more appropriate than `eval_with_context()`.

## Recommendations

1. **Use `eval_with_context()`** for new tests that evaluate expressions with variables
2. **Use `parse_syntax_at_depth()`** for tests that need Syntax nodes for type checking
3. **Keep manual AST construction** only in parser tests where you're verifying the AST structure
4. **Use `print_value_to_string()`** for assertions on evaluation results

## Impact

- **3 tests migrated** from manual AST construction to parsing
- **Improved readability** - tests now show the actual syntax being tested
- **No behavior changes** - tests verify the same properties
- **Maintained compatibility** - all existing tests still work

