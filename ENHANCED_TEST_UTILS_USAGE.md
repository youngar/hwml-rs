# Enhanced Test Utilities Usage Guide

This document demonstrates how to use the enhanced test utilities in `crates/hwml-core/src/test_utils.rs`.

## Overview

The enhanced test utilities provide:

1. **String-based value printing** - Convert values to strings for assertions
2. **Context-based evaluation** - Declare typed variables using type theory notation
3. **Convenience wrappers** - Auto-manage Database for common test cases

## New Functions

### 1. `print_value_to_string()`

Quote a value at a type and print it to a string for test assertions.

```rust
use hwml_core::test_utils::*;

let db = Database::default();
let global = load_prelude(&db, NAT_PRELUDE);

let val = eval_str(&db, &global, "[@Succ [@Zero]]");
let ty = eval_str(&db, &global, "#[@Nat]");

assert_eq!(print_value_to_string(&db, &global, &val, &ty), "[@Succ [@Zero]]");
```

### 2. `print_type_to_string()`

Quote a type and print it to a string.

```rust
let ty = eval_str(&db, &global, "#[@Nat]");
assert_eq!(print_type_to_string(&db, &global, &ty), "#[@Nat]");
```

### 3. `eval_with_context()`

Evaluate expressions with typed variables using the syntax: `context |- expression`

**Context syntax:** `%name : type; %name2 : type2; ... |- expression`

Variables are referenced by position (0-indexed) in the expression:
- First variable in context → `%0`
- Second variable in context → `%1`
- etc.

```rust
let db = Database::default();
let global = load_prelude(&db, NAT_PRELUDE);

// Single variable
let val = eval_with_context(&db, &global, "%n : #[@Nat] |- [@Succ %0]");

// Multiple variables
let val = eval_with_context(
    &db,
    &global,
    "%n : #[@Nat]; %m : #[@Nat] |- [@Succ %0]"
);

// Empty context
let val = eval_with_context(&db, &global, " |- [@Zero]");

// Dependent types
let val = eval_with_context(
    &db,
    &global,
    "%n : #[@Nat]; %a : U0 |- #[@Vec %1 %0]"
);
```

### 4. `eval_with_prelude_and_context()`

Convenience wrapper that loads a prelude and evaluates with context.

```rust
let db = Database::default();
let val = eval_with_prelude_and_context(
    &db,
    NAT_PRELUDE,
    "%n : #[@Nat] |- [@Succ %0]"
);
```

### 5. `eval_with_prelude()`

Convenience wrapper for simple expressions with a prelude.

```rust
let db = Database::default();
let val = eval_with_prelude(&db, NAT_PRELUDE, "[@Zero]");
```

## Complete Example

```rust
use hwml_core::test_utils::*;
use hwml_core::Database;

#[test]
fn test_nat_operations() {
    let db = Database::default();
    let global = load_prelude(&db, NAT_PRELUDE);
    
    // Evaluate with context
    let val = eval_with_context(
        &db,
        &global,
        "%n : #[@Nat] |- [@Succ %0]"
    );
    
    // Print for assertion
    let ty = eval_str(&db, &global, "#[@Nat]");
    let printed = print_value_to_string(&db, &global, &val, &ty);
    
    // Variables print as !0 (unbound) when quoted at depth 0
    assert_eq!(printed, "[@Succ !0]");
}
```

## Benefits

1. **Self-documenting tests** - Context syntax makes variable types explicit
2. **Less boilerplate** - No manual Database or Environment management
3. **String-based assertions** - Easy to read and write test expectations
4. **Type safety** - Variables have proper types, not dummy U0

## Migration from Old Style

**Before:**
```rust
let db = Database::default();
let global = load_prelude(&db, NAT_PRELUDE);
let val = eval_str_at_depth(&db, &global, "[@Succ %0]", 1);
// Variables have dummy type U0
```

**After:**
```rust
let db = Database::default();
let val = eval_with_prelude_and_context(
    &db,
    NAT_PRELUDE,
    "%n : #[@Nat] |- [@Succ %0]"
);
// Variable %n has proper type #[@Nat]
```

## Notes

- Variable names in the context (e.g., `%n`, `%m`) are for documentation only
- Variables are referenced by position in the expression (e.g., `%0`, `%1`)
- The context can be empty: ` |- expression`
- Types in the context can reference earlier variables (dependent types)

