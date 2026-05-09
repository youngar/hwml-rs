# Wildcard Identifier Validation

## Overview

This document describes the implementation of wildcard (`_`) identifier validation in declaration contexts. The single underscore is a valid **pattern wildcard** but should **never** be used as a **declaration name**.

## Motivation

Pattern matching contexts allow `_` as a wildcard that matches any value:
```hwml
case x of
  | @Zero => ...
  | _ => ...        -- Valid: wildcard pattern
```

However, using `_` as a declaration name is nonsensical:
```hwml
def _ : Nat = @Zero    -- Invalid: what would this declare?
```

## Implementation

### 1. New Error Variant

**File:** `crates/hwml-core/src/name.rs`

Added a new variant to `NameError`:
```rust
pub enum NameError {
    ConsecutiveUnderscores(String),
    EmptyIdentifier,
    WildcardAsIdentifier,  // ← NEW
}
```

**Error message:** `"Wildcard '_' cannot be used as a declaration name"`

### 2. Validation in `surface_id_to_path`

**File:** `crates/hwml-elab/src/util.rs`

The `surface_id_to_path` function now checks each path segment:
```rust
pub fn surface_id_to_path<'db>(
    db: &'db dyn salsa::Database,
    id: &Id,
) -> Result<Vec<Name<'db>>, NameError> {
    // Check for wildcard pattern in any segment
    for segment in id.value.split('.').filter(|s| !s.is_empty()) {
        if segment == "_" {
            return Err(NameError::WildcardAsIdentifier);
        }
    }
    
    str_to_path(db, &id.value)
}
```

**Rejects:**
- `_` (single wildcard - valid in patterns, invalid as declaration name)
- `__` (double underscore - consecutive underscores)
- `___` (triple underscore - consecutive underscores)
- `foo__bar` (consecutive underscores anywhere)
- `Foo._` (wildcard in path)
- `Foo.__.Bar` (consecutive underscores in path)
- `_.Bar._` (multiple wildcards in path)

**Accepts:**
- `_+_` (mixfix infix operator - has content between underscores)
- `_foo` (prefix operator)
- `foo_` (postfix operator)
- `foo_bar` (single underscore separators are OK)
- `Foo.Bar` (normal qualified path)

### 3. Monadic Error Handling

All call sites now use a **monadic pattern** with pattern matching:
```rust
let path = match surface_id_to_path(db, &id) {
    Ok(p) if !p.is_empty() => p,
    Ok(_) => {
        // Handle empty path case
    }
    Err(e) => {
        // Report specific error with context
        errors.push(ElabError::NotInScope {
            name: format!("Invalid name '{}': {}", id.value, e),
            span: None,
        });
        return;
    }
};
```

**Benefits:**
1. ✅ Exhaustive error handling
2. ✅ Specific error messages with context
3. ✅ No silent failures
4. ✅ Distinguishes empty paths from validation errors

### 4. Updated Files

**Core validation:**
- `crates/hwml-core/src/name.rs` - New error variant
- `crates/hwml-elab/src/util.rs` - Validation logic + tests

**Error handling (12 call sites):**
- `crates/hwml-elab/src/program.rs` (9 locations)
- `crates/hwml-elab/src/scc_elab.rs` (2 locations)
- `crates/hwml-elab/src/elab/decl.rs` (already had proper handling)

## Testing

### Surface Syntax Tests

**File:** `crates/hwml-elab/src/util.rs::tests`

Eight comprehensive tests for `surface_id_to_path`:
1. ✅ Rejects single wildcard `_`
2. ✅ Rejects wildcard in path `Foo._.Bar`
3. ✅ Rejects double underscore `__`
4. ✅ Rejects triple underscore `___`
5. ✅ Rejects double underscore in path `Foo.__.Bar`
6. ✅ Accepts valid names `Foo.Bar`
7. ✅ Accepts mixfix names `_+_`
8. ✅ Rejects consecutive underscores `foo__bar`

### Core Syntax Tests

**File:** `crates/hwml-core/src/name.rs::tests`

Four tests for consecutive underscore validation:
1. ✅ Rejects `__` (double underscore)
2. ✅ Rejects `___` (triple underscore)
3. ✅ Rejects `______` (many underscores)
4. ✅ Accepts `_` (single wildcard - valid in patterns)

**File:** `crates/hwml-core/src/syn/parse.rs::tests`

Three parser tests:
1. ✅ Parser rejects `@__` in declarations
2. ✅ Parser rejects `@___` in declarations
3. ✅ Parser rejects `@foo__bar` in declarations

All 15 tests pass. ✅

## Error Messages

The implementation provides **specific, helpful error messages**:

```
Invalid def name '_': Wildcard '_' cannot be used as a declaration name
Invalid inductive name 'Foo._': Wildcard '_' cannot be used as a declaration name
Invalid namespace name '_': Wildcard '_' cannot be used as a declaration name
```

Each error includes:
- **Context** (what kind of declaration)
- **Invalid name** (the actual identifier)
- **Reason** (the NameError display message)

## Future Work

- Consider extending to detect other invalid patterns (e.g., reserved keywords)
- Add span information for better error reporting in the UI
- Integrate with the LSP for real-time validation
