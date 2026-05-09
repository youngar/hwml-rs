# Mixfix-Aware Name Conversion Implementation Plan

## Problem Statement

Currently, all identifier-to-`Name` conversions use `Fixity::Closed` and treat the entire string as a single `Atom`. This is incorrect for mixfix operators where underscores denote argument positions.

### Examples of Incorrect Behavior

```rust
// Current (WRONG):
"_+_"   → Name { fixity: Closed, parts: [Atom("_+_")] }
"_foo"  → Name { fixity: Closed, parts: [Atom("_foo")] }
"foo_"  → Name { fixity: Closed, parts: [Atom("foo_")] }

// Expected (CORRECT):
"_+_"   → Name { fixity: Infix,   parts: [Atom("+")] }
"_foo"  → Name { fixity: Prefix,  parts: [Atom("foo")] }
"foo_"  → Name { fixity: Postfix, parts: [Atom("foo")] }
"_foo_bar_" → Name { fixity: Infix, parts: [Atom("foo"), Atom("bar")] }
```

### Impact

Since datatypes, constructors, and other definitions can use mixfix naming (e.g., `inductive _Vec_ A n : Type`), **all namespace segments must correctly parse fixity**.

---

## Phase 1: Core API Implementation

### 1.1 Add `str_to_name` Function in `hwml-core/src/name.rs`

**Location**: `crates/hwml-core/src/name.rs`

Add a new public function that converts a UTF-8 string segment to a `Name` with correct fixity.

**Error Handling**: Returns `Result` to reject malformed identifiers with consecutive underscores.

```rust
/// Error type for invalid identifier formats.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NameError {
    /// Identifier contains consecutive underscores (e.g., "foo__bar", "___")
    ConsecutiveUnderscores(String),
    /// Empty identifier string
    EmptyIdentifier,
}

impl std::fmt::Display for NameError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NameError::ConsecutiveUnderscores(s) => {
                write!(f, "Identifier '{}' contains consecutive underscores", s)
            }
            NameError::EmptyIdentifier => write!(f, "Identifier cannot be empty"),
        }
    }
}

impl std::error::Error for NameError {}

/// Convert a UTF-8 string identifier to a Name with correct Fixity.
///
/// Mixfix parsing rules (Agda-style):
/// - `_foo_bar_` → Infix with parts ["foo", "bar"]
/// - `_foo`      → Prefix with parts ["foo"]
/// - `foo_`      → Postfix with parts ["foo"]
/// - `foo`       → Closed with parts ["foo"]
/// - `my_var`    → Closed with parts ["my", "var"] (can be used in mixfix form)
/// - `_`         → Closed with parts ["_"] (special case: pattern wildcard)
///
/// # Errors
///
/// Returns `Err(NameError::ConsecutiveUnderscores)` if the identifier contains
/// consecutive underscores (e.g., `foo__bar`, `___`).
///
/// Returns `Err(NameError::EmptyIdentifier)` if the string is empty.
pub fn str_to_name<'db>(db: &'db dyn salsa::Database, text: &str) -> Result<Name<'db>, NameError> {
    // Validate: reject empty strings
    if text.is_empty() {
        return Err(NameError::EmptyIdentifier);
    }

    // Validate: reject consecutive underscores
    if text.contains("__") {
        return Err(NameError::ConsecutiveUnderscores(text.to_string()));
    }

    // Special case: standalone underscore (pattern wildcard)
    if text == "_" {
        let word = Word::new(db, "_");
        let atom = Atom::new(word);
        return Ok(Name::new(db, Fixity::Closed, Box::from([atom])));
    }

    let starts_with_underscore = text.starts_with('_');
    let ends_with_underscore = text.ends_with('_');

    // Determine fixity based on underscore positions
    let fixity = match (starts_with_underscore, ends_with_underscore) {
        (true, true)   => Fixity::Infix,
        (true, false)  => Fixity::Prefix,
        (false, true)  => Fixity::Postfix,
        (false, false) => Fixity::Closed,
    };

    // Split by underscore to extract name parts (atoms)
    // Since we validated no consecutive underscores, no empty segments will appear
    let parts: Box<[Atom<'db>]> = text
        .split('_')
        .filter(|s| !s.is_empty())
        .map(|part| Atom::new(Word::new(db, part)))
        .collect();

    // Defensive: this should never happen after validation
    debug_assert!(!parts.is_empty(), "str_to_name produced empty parts after validation");

    Ok(Name::new(db, fixity, parts))
}
```

### 1.2 Update `FromWithDb<&str>` for `Name`

Replace the current `FromWithDb` implementation in `hwml-core/src/name.rs` (line 84-94):

```rust
impl<'db> FromWithDb<'db, &str> for Name<'db> {
    fn from_with_db<Db>(db: &'db Db, value: &str) -> Self
    where
        Db: salsa::Database + ?Sized,
    {
        // Panic on malformed identifiers - these should be caught by the lexer/parser
        str_to_name(db, value).expect("Invalid identifier passed to FromWithDb")
    }
}

impl<'db> FromWithDb<'db, String> for Name<'db> {
    fn from_with_db<Db>(db: &'db Db, value: String) -> Self
    where
        Db: salsa::Database + ?Sized,
    {
        str_to_name(db, &value).expect("Invalid identifier passed to FromWithDb")
    }
}
```

**Note**: Remove the existing `FromWithDb<T> where T: IntoWithDb<Atom>` impl to avoid conflicts.

**Design Decision**: `FromWithDb` panics on validation errors because:
1. The lexer should prevent malformed identifiers from reaching this point
2. If a malformed identifier reaches here, it's a compiler bug, not a user error
3. Explicit call sites can use `str_to_name()` directly for proper error handling

---

## Phase 2: Update All Conversion Functions

### 2.1 `hwml-elab/src/util.rs`

**File**: `crates/hwml-elab/src/util.rs`

Update `str_to_path` (line 7-16) to use the standard API and propagate errors:

```rust
/// Convert a UTF-8 string to a path of Names.
/// Handles dotted paths like "Foo.Bar.Baz" -> [Foo, Bar, Baz]
/// Returns an empty vector for empty strings or strings containing only dots.
///
/// # Errors
/// Returns error if any path segment contains consecutive underscores.
pub fn str_to_path<'db>(
    db: &'db dyn salsa::Database,
    text: &str
) -> Result<Vec<Name<'db>>, hwml_core::NameError> {
    text.split('.')
        .filter(|seg| !seg.is_empty())
        .map(|seg| hwml_core::str_to_name(db, seg))
        .collect()
}
```

Update `surface_id_to_path` to propagate the error:

```rust
pub fn surface_id_to_path<'db>(
    db: &'db dyn salsa::Database,
    id: &Id
) -> Result<Vec<Name<'db>>, hwml_core::NameError> {
    str_to_path(db, &id.value)
}
```

### 2.2 `hwml-elab/src/names.rs`

**File**: `crates/hwml-elab/src/names.rs`

Update `str_to_simple_qname` (line 15-24) to propagate errors:

```rust
pub fn str_to_simple_qname<'db>(
    db: &'db dyn salsa::Database,
    namespace: Option<QualifiedName<'db>>,
    segment: &str,
) -> Result<QualifiedName<'db>, hwml_core::NameError> {
    let name = hwml_core::str_to_name(db, segment)?;
    Ok(QualifiedName::new(db, namespace, name))
}
```

### 2.3 `hwml-core/src/syn/parse.rs`

**File**: `crates/hwml-core/src/syn/parse.rs`

Update `p_qname` function (line 436-444):

```rust
fn p_qname<'db>(db: &'db dyn salsa::Database, name_str: &str) -> QualifiedName<'db> {
    let components: Vec<&str> = name_str.split('/').collect();
    let mut qname = None;
    for component in components {
        let name = hwml_core::str_to_name(db, component);  // ✅ Use standard API
        qname = Some(QualifiedName::new(db, qname, name));
    }
    qname.unwrap()
}
```

### 2.4 `hwml-elab/src/elab/expr.rs`

**File**: `crates/hwml-elab/src/elab/expr.rs`

Update field name construction (line 139-142):

```rust
// OLD:
let word = hwml_core::Word::new(db, *field_str);
let atom = hwml_core::Atom::new(word);
let field_name = Name::new(db, hwml_core::Fixity::Closed, Box::from([atom]));

// NEW:
let field_name = hwml_core::str_to_name(db, *field_str);  // ✅ Use standard API
```

### 2.5 `hwml-elab/tests/elab_tests.rs`

**File**: `crates/hwml-elab/tests/elab_tests.rs`

Update `make_qn` helper function (line 497-506):

```rust
fn make_qn<'db>(db: &'db hwml_core::TestDatabase, name: &str) -> hwml_core::QualifiedName<'db> {
    let name = hwml_core::str_to_name(db, name);  // ✅ Use standard API
    hwml_core::QualifiedName::new(db, None, name)
}
```

---

## Phase 3: Enforcement - Make Direct Construction Impossible

### 3.1 Make `Name::new` Construction Private (Future Enhancement)

**Consideration**: To truly enforce that all conversions go through the standard API, we could:
1. Make `Name::new` take a `pub(crate)` visibility
2. Add a `#[doc(hidden)]` marker
3. Add compile-time checks using type-level restrictions

**However**, this may break internal uses in `hwml-core` that legitimately need direct construction. Defer this to a future refactor.

### 3.2 Deprecation Strategy

Mark the old `FromWithDb` implementation for `Name` as deprecated:

```rust
#[deprecated(since = "0.1.0", note = "Use hwml_core::str_to_name instead")]
impl<'db, T> FromWithDb<'db, T> for Name<'db>
where
    T: IntoWithDb<'db, Atom<'db>>,
{
    // ... existing implementation
}
```

---

## Phase 4: Testing Strategy

### 4.1 Unit Tests for `str_to_name`

Add tests in `crates/hwml-core/src/name.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::TestDatabase;

    #[test]
    fn test_str_to_name_closed() {
        let db = TestDatabase::default();
        let name = str_to_name(&db, "foo");
        assert_eq!(name.fixity(&db), Fixity::Closed);
        assert_eq!(name.len(&db), 1);
        assert_eq!(name.parts(&db)[0].text(&db), "foo");
    }

    #[test]
    fn test_str_to_name_infix() {
        let db = TestDatabase::default();
        let name = str_to_name(&db, "_+_");
        assert_eq!(name.fixity(&db), Fixity::Infix);
        assert_eq!(name.len(&db), 1);
        assert_eq!(name.parts(&db)[0].text(&db), "+");
    }

    #[test]
    fn test_str_to_name_prefix() {
        let db = TestDatabase::default();
        let name = str_to_name(&db, "_not");
        assert_eq!(name.fixity(&db), Fixity::Prefix);
        assert_eq!(name.len(&db), 1);
        assert_eq!(name.parts(&db)[0].text(&db), "not");
    }

    #[test]
    fn test_str_to_name_postfix() {
        let db = TestDatabase::default();
        let name = str_to_name(&db, "factorial_");
        assert_eq!(name.fixity(&db), Fixity::Postfix);
        assert_eq!(name.len(&db), 1);
        assert_eq!(name.parts(&db)[0].text(&db), "factorial");
    }

    #[test]
    fn test_str_to_name_multipart_infix() {
        let db = TestDatabase::default();
        let name = str_to_name(&db, "_if_then_else_");
        assert_eq!(name.fixity(&db), Fixity::Infix);
        assert_eq!(name.len(&db), 3);
        assert_eq!(name.parts(&db)[0].text(&db), "if");
        assert_eq!(name.parts(&db)[1].text(&db), "then");
        assert_eq!(name.parts(&db)[2].text(&db), "else");
    }

    #[test]
    fn test_str_to_name_standalone_underscore() {
        let db = TestDatabase::default();
        let name = str_to_name(&db, "_");
        assert_eq!(name.fixity(&db), Fixity::Closed);
        assert_eq!(name.len(&db), 1);
        assert_eq!(name.parts(&db)[0].text(&db), "_");
    }
}
```

### 4.2 Integration Tests

Test that mixfix names work correctly in actual HWML programs:

```hwml
namespace Test

-- Inductive type with mixfix name
inductive _Vec_ (A : Type) : Nat -> Type where
  | nil : _Vec_ A 0
  | cons (n : Nat) (x : A) (xs : _Vec_ A n) : _Vec_ A (succ n)

-- Operator definition
def _+_ (x y : Nat) : Nat := ...
def _*_ (x y : Nat) : Nat := ...
```

---

## Phase 5: Call Site Audit Summary

### Locations Requiring Updates

| File | Line | Function | Pattern | Status |
|------|------|----------|---------|--------|
| `hwml-elab/src/util.rs` | 13 | `str_to_path` | `Name::new(db, Fixity::Closed, ...)` | ✅ Update |
| `hwml-elab/src/names.rs` | 22 | `str_to_simple_qname` | `Name::new(db, Fixity::Closed, ...)` | ✅ Update |
| `hwml-core/src/syn/parse.rs` | 440 | `p_qname` | `FromWithDb::from_with_db(db, component)` | ✅ Update |
| `hwml-elab/src/elab/expr.rs` | 142 | `synth` (field access) | `Name::new(db, Fixity::Closed, ...)` | ✅ Update |
| `hwml-elab/tests/elab_tests.rs` | 504 | `make_qn` | `Name::new(db, Fixity::Closed, ...)` | ✅ Update |
| `hwml-core/src/name.rs` | 92 | `FromWithDb` impl | `Name::new(db, Fixity::Closed, ...)` | ✅ Replace |

### Estimated Impact

- **6 direct call sites** requiring updates
- **~15 indirect call sites** that will automatically use the new API via `FromWithDb`
- **0 breaking changes** for external API (new function is additive)

---

## Phase 6: Implementation Order

1. ✅ **Create this plan document**
2. Add `str_to_name` function to `hwml-core/src/name.rs`
3. Add unit tests for `str_to_name` in `hwml-core/src/name.rs`
4. Update `FromWithDb<&str>` implementation
5. Update all 6 direct call sites listed above
6. Run full test suite: `cargo test --workspace`
7. Add integration tests for mixfix names
8. Update documentation

---

## Open Questions & Future Work

### Q1: What about qualified names like `Foo._+_.Bar`?

**Answer**: Each segment is converted independently, so:
- `"Foo._+_.Bar"` → `[Name("Foo"), Name("_+_"), Name("Bar")]`
- The middle segment will correctly parse as `Infix` with part `["+"]`

### Q2: Should we validate that mixfix names are well-formed?

Currently we allow arbitrary patterns like `___foo___`. Should we reject malformed operators?

**Recommendation**: Defer to a future "operator declaration" phase where the elaborator validates operator well-formedness.

### Q3: What about Unicode underscores?

The lexer currently only treats ASCII `_` (U+005F) as special. Should we support Unicode underscores like `⸏` (U+2E0F)?

**Recommendation**: Stick with ASCII `_` for now. Unicode operators can be future work.

---

## Success Criteria

- ✅ All identifier conversions use `str_to_name` or `FromWithDb`
- ✅ Mixfix operators like `_+_` create `Infix` names with correct parts
- ✅ No direct `Name::new(..., Fixity::Closed, ...)` calls in conversion code
- ✅ All existing tests pass
- ✅ New tests verify mixfix parsing works correctly

