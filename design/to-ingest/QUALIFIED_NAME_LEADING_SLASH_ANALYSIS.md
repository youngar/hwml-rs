# Analysis: Adding Leading "/" to Qualified Names with No Namespace

## Request

Add a leading "/" to the printed representation of fully qualified paths when the namespace is `None` (root-level names).

## Current Behavior

**Currently:**
- `QualifiedName` with namespace `None` prints as: `foo` or `foo/bar/baz`
- `QualifiedName` with namespace `Some(...)` prints as: `Std/Bool` or `Std/Vec/head`

**Examples from tests:**
```rust
// Single component, no namespace
"foo" → prints as "@foo" (in core syntax, with @ prefix)

// Multiple components, no namespace  
"foo/bar/baz" → prints as "@foo/bar/baz"

// With namespace
"Std/Bool" → prints as "@Std/Bool"
```

## Desired Behavior

**After change:**
- Root-level names (namespace = `None`) should print with leading "/"
- Names with a namespace should print as before

**Examples:**
```rust
// Single component, no namespace
"foo" → prints as "@/foo"

// Multiple components, no namespace
"foo/bar/baz" → prints as "@/foo/bar/baz"

// With namespace (unchanged)
"Std/Bool" → prints as "@Std/Bool"
```

## Impact Analysis

### 1. Core Implementation: `QualifiedName::to_string()`

**Location:** `crates/hwml-core/src/name.rs:214-226`

**Current code:**
```rust
pub fn to_string(&self, db: &'db dyn salsa::Database) -> String {
    let mut s = String::new();
    let names = self.segments(db);
    let mut first = true;
    for name in names {
        if !first {
            s.push('/')
        }
        s.push_str(&name.to_string(db));
        first = false;
    }
    s
}
```

**Proposed change:**
```rust
pub fn to_string(&self, db: &'db dyn salsa::Database) -> String {
    let mut s = String::new();
    
    // Add leading "/" if this is a root-level name (namespace is None)
    if self.namespace(db).is_none() {
        s.push('/');
    }
    
    let names = self.segments(db);
    let mut first = true;
    for name in names {
        if !first {
            s.push('/')
        }
        s.push_str(&name.to_string(db));
        first = false;
    }
    s
}
```

### 2. Print Implementation for Core Syntax

**Location:** `crates/hwml-core/src/syn/print.rs:409-418`

**Current code:**
```rust
impl<'db> Print for QualifiedName<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        _st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        p.text_owned(&format!("@{}", self.to_string(db)))
    }
}
```

**This doesn't need to change!** It just adds the "@" prefix. The leading "/" will come from `to_string()`.

### 3. Tests That Need Updating

**Location:** `crates/hwml-core/src/syn/print.rs:1238-1340`

All tests that create root-level names will need snapshot updates:

```rust
#[test]
fn print_prim() {
    let db = TestDatabase::default();
    assert_snapshot!(p(&db, &Syntax::prim_from(&db, "and")), @"$and");
    //                                                           ^^^^
    //                                                        Should become: @$/and
}

#[test]
fn print_constant() {
    let db = TestDatabase::default();
    assert_snapshot!(p(&db, &Syntax::constant_from(&db, "myConst")), @"@myConst");
    //                                                                   ^^^^^^^^
    //                                                                Should become: @/myConst
}

#[test]
fn print_constant_hierarchical_two_components() {
    let db = TestDatabase::default();
    let foo: QualifiedName = hwml_support::FromWithDb::from_with_db(&db, "foo");
    let foo_bar = foo.qualify_name(&db, "bar");
    assert_snapshot!(p(&db, &Syntax::constant_rc(foo_bar)), @"@foo/bar");
    //                                                          ^^^^^^^^
    //                                                       Should become: @/foo/bar
}

#[test]
fn print_constant_hierarchical_three_components() {
    let db = TestDatabase::default();
    let foo: QualifiedName = hwml_support::FromWithDb::from_with_db(&db, "foo");
    let foo_bar = foo.qualify_name(&db, "bar");
    let foo_bar_baz = foo_bar.qualify_name(&db, "baz");
    assert_snapshot!(p(&db, &Syntax::constant_rc(foo_bar_baz)), @"@foo/bar/baz");
    //                                                              ^^^^^^^^^^^^
    //                                                           Should become: @/foo/bar/baz
}
```

**Estimated:** ~12-15 test snapshots need updating

### 4. Declaration Printing

**Location:** `crates/hwml-core/src/syn/print.rs:73-100`

Uses `qname.to_string(db)` directly:
```rust
pub fn print_primitive_decl(...) {
    p.text("prim $")?;
    p.text_owned(prim.name.to_string(db))?;  // ← Will automatically get "/"
    ...
}

pub fn print_constant_decl(...) {
    p.text("const @")?;
    p.text_owned(c.name.to_string(db))?;  // ← Will automatically get "/"
    ...
}
```

**No code changes needed** - they will automatically get the leading "/".

### 5. Debug Output

**Location:** `crates/hwml-elab/src/program.rs:1067-1078`

```rust
eprintln!(
    "[GATHER] Created QualifiedName {:?} = '{}' | namespace: {:?} | segments: {:?}",
    qname,
    qname.to_string(db),  // ← Will automatically show "/"
    current_namespace.map(|n| n.to_string(db)),
    ...
);
```

**Impact:** Debug output will show the leading "/" automatically.

Example output change:
```
Before: [GATHER] Created QualifiedName ... = 'Std/Bool' | ...
After:  [GATHER] Created QualifiedName ... = '/Std/Bool' | ...  (if root-level)
        [GATHER] Created QualifiedName ... = 'Std/Bool' | ...    (if has namespace)
```

### 6. Error Messages

**Location:** `crates/hwml-elab/src/kernel/mod.rs:49-54, 134-140`

```rust
fn format_path<'db>(db: &'db dyn salsa::Database, path: &[Name<'db>]) -> String {
    path.iter()
        .map(|name| name.to_string(db))
        .collect::<Vec<_>>()
        .join(".")  // Note: uses "." not "/"
}
```

**This function works on `Name`, not `QualifiedName`** - no change needed.

### 7. Resolver Debug Output

**Location:** `crates/hwml-elab/src/resolver.rs:295-297`

```rust
eprintln!(
    "[RESOLVE] Trying namespace qualification: {}",
    qualified.to_string(db)  // ← Will automatically show "/"
);
```

**Impact:** Resolution debug output will show leading "/" for root names.

## Files Requiring Changes

### Direct Code Changes (1 file)

1. **`crates/hwml-core/src/name.rs`**
   - Modify `QualifiedName::to_string()` method
   - Add check for `namespace.is_none()`
   - Insert leading "/" for root-level names

### Test Updates (1 file)

2. **`crates/hwml-core/src/syn/print.rs`**
   - Update all test snapshots that create root-level `QualifiedName`s
   - Estimated 12-15 snapshot updates

## Parsing Implications

**Important:** Does the parser currently accept leading "/"?

**Check:** `crates/hwml-core/src/syn/parse.rs:436-447`

```rust
fn p_qname<'db>(db: &'db dyn salsa::Database, name_str: &str) -> QualifiedName<'db> {
    let components: Vec<&str> = name_str.split('/').collect();
    let mut qname = None;
    for component in components {
        let name = crate::str_to_name(db, component)
            .expect("Core syntax should not contain malformed identifiers");
        qname = Some(QualifiedName::new(db, qname, name));
    }
    qname.unwrap()
}
```

**Issue:** If input is `"/foo"`, this will split to `["", "foo"]` and try to parse empty string as a name!

**Solution needed:** Skip empty components from leading slash:

```rust
fn p_qname<'db>(db: &'db dyn salsa::Database, name_str: &str) -> QualifiedName<'db> {
    let components: Vec<&str> = name_str.split('/').filter(|s| !s.is_empty()).collect();
    let mut qname = None;
    for component in components {
        let name = crate::str_to_name(db, component)
            .expect("Core syntax should not contain malformed identifiers");
        qname = Some(QualifiedName::new(db, qname, name));
    }
    qname.unwrap()
}
```

## Summary

### Changes Required

1. **`crates/hwml-core/src/name.rs`**
   - Add `if self.namespace(db).is_none() { s.push('/'); }` at start of `to_string()`

2. **`crates/hwml-core/src/syn/parse.rs`**  
   - Add `.filter(|s| !s.is_empty())` to handle leading "/" in parsing

3. **`crates/hwml-core/src/syn/print.rs`**
   - Update ~12-15 test snapshots

### Affected Output

- Core syntax printing (constants, primitives, type constructors)
- Debug output in elaborator
- Error messages (indirectly through qualified name display)
- All root-level declarations in stdlib will show with "/"

### Not Affected

- Path resolution logic (works on `Vec<Name>`, not `QualifiedName`)  
- Declaration declarations in surface syntax
- Internal name representation (only display changes)
