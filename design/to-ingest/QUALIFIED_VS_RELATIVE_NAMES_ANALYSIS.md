# Qualified vs. Relative Names - Deep Dive Analysis

## Executive Summary

HWML currently uses `QualifiedName` for **two distinct purposes**:
1. **Absolute/Qualified Names**: Fully resolved names rooted at the root namespace (e.g., `/Std/Bool/true`)
2. **Relative Names**: Unresolved local identifiers from surface syntax that need resolution (e.g., `Bool.true`)

This overloading creates conceptual confusion. A proper separation would make the type system more precise and the codebase easier to understand.

## Current Architecture

### Data Flow: Surface Syntax → Resolution → Qualified Names

```
Surface Syntax (String)
    ↓
  Id { value: "Foo.Bar.Baz" }     [hwml-surface]
    ↓
  surface_id_to_path()             [hwml-elab/util.rs]
    ↓
  Vec<Name> = [Foo, Bar, Baz]      [Relative path - NOT rooted yet!]
    ↓
  resolve_path()                   [hwml-elab/resolver.rs]
    ↓
  Vec<QualifiedName>               [Absolute paths - rooted at root!]
    ↓
  StubTable lookup                 [Validation that name exists]
    ↓
  QualifiedName                    [Final resolved absolute name]
```

### Key Observation: `Vec<Name>` is the "Relative Name"

**The current system already has a representation for relative names: `Vec<Name>` (or `&[Name]`)**.

This is the path extracted from surface syntax that has **not yet been resolved** according to:
- The current namespace
- Open directives (imports)
- Lexical scopes

### `QualifiedName` Structure

```rust
#[salsa::interned]
pub struct QualifiedName {
    pub namespace: Option<QualifiedName<'db>>,  // Parent namespace
    pub name: Name<'db>,                        // Final segment
}
```

**Semantics:**
- `namespace: None` → This is a root-level name (e.g., `Std`, `Bool`)
- `namespace: Some(parent)` → This is a name qualified under `parent`

**Visual representation (current):**
- `Std/Bool` (namespace chain: `Std` → `Bool`)
- Printed without leading `/` currently

**Visual representation (proposed):**
- `/Std/Bool` (leading `/` indicates root)

## The Two Concepts in Detail

### 1. Relative Names (Currently: `Vec<Name>`)

**Definition:** A path of names from surface syntax that has NOT been resolved against the current scope.

**Examples:**
- User writes: `Bool` → Relative path: `[Bool]`
- User writes: `Std.Bool` → Relative path: `[Std, Bool]`
- User writes: `List.map` → Relative path: `[List, map]`

**Properties:**
- **Not rooted**: Could resolve to different qualified names depending on context
- **Context-dependent**: Meaning depends on current namespace and open directives
- **Ambiguous**: Could match multiple qualified names (requires disambiguation)

**Where they appear:**
- Surface syntax identifiers (`Expression::Id`)
- Namespace declarations (`namespace Foo.Bar { ... }`)
- Type references in signatures
- Import paths in `open` statements

**Current representation:** `Vec<Name<'db>>` or `&[Name<'db>]`

### 2. Qualified Names (Currently: `QualifiedName`)

**Definition:** A fully resolved, absolute path rooted at the root namespace.

**Examples:**
- `/Bool` (the root-level `Bool` type)
- `/Std/List` (the `List` type in the `Std` namespace)
- `/Std/List/map` (the `map` function in the `List` namespace under `Std`)

**Properties:**
- **Rooted**: Always starts from the root namespace
- **Context-independent**: Has the same meaning everywhere
- **Unambiguous**: Refers to exactly one global definition

**Where they appear:**
- StubTable keys (maps qualified names to declarations)
- Global environment (stores types/values for qualified names)
- Core syntax after elaboration (`Syntax::constant(QualifiedName)`)
- Resolver output (result of resolution)

**Current representation:** `QualifiedName<'db>`

## Current System Analysis

### ✅ What Works Well

1. **`Vec<Name>` as Relative Names**
   - Simple and lightweight
   - Natural representation of dotted paths from syntax
   - Easy to manipulate (append, prepend, slice)

2. **`QualifiedName` as Absolute Names**
   - Interned (cheap to copy, compare)
   - Recursive structure mirrors namespace hierarchy
   - Easy to walk up the namespace chain

3. **Clear Separation Point: `resolve_path()`**
   - Takes `Vec<Name>` (relative)
   - Returns `Vec<QualifiedName>` (candidates, all absolute)
   - Clean transformation from relative to absolute

### ⚠️ What's Confusing

1. **`QualifiedName::qualify_path()` Overloaded**
   ```rust
   pub fn qualify_path(
       db: &'db Db,
       namespace: Option<QualifiedName<'db>>,  // ← Could be None (root) or Some (relative to namespace)
       path: &[Name<'db>],
   ) -> Option<Self>
   ```

   This function is used for **both**:
   - **Absolute qualification**: `namespace=None, path=[Std, Bool]` → `/Std/Bool`
   - **Relative qualification**: `namespace=Some(/Std), path=[Bool]` → `/Std/Bool`

2. **No Type-Level Distinction**
   - A `QualifiedName` with `namespace: None` could be:
     - A root-level name (e.g., `/Std`)
     - A single-segment relative name before resolution (shouldn't happen, but nothing prevents it)

3. **Resolver Namespace is `Option<QualifiedName>`**
   - `None` means "we're at root"
   - But this is an implementation detail, not a separate type

## Potential Design: Explicit `RelativePath` Type

### Option A: NewType Wrapper

```rust
/// A relative path from surface syntax, not yet resolved.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RelativePath<'db>(Vec<Name<'db>>);

impl<'db> RelativePath<'db> {
    pub fn new(names: Vec<Name<'db>>) -> Self {
        assert!(!names.is_empty(), "RelativePath cannot be empty");
        Self(names)
    }

    pub fn segments(&self) -> &[Name<'db>] {
        &self.0
    }

    pub fn to_string(&self, db: &'db dyn salsa::Database) -> String {
        self.0.iter()
            .map(|n| n.to_string(db))
            .collect::<Vec<_>>()
            .join(".")
    }
}
```

**Benefits:**
- Clear semantic distinction in types
- Can't accidentally use relative path where absolute is expected
- Better documentation through types

**Drawbacks:**
- Extra type to maintain
- Conversion overhead (though minimal)
- `Vec<Name>` is already quite clear

### Option B: Keep `Vec<Name>`, Add Documentation

**Recommendation:** Keep the current `Vec<Name>` representation but:
1. Add clear documentation that `Vec<Name>` represents **relative paths**
2. Name variables consistently: `relative_path`, `unresolved_path`, `surface_path`
3. Document that `QualifiedName` is **always absolute** (rooted at root namespace)

## Critical Insight: `namespace: None` vs Relative Paths

### Current Confusion Point

When you see `QualifiedName::new(db, None, name)`, what does it mean?

**Two interpretations:**
1. ❌ **Wrong:** "This is a relative name (just `name` by itself)"
2. ✅ **Correct:** "This is an absolute name at the root level (i.e., `/name`)"

### The Truth: `namespace: None` Always Means Root-Level Absolute

Looking at the harvesting code:

```rust
// crates/hwml-elab/src/stub_table.rs (harvesting declarations)
fn harvest_def<'db>(
    db: &'db dyn salsa::Database,
    stub_table: &mut StubTable<'db>,
    namespace: Option<QualifiedName<'db>>,  // ← Current namespace during traversal
    def: &surface::Def,
    source_range: SourceRange<'db>,
) -> Result<(), String> {
    let path = surface_id_to_path(db, &def.id)?;  // ← Relative path from syntax
    let name = QualifiedName::qualify_path(db, namespace, &path)?;  // ← Qualify to absolute
    stub_table.insert(name, GlobalNameKind::Constant, source_range)?;
    Ok(())
}
```

**Key observations:**
- `namespace: Option<QualifiedName>` is the **current namespace during program traversal**
  - `None` = "We're at the root of the file"
  - `Some(ns)` = "We're inside namespace `ns`"
- `path` from `surface_id_to_path()` is a **relative path** from the surface syntax
- `QualifiedName::qualify_path(db, namespace, &path)` combines them to create an **absolute name**

### The Resolution Process

```rust
// In resolver.rs
pub fn resolve_path<'db>(
    db: &'db Db,
    stub_table: &StubTable<'db>,
    resolver: &Resolver<'db>,
    path: &[Name<'db>],  // ← RELATIVE path from surface syntax
) -> Vec<QualifiedName<'db>>  // ← ABSOLUTE qualified names (candidates)
{
    // Try qualifying against current namespace
    let current_ns = resolver.namespace();  // Option<QualifiedName> - current namespace

    if let Some(qualified) = QualifiedName::qualify_path(db, current_ns, path) {
        if stub_table.contains(qualified) {
            candidates.push(qualified);  // ← This is ABSOLUTE
        }
    }

    // Also try qualifying against open directives, walking up namespaces, etc.
    // All resulting QualifiedNames are ABSOLUTE
}
```

## Concrete Example: How Names Flow

### Example Program

```hwml
namespace Std {
    inductive Bool : Type where
        | true : Bool
        | false : Bool
}

def myBool : Bool := true
```

### Step-by-Step Flow

1. **Harvesting `namespace Std { ... }`**
   - Surface: `Id { value: "Std" }`
   - `surface_id_to_path()` → `[Std]` (relative path)
   - `QualifiedName::qualify_path(db, None, [Std])` → `/Std` (absolute)
   - Enter namespace: `resolver.namespace = Some(/Std)`

2. **Harvesting `inductive Bool`**
   - Surface: `Id { value: "Bool" }`
   - `surface_id_to_path()` → `[Bool]` (relative path)
   - Current namespace: `Some(/Std)`
   - `QualifiedName::qualify_path(db, Some(/Std), [Bool])` → `/Std/Bool` (absolute)
   - StubTable: `/Std/Bool` → TypeConstructor

3. **Harvesting `| true`**
   - Surface: `Id { value: "true" }`
   - `surface_id_to_path()` → `[true]` (relative path)
   - Current namespace: `Some(/Std/Bool)` (inside the inductive!)
   - `QualifiedName::qualify_path(db, Some(/Std/Bool), [true])` → `/Std/Bool/true` (absolute)
   - StubTable: `/Std/Bool/true` → DataConstructor

4. **Elaborating `def myBool : Bool := true`**
   - Type reference `Bool`:
     - Surface: `Id { value: "Bool" }`
     - `surface_id_to_path()` → `[Bool]` (relative path)
     - `resolve_path(db, stub_table, resolver, [Bool])`
       - Try: `QualifiedName::qualify_path(db, None, [Bool])` → `/Bool`
       - Check StubTable: `/Bool` not found
       - Try: `QualifiedName::qualify_path(db, None, [Std, Bool])` via open directive (if any)
       - Check StubTable: `/Std/Bool` found! ✅
     - Result: `/Std/Bool` (absolute)

   - Value reference `true`:
     - Surface: `Id { value: "true" }`
     - `surface_id_to_path()` → `[true]` (relative path)
     - `resolve_path(db, stub_table, resolver, [true])`
       - Walk through scopes, try various qualifications
       - Eventually finds: `/Std/Bool/true` (absolute)
     - Result: `/Std/Bool/true` (absolute)

## Recommendations

### 1. Keep Current Architecture ✅

**The current design is actually quite good!**

- `Vec<Name>` for relative paths (unresolved surface syntax)
- `QualifiedName` for absolute paths (resolved global names)
- Clean separation at `resolve_path()` boundary

### 2. Add Leading `/` to `QualifiedName::to_string()` ✅

This makes the "absolute" nature visually clear:

```rust
pub fn to_string(&self, db: &'db dyn salsa::Database) -> String {
    let mut s = String::new();

    // Add leading "/" for root-level names
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

**Result:**
- `/Bool` (clearly rooted at root)
- `/Std/Bool` (clearly rooted at root)
- Makes "qualified" = "absolute" visually obvious

### 3. Documentation Improvements

Add clear documentation to key functions:

**`hwml-elab/src/util.rs`:**
```rust
/// Convert a surface syntax identifier to a **relative path** of names.
///
/// The resulting path is NOT resolved - it represents the user's written
/// identifier and must be resolved against the current scope to find the
/// actual qualified name.
///
/// # Examples
/// - `"Bool"` → `[Bool]` (relative, could resolve to `/Bool` or `/Std/Bool`)
/// - `"List.map"` → `[List, map]` (relative, needs resolution)
pub fn surface_id_to_path<'db>(...) -> Result<Vec<Name<'db>>, NameError>
```

**`hwml-elab/src/resolver.rs`:**
```rust
/// Resolve a **relative path** from surface syntax to **absolute qualified names**.
///
/// Takes a path like `[Bool]` or `[List, map]` and returns all matching
/// qualified names found in the current scope, considering:
/// - The current namespace
/// - Open directives (imports)
/// - Walking up the namespace hierarchy
///
/// All returned `QualifiedName`s are **absolute** (rooted at the root namespace).
pub fn resolve_path<'db>(
    db: &'db Db,
    stub_table: &StubTable<'db>,
    resolver: &Resolver<'db>,
    path: &[Name<'db>],  // ← RELATIVE path
) -> Vec<QualifiedName<'db>>  // ← ABSOLUTE qualified names
```

### 4. Naming Conventions

Use consistent variable names to make the distinction clear:

**Relative paths (unresolved):**
- `relative_path`
- `surface_path`
- `unresolved_path`
- `path` (when context is clear)

**Absolute names (resolved):**
- `qualified_name`
- `qname`
- `absolute_name`
- `resolved_name`

**Example:**
```rust
fn synth_id(elab: &mut Elaborator, id: &Id) -> Result<...> {
    // Extract relative path from surface syntax
    let relative_path = surface_id_to_path(db, id)?;

    // Resolve to absolute qualified names
    let candidates = resolve_path(db, stub_table, resolver, &relative_path);

    // Pick one qualified name (disambiguate if needed)
    let qualified_name = disambiguate(candidates)?;

    // Use the absolute qualified name
    kernel.synth_constant(qualified_name, ...)
}
```

## Summary Table

| Concept | Type | Example Value | String Repr | Scope-Dependent? | Where Used |
|---------|------|---------------|-------------|------------------|------------|
| **Relative Path** | `Vec<Name>` | `[Bool]` | `"Bool"` | Yes | Surface syntax → Resolution |
| **Relative Path** | `Vec<Name>` | `[List, map]` | `"List.map"` | Yes | Surface syntax → Resolution |
| **Qualified Name** | `QualifiedName` | `/Bool` | `"/Bool"` (with leading `/`) | No | Resolution → Core syntax |
| **Qualified Name** | `QualifiedName` | `/Std/Bool/true` | `"/Std/Bool/true"` | No | StubTable, Global env |

## Conclusion

**No architectural changes needed.** The current design already has a clear separation:

1. **Relative paths**: `Vec<Name>` - context-dependent, from surface syntax
2. **Qualified names**: `QualifiedName` - context-independent, always absolute

The confusion comes from:
- Lack of explicit documentation
- No visual distinction (leading `/` will fix this)
- Variable naming not always consistent

**Recommended actions:**
1. ✅ Implement leading `/` for qualified names (as analyzed in `QUALIFIED_NAME_LEADING_SLASH_ANALYSIS.md`)
2. ✅ Add documentation clarifying relative vs. absolute
3. ✅ Use consistent naming conventions
4. ❌ Do NOT create a new `RelativePath` type - `Vec<Name>` is perfect for this use case





