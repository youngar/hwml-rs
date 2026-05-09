# UTF-8 Conversion Audit: Problematic Patterns in HWML Codebase

**Date:** 2026-05-06  
**Auditor:** Augment Agent  
**Scope:** Full codebase scan for `String::from_utf8_lossy` and unnecessary UTF-8 conversions

---

## Executive Summary

**Status:** ⚠️ **15 problematic instances** found where we convert `&[u8]` → `String` unnecessarily

**Root Cause:** The `Word` type (Salsa-interned string) requires `Box<str>`, forcing all callsites to convert bytes to strings. This breaks the byte-oriented pipeline.

**Impact:**
- **Performance:** Unnecessary allocations and UTF-8 validation on every identifier
- **Correctness:** Using `from_utf8_lossy` masks invalid UTF-8 (replaces with �)
- **Architecture:** Violates the byte-based design principle

**Recommendation:** Either:
1. Make `Word` accept `&[u8]` (validate once, intern bytes)
2. Add explicit UTF-8 validation with proper error handling

---

## Critical Finding: The `Word` Bottleneck

### Current Design

<parameter name="file_content">```rust
// crates/hwml-core/src/word.rs
#[salsa::interned]
pub struct Word {
    #[return_ref]
    pub text: Box<str>,  // ← FORCES String conversion!
}
```

**Every identifier creation goes through:**
1. Lexer produces `&[u8]` (correct!)
2. Elaborator receives `&[u8]` in `Id.value`
3. **Forced conversion:** `String::from_utf8_lossy(&bytes)` 
4. Create `Word::new(db, text.as_ref())`
5. Intern as `Box<str>`

### The Problem

`String::from_utf8_lossy` **silently replaces** invalid UTF-8 with �:

```rust
let bytes = b"caf\xFF";  // Invalid UTF-8
let lossy = String::from_utf8_lossy(bytes);  
// Result: "caf�" - NO ERROR!
```

**This masks invalid UTF-8 in user source code instead of reporting it.**

---

## Problematic Instances (15 Total)

### Category 1: Name Construction (9 instances)

**Files:**
- `crates/hwml-elab/src/util.rs` (2 instances)
- `crates/hwml-elab/src/names.rs` (1 instance)
- `crates/hwml-elab/src/elab/expr.rs` (4 instances)  
- `crates/hwml-elab/src/elab/decl.rs` (2 instances)

**Pattern:**
```rust
// PROBLEMATIC: Silent lossy conversion
let text = String::from_utf8_lossy(seg);
let word = Word::new(db, text.as_ref());
let atom = Atom::new(word);
let name = Name::new(db, Fixity::Closed, Box::from([atom]));
```

**Locations:**

1. **`crates/hwml-elab/src/util.rs:16`**
   ```rust
   pub fn surface_id_to_path(...) {
       segments.map(|seg| {
           let text = String::from_utf8_lossy(seg);  // ← BAD
           let word = Word::new(db, text.as_ref());
           // ...
       })
   }
   ```

2. **`crates/hwml-elab/src/util.rs:34`**
   ```rust
   pub fn bytes_to_path(...) {
       segments.map(|seg| {
           let text = String::from_utf8_lossy(seg);  // ← BAD
           // ...
       })
   }
   ```

3. **`crates/hwml-elab/src/names.rs:20`**
   ```rust
   pub fn bytes_to_simple_qname(...) {
       let text = String::from_utf8_lossy(segment);  // ← BAD
       let word = Word::new(db, text.as_ref());
       // ...
   }
   ```

4-7. **`crates/hwml-elab/src/elab/expr.rs:89, 127, 140, 173`**
   ```rust
   // Line 89: Identifier synthesis
   let name = String::from_utf8_lossy(&id.value).to_string();  // ← BAD
   
   // Line 127: Dotted identifier receiver
   let receiver_name = String::from_utf8_lossy(receiver_bytes).to_string();  // ← BAD
   
   // Line 140: Field access
   let text = String::from_utf8_lossy(field_bytes);  // ← BAD
   
   // Line 173: Dot expression field
   let text = String::from_utf8_lossy(&dot.field.value);  // ← BAD
   ```

8-9. **`crates/hwml-elab/src/elab/decl.rs:106, 241`**
   ```rust
   // Error message generation (also problematic!)
   name: String::from_utf8_lossy(&def.id.value).to_string(),  // ← BAD
   ```

### Category 2: Error Messages (4 instances)

**Files:**
- `crates/hwml-elab/src/elab/decl.rs` (2)
- `crates/hwml-elab/src/scc_elab.rs` (1)
- `crates/hwml-elab/src/program.rs` (3)

**Pattern:**
```rust
// PROBLEMATIC: Even error messages use lossy conversion
ElabError::NotInScope {
    name: String::from_utf8_lossy(&id.value).to_string(),  // ← BAD
    span: None,
}
```

**Issue:** If the user writes invalid UTF-8, we should report "invalid UTF-8 in identifier", not "cannot find identifier �".

### Category 3: Debugging/Logging (2 instances)

**Files:**
- `crates/hwml-elab/src/kernel/mod.rs:751`
- `crates/hwml-elab/src/elab/expr.rs:369`

**Pattern:**
```rust
// For debug output
let name = String::from_utf8_lossy(&id.value).to_string();
eprintln!("[EXPR] Synthesizing identifier: {}", name);
```

**Note:** This is actually OKAY for debug output (lossy is fine for logging).

---

## Architecture Analysis

### Current Flow (Broken)

```
Source File (UTF-8 bytes)
    ↓
Lexer (&[u8])  ✅ Good!
    ↓
Token with ByteRange  ✅ Good!
    ↓
Parser extracts Id { value: Box<[u8]> }  ✅ Good!
    ↓
❌ Elaborator: String::from_utf8_lossy()  ← BAD! Silent masking
    ↓
Word::new(db, &str) → Box<str>  ← Forced by Word's signature
    ↓
Salsa interning
```

### Root Cause: Word Design

`Word` is a Salsa-interned type that stores `Box<str>`. This means:
1. **Must be valid UTF-8** - `str` is a UTF-8 string
2. **Forces conversion** - All call sites must convert `&[u8]` → `&str`
3. **Callsites use lossy** - To avoid panics, everyone uses `from_utf8_lossy`

### Two Possible Fixes

**Option A: Make Word byte-oriented**

```rust
#[salsa::interned]
pub struct Word {
    #[return_ref]
    pub bytes: Box<[u8]>,  // ← Store bytes, validate on access
}

impl Word {
    /// Get text, validating UTF-8 on demand
    pub fn text(&self, db: &dyn salsa::Database) -> Result<&str, Utf8Error> {
        std::str::from_utf8(self.bytes(db))
    }
    
    /// Get text, lossy (for debug/display only)
    pub fn text_lossy(&self, db: &dyn salsa::Database) -> Cow<'_, str> {
        String::from_utf8_lossy(self.bytes(db))
    }
}
```

**Pros:**
- ✅ Store exactly what lexer produces (byte offsets align)
- ✅ Can detect invalid UTF-8 and report proper errors
- ✅ Validate once per unique identifier (interning deduplicates)

**Cons:**
- ⚠️ Every access to `.text()` needs error handling
- ⚠️ Breaks existing code (needs migration)

**Option B: Validate explicitly at conversion sites**

```rust
// Helper function
pub fn bytes_to_word<'db>(
    db: &'db dyn salsa::Database,
    bytes: &[u8],
) -> Result<Word<'db>, InvalidUtf8Error> {
    let text = std::str::from_utf8(bytes)?;  // ← Explicit validation
    Ok(Word::new(db, text))
}

// Usage
let word = bytes_to_word(db, seg).map_err(|e| ElabError::InvalidUtf8 {
    bytes: seg.to_vec(),
    location: span,
    error: e,
})?;
```

**Pros:**
- ✅ Keeps `Word` as `Box<str>` (no migration needed)
- ✅ Explicit error handling at conversion sites
- ✅ Can report proper errors with byte offsets

**Cons:**
- ⚠️ Must update all 15+ call sites
- ⚠️ More verbose

---

## Recommended Solution

**Phase 1: Add validation helper (this week)**

```rust
// crates/hwml-core/src/word.rs

/// Error for invalid UTF-8 in identifiers
#[derive(Debug, Clone)]
pub struct InvalidUtf8Error {
    pub bytes: Vec<u8>,
    pub error: std::str::Utf8Error,
}

impl Word {
    /// Create a Word from UTF-8 bytes with validation
    pub fn from_utf8<'db>(
        db: &'db dyn salsa::Database,
        bytes: &[u8],
    ) -> Result<Word<'db>, InvalidUtf8Error> {
        let text = std::str::from_utf8(bytes)
            .map_err(|e| InvalidUtf8Error {
                bytes: bytes.to_vec(),
                error: e,
            })?;
        Ok(Word::new(db, text))
    }
}
```

**Phase 2: Update call sites (next week)**

Replace all instances of:
```rust
// OLD (silent lossy)
let text = String::from_utf8_lossy(seg);
let word = Word::new(db, text.as_ref());
```

With:
```rust
// NEW (explicit validation)
let word = Word::from_utf8(db, seg).map_err(|e| ElabError::InvalidUtf8 {
    bytes: e.bytes,
    location: span,
    utf8_error: e.error,
})?;
```

**Phase 3: Long-term (optional)**

Consider making `Word` byte-oriented if the error handling becomes too verbose.

---

## Detailed Instance List

| File | Line | Function | Current Code | Issue |
|------|------|----------|--------------|-------|
| `util.rs` | 16 | `surface_id_to_path` | `from_utf8_lossy(seg)` | Name construction |
| `util.rs` | 34 | `bytes_to_path` | `from_utf8_lossy(seg)` | Name construction |
| `names.rs` | 20 | `bytes_to_simple_qname` | `from_utf8_lossy(segment)` | Name construction |
| `elab/expr.rs` | 89 | `synth` | `from_utf8_lossy(&id.value)` | Name lookup |
| `elab/expr.rs` | 127 | `synth` (dotted ID) | `from_utf8_lossy(receiver_bytes)` | Field access |
| `elab/expr.rs` | 140 | `synth` (field chain) | `from_utf8_lossy(field_bytes)` | Field access |
| `elab/expr.rs` | 173 | `synth` (Dot expr) | `from_utf8_lossy(&dot.field.value)` | Field access |
| `elab/expr.rs` | 369 | `check_let_in` | `from_utf8_lossy(&let_in.id.value)` | Let binding |
| `elab/decl.rs` | 106 | `elab_def_impl` | `from_utf8_lossy(&def.id.value)` | Error message |
| `elab/decl.rs` | 241 | `elab_inductive_impl` | `from_utf8_lossy(&ind.name.value)` | Error message |
| `elab/decl.rs` | 496 | `binder_to_name` | `from_utf8_lossy(&id.value)` | Binder name |
| `scc_elab.rs` | 113 | `elaborate_scc` | `from_utf8_lossy(&ind.name.value)` | Error message |
| `program.rs` | 233 | `handle_namespace` | `from_utf8_lossy(&alias_id.value)` | Namespace alias |
| `program.rs` | 248 | `handle_namespace` | `from_utf8_lossy(&open.namespace.value)` | Open directive |
| `program.rs` | 263 | `handle_namespace` | `from_utf8_lossy(&open.namespace.value)` | Error message |

---

## Action Items

**High Priority:**
1. [ ] Add `Word::from_utf8()` validation helper
2. [ ] Add `ElabError::InvalidUtf8` variant
3. [ ] Update `util.rs` functions (2 instances)
4. [ ] Update `names.rs` functions (1 instance)
5. [ ] Update `elab/expr.rs` identifier handling (5 instances)

**Medium Priority:**
6. [ ] Update error message generation (4 instances)
7. [ ] Update namespace/program handling (3 instances)
8. [ ] Add test cases for invalid UTF-8 identifiers

**Low Priority (OK for now):**
- Debug/logging uses of `from_utf8_lossy` (2 instances) - acceptable for display

---

## Test Cases Needed

```rust
#[test]
fn test_invalid_utf8_identifier() {
    let source = b"def \xFF\xFE = 42";  // Invalid UTF-8
    let result = lex_and_parse(source);
    
    // Should produce: ElabError::InvalidUtf8
    assert!(matches!(result, Err(ElabError::InvalidUtf8 { .. })));
}

#[test]
fn test_valid_unicode_identifier() {
    let source = "def café = 42";  // Valid UTF-8
    let result = lex_and_parse(source);
    
    // Should succeed
    assert!(result.is_ok());
}

#[test]
fn test_emoji_identifier() {
    let source = "def 🚀_speed = 299792";  // Emoji (valid UTF-8)
    let result = lex_and_parse(source);
    
    // Should succeed
    assert!(result.is_ok());
}
```

---

**Next Steps:** Review this audit and decide on Option A vs Option B for the fix strategy.
