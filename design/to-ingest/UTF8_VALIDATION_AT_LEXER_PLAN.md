# UTF-8 Validation at Lexer Boundary: Implementation Plan

**Date:** 2026-05-06  
**Goal:** Validate UTF-8 at lexer, use unchecked conversion internally

---

## Current Architecture

### 1. Lexer Layer (Logos)

**Two lexers exist:**

1. **`hwml-core/src/syn/parse.rs`** - Core language lexer
   ```rust
   #[derive(Logos, Clone, Debug, Eq, PartialEq, Hash)]
   #[logos(error(Error, Error::from_lexer))]
   pub enum Token {
       // Tokens with String payloads:
       #[regex(r"@(?&id)+(/(?&id)+)*", callback = |lex| lex.slice()["@".len()..].to_owned())]
       Constant(String),  // ← Currently uses .to_owned() on &[u8]
       
       #[regex(r"%(?&id)+", callback = |lex| lex.slice()["%".len()..].to_owned())]
       Variable(String),  // ← Currently uses .to_owned() on &[u8]
       
       #[regex(r"\$(?&id)+(/(?&id)+)*", callback = |lex| lex.slice()["$".len()..].to_owned())]
       Primitive(String), // ← Currently uses .to_owned() on &[u8]
       
       // ... other tokens
   }
   ```

2. **`hwml-surface/src/lex.rs`** - Surface language lexer
   ```rust
   #[derive(Logos, Copy, Clone, Debug, Eq, PartialEq, Hash)]
   #[logos(source = [u8], error = LexicalError)]  // ← Already byte-based!
   pub enum Token {
       #[regex(r"[^\p{gc=Separator}\p{gc=Control}{}()\[\];,]+")]
       Identifier,  // ← No payload, bytes extracted later
       
       #[regex(r"[0-9]+")]
       Number,      // ← No payload, bytes extracted later
       
       #[regex(r".", priority = 1)]
       Unknown,
       
       #[regex(r"[\x00-\xFF]", priority = 0)]
       Error,       // ← POTENTIAL invalid UTF-8 token!
   }
   ```

### 2. Parser Layer (LALRPOP)

**How identifiers are extracted:**

```rust
// crates/hwml-surface/src/grammar.lalrpop
Id: Id = {
  <l:@L> <s:"id"> <r:@R> => {
    Id::new(l..r, Box::from(&input[l..r]))  // ← Slices original input bytes
  }
};
```

**Key insight:** The LALRPOP grammar receives:
- `input: &'input [u8]` - The original source bytes
- `l` and `r` - Byte offsets from lexer
- Token stream from `Lexer::new(input)`

**What gets stored:**
```rust
// crates/hwml-surface/src/syntax.rs
pub struct Id {
    pub loc: Range<usize>,
    pub value: Box<[u8]>,  // ← RAW BYTES from input[l..r]
}
```

### 3. Elaborator Layer

**Current conversion (problematic):**

```rust
// crates/hwml-elab/src/names.rs
pub fn bytes_to_simple_qname(db: &dyn Database, segment: &[u8]) -> QualifiedName {
    let text = String::from_utf8_lossy(segment);  // ← SILENT masking!
    let word = Word::new(db, text.as_ref());
    // ...
}
```

**This pattern appears in 15 places** (see `UTF8_CONVERSION_AUDIT.md`).

---

## The Problem

**Current flow:**
```
Source file → Lexer → Parser → Elaborator → Word
   [u8]        [u8]     [u8]    from_utf8_lossy   Box<str>
                                    ↑ MASKS ERRORS HERE!
```

**Issue:** Invalid UTF-8 in source (e.g., `café\xFF`) silently becomes `café�`, leading to confusing "identifier not found" errors later.

---

## The Solution: Validate at Lexer Boundary

### Strategy

**Production compiler consensus** (see `PRODUCTION_COMPILERS_UTF8_STORAGE.md`):
1. ✅ Validate UTF-8 **once** at the lexer/parser boundary
2. ✅ Store validated strings internally (`Box<str>`, `&str`)
3. ✅ Use unchecked conversion after validation
4. ✅ Report errors early (at lex/parse, not elaboration)

### New Flow

```
Source file → Lexer validates → Parser → Elaborator → Word
   [u8]        checks UTF-8      [u8]    from_utf8_unchecked  Box<str>
                     ↓
                   Error if invalid
                     ↓
                LexicalError::InvalidUtf8 { byte_offset, invalid_sequence }
```

---

## Implementation Plan

### Phase 1: Update `hwml-surface` Lexer (Surface Language)

**File:** `crates/hwml-surface/src/lex.rs`

**Current state:** Already has `Error` token for invalid bytes!

```rust
#[logos(subpattern horizontal_whitespace = "...")]
pub enum Token {
    // ...
    #[regex(r"[^\p{gc=Separator}\p{gc=Control}{}()\[\];,]+", priority = 2)]
    Identifier,  // ← Matches any bytes (including invalid UTF-8!)
    
    #[regex(r".", priority = 1)]
    Unknown,
    
    #[regex(r"[\x00-\xFF]", priority = 0)]
    Error,  // ← Can catch invalid UTF-8, but doesn't validate Identifier!
}
```

**Problem:** The `Identifier` regex operates on **byte patterns** (Logos with `source = [u8]`), so it doesn't validate UTF-8.

**Solution:** Add validation in the lexer wrapper:

```rust
// crates/hwml-surface/src/lex.rs
impl<'input> Iterator for Lexer<'input> {
    type Item = (usize, Token, usize);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let token = self.inner.next()?;
            let span = self.inner.span();
            let slice = self.inner.slice();  // &[u8] from Logos

            // *** ADD UTF-8 VALIDATION HERE ***
            match token {
                Ok(Token::Identifier) | Ok(Token::Number) => {
                    // Validate UTF-8 for tokens that will become identifiers
                    if std::str::from_utf8(slice).is_err() {
                        // Report error with proper location
                        panic!(
                            "Invalid UTF-8 in identifier at {}:{} (bytes {:?})",
                            self.line, self.column, slice
                        );
                    }
                    // Continue with normal flow...
                }
                // ... rest of token handling
            }
        }
    }
}
```

**Better:** Extend `LexicalError` to include UTF-8 errors:

```rust
// crates/hwml-surface/src/lex.rs
#[derive(Default, Debug, Clone, PartialEq)]
pub enum LexicalError {
    #[default]
    InvalidToken,
    InvalidUtf8 {
        byte_offset: usize,
        invalid_bytes: Vec<u8>,
    },
}
```

Then return error instead of panicking:

```rust
match token {
    Ok(Token::Identifier) | Ok(Token::Number) => {
        if std::str::from_utf8(slice).is_err() {
            // This would require changing Lexer to return Result<Item, Error>
            // OR: Convert to Token::Error and let parser handle it
            return Some((span.start, Token::Error, span.end));
        }
    }
    // ...
}
```

---

### Phase 2: Update `hwml-core` Lexer (Core Language)

**File:** `crates/hwml-core/src/syn/parse.rs`

**Current state:** Tokens with String payloads use `.to_owned()` on slices:

```rust
#[regex(r"@(?&id)+(/(?&id)+)*", callback = |lex| lex.slice()["@".len()..].to_owned())]
Constant(String),
```

**Problem:** `.to_owned()` on `&[u8]` creates `Vec<u8>`, then implicitly converted to `String` **without validation**!

**This is a bug!** Logos callbacks should validate UTF-8.

**Solution:** Add validation in callbacks:

```rust
// Helper function for validated String extraction
fn validated_string(slice: &[u8]) -> String {
    match std::str::from_utf8(slice) {
        Ok(s) => s.to_owned(),
        Err(e) => panic!("Invalid UTF-8 in token: {:?} (error: {})", slice, e),
        // OR: Use Error token via callback return type
    }
}

#[derive(Logos, Clone, Debug, Eq, PartialEq, Hash)]
pub enum Token {
    #[regex(r"@(?&id)+(/(?&id)+)*", callback = |lex| {
        validated_string(&lex.slice()["@".len()..])
    })]
    Constant(String),
    
    // ... similar for Variable, Primitive
}
```

**Even better:** Change token payload to store `Box<str>` directly:

```rust
#[regex(r"@(?&id)+(/(?&id)+)*", callback = |lex| {
    let slice = &lex.slice()["@".len()..];
    std::str::from_utf8(slice)
        .expect("Invalid UTF-8 in constant")
        .into()
})]
Constant(Box<str>),  // ← Validated at lex time!
```

---

### Phase 3: Update `Word::from_utf8` to Use Unchecked Conversion

**File:** `crates/hwml-core/src/word.rs`

**Current:**
```rust
#[salsa::interned]
pub struct Word {
    #[return_ref]
    pub text: Box<str>,  // ← Correct storage!
}
```

**Add constructor that assumes pre-validated bytes:**

```rust
impl Word {
    /// Create Word from UTF-8 bytes with validation
    pub fn from_utf8<'db>(
        db: &'db dyn salsa::Database,
        bytes: &[u8],
    ) -> Result<Word<'db>, std::str::Utf8Error> {
        let text = std::str::from_utf8(bytes)?;
        Ok(Word::new(db, text))
    }
    
    /// Create Word from pre-validated UTF-8 bytes (unchecked)
    ///
    /// # Safety
    /// Caller must ensure `bytes` is valid UTF-8.
    /// This should only be called after lexer validation.
    pub unsafe fn from_utf8_unchecked<'db>(
        db: &'db dyn salsa::Database,
        bytes: &[u8],
    ) -> Word<'db> {
        let text = std::str::from_utf8_unchecked(bytes);
        Word::new(db, text)
    }
}
```

---

### Phase 4: Update All 15 Call Sites

Replace:
```rust
let text = String::from_utf8_lossy(bytes);
let word = Word::new(db, text.as_ref());
```

With:
```rust
// SAFETY: Lexer validated UTF-8
let word = unsafe { Word::from_utf8_unchecked(db, bytes) };
```

**All 15 locations:**
1. `crates/hwml-elab/src/scc.rs:245`
2. `crates/hwml-elab/src/util.rs:16`
3. `crates/hwml-elab/src/util.rs:34`
4. `crates/hwml-elab/src/scc_elab.rs:113`
5. `crates/hwml-elab/src/kernel/mod.rs:751`
6. `crates/hwml-elab/src/program.rs:233`
7. `crates/hwml-elab/src/program.rs:248`
8. `crates/hwml-elab/src/program.rs:263`
9. `crates/hwml-elab/src/elab/decl.rs:106`
10. `crates/hwml-elab/src/elab/decl.rs:241`
11. `crates/hwml-elab/src/elab/decl.rs:496`
12. `crates/hwml-elab/src/names.rs:20`
13. `crates/hwml-elab/tests/snap_tests.rs:42`
14. `crates/hwml-elab/src/elab/expr.rs:89`
15. (and 5 more in `expr.rs`)

---

## Testing Strategy

### 1. Unit Tests for Lexer Validation

```rust
#[test]
fn test_invalid_utf8_in_identifier() {
    let invalid = b"def caf\xFFe := 1";
    let result = parse(invalid);
    assert!(result.is_none());  // Should error, not silently fix
}

#[test]
fn test_valid_utf8_emoji_identifier() {
    let valid = "def 🔥_lit := 1";
    let result = parse(valid.as_bytes());
    assert!(result.is_some());
}
```

### 2. Integration Tests

```rust
#[test]
fn test_complex_utf8_identifiers() {
    let cases = vec![
        ("def café := 1", true),          // Valid UTF-8
        ("def 日本語 := 1", true),          // Japanese
        ("def 👨‍👩‍👧‍👦 := 1", true),  // ZWJ sequence
        (b"def caf\xFFe := 1", false),   // Invalid UTF-8
    ];
    // ...
}
```

---

## Summary of Changes

| Component | Current | New |
|-----------|---------|-----|
| **`hwml-surface` lexer** | No UTF-8 validation | Validate `Identifier`/`Number` tokens |
| **`hwml-core` lexer** | `.to_owned()` without validation | Validate in callbacks, use `Box<str>` |
| **`Word` storage** | `Box<str>` ✅ | Keep `Box<str>` ✅ |
| **`Word` constructor** | `new()` only | Add `from_utf8_unchecked()` |
| **Elaborator (15 sites)** | `from_utf8_lossy()` ❌ | `from_utf8_unchecked()` ✅ |

**Validation boundary:**
```
  User Source → Lexer (VALIDATES) → Parser → Elaborator (UNCHECKED) → Word
     [u8]          validates           [u8]     from_utf8_unchecked    Box<str>
                     UTF-8                            ↑
                                                 SAFE: lexer checked!
```

---

## Next Steps

1. Implement lexer validation (Phase 1 & 2)
2. Add `Word::from_utf8_unchecked()` (Phase 3)
3. Update all 15 call sites (Phase 4)
4. Add comprehensive tests
5. Document the invariant: "All `Id.value` bytes are valid UTF-8 after parsing"
