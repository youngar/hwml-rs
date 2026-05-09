# Implementation Plan: UTF-8 Validation at Lexer → Box<str> in Surface Syntax

**Date:** 2026-05-06  
**Decision:** Validate UTF-8 at lexer, use `from_utf8_unchecked` in parser, store `Box<str>` in surface syntax

---

## Goals

1. ✅ Validate UTF-8 once at lexer boundary
2. ✅ Use `from_utf8_unchecked` in parser (safe because lexer validated)
3. ✅ Store `Box<str>` in surface syntax (type-safe)
4. ✅ Eliminate `from_utf8_lossy` from elaborator (no unsafe needed)

---

## Changes Required

### Phase 1: Update Surface Syntax Types

**File:** `crates/hwml-surface/src/syntax.rs`

**Change 1: Id**
```rust
// BEFORE
pub struct Id {
    pub loc: Range<usize>,
    pub value: Box<[u8]>,
}

// AFTER
pub struct Id {
    pub loc: Range<usize>,
    pub value: Box<str>,  // ✅ Changed from Box<[u8]>
}
```

**Change 2: Num**
```rust
// BEFORE
pub struct Num {
    pub loc: Range<usize>,
    pub value: Box<[u8]>,
}

// AFTER
pub struct Num {
    pub loc: Range<usize>,
    pub value: Box<str>,  // ✅ Changed from Box<[u8]>
}
```

**Change 3: Update Id::segments()**
```rust
// BEFORE
impl Id {
    pub fn segments(&self) -> impl Iterator<Item = &[u8]> {
        self.value.split(|&b| b == b'.')
    }
}

// AFTER
impl Id {
    pub fn segments(&self) -> impl Iterator<Item = &str> {
        self.value.split('.')
    }
}
```

---

### Phase 2: Document Lexer's UTF-8 Guarantees

**File:** `crates/hwml-surface/src/lex.rs`

**Good news: The lexer ALREADY validates UTF-8 by construction!**

The three-tier token design ensures UTF-8 validity:
```rust
// Priority 2: Valid UTF-8 + correct character class
#[regex(r"[^\p{gc=Separator}\p{gc=Control}{}()\[\];,]+", priority = 2)]
Identifier,

// Priority 1: Valid UTF-8 but reserved
#[regex(r".", priority = 1)]  // . matches Unicode scalar value
Unknown,

// Priority 0: Invalid UTF-8
#[regex(r"[\x00-\xFF]", priority = 0)]
Error,
```

**Why this works:**
- Logos operates on UTF-8 strings internally
- The `.` regex matches a **Unicode scalar value** (valid UTF-8)
- Identifier regex uses Unicode properties (`\p{gc=...}`) which require valid UTF-8
- If bytes aren't valid UTF-8, Logos can't match Identifier or Unknown, so falls to Error

**Action: Add documentation:**
```rust
/// Lexer token types with UTF-8 validation by construction.
///
/// The three-tier priority design ensures:
/// - `Identifier` and `Number`: Guaranteed valid UTF-8 (Logos regex matches Unicode)
/// - `Unknown`: Valid UTF-8 but not in identifier character set (future-proofing)
/// - `Error`: Invalid UTF-8 byte sequences (catchall)
///
/// This means `from_utf8_unchecked` is safe for Identifier/Number tokens.
#[derive(Logos, Copy, Clone, Debug, Eq, PartialEq, Hash)]
#[logos(source = [u8], error = LexicalError)]
pub enum Token {
    // ...
}
```

**Optional: Add explicit validation check (belt-and-suspenders):**
```rust
// In Lexer::next(), add debug assertion:
match token {
    Ok(Token::Identifier) | Ok(Token::Number) => {
        debug_assert!(
            std::str::from_utf8(slice).is_ok(),
            "Identifier/Number token contains invalid UTF-8: {:?}",
            slice
        );
    }
    _ => {}
}
```

---

### Phase 3: Update LALRPOP Grammar

**File:** `crates/hwml-surface/src/grammar.lalrpop`

**Change Id production:**
```rust
// BEFORE
Id: Id = {
  <l:@L> <s:"id"> <r:@R> => {
    Id::new(l..r, Box::from(&input[l..r]))
  }
};

// AFTER
Id: Id = {
  <l:@L> <s:"id"> <r:@R> => {
    // SAFETY: Lexer validated UTF-8 for Identifier token
    let text = unsafe { std::str::from_utf8_unchecked(&input[l..r]) };
    Id::new(l..r, text.into())
  }
};
```

**Change Num production:**
```rust
// BEFORE
Num: Num = {
  <l:@L> <s:"num"> <r:@R> => {
    Num::new(l..r, Box::from(&input[l..r]))
  }
};

// AFTER
Num: Num = {
  <l:@L> <s:"num"> <r:@R> => {
    // SAFETY: Lexer validated UTF-8 for Number token
    let text = unsafe { std::str::from_utf8_unchecked(&input[l..r]) };
    Num::new(l..r, text.into())
  }
};
```

---

### Phase 4: Update Elaborator (Remove Unsafe!)

**File:** `crates/hwml-elab/src/names.rs`

**Change function signature and body:**
```rust
// BEFORE
pub fn bytes_to_simple_qname<'db>(
    db: &'db dyn salsa::Database,
    namespace: Option<QualifiedName<'db>>,
    segment: &[u8],
) -> QualifiedName<'db> {
    let text = String::from_utf8_lossy(segment);  // ❌ Silent masking
    let word = Word::new(db, text.as_ref());
    // ...
}

// AFTER
pub fn str_to_simple_qname<'db>(
    db: &'db dyn salsa::Database,
    namespace: Option<QualifiedName<'db>>,
    segment: &str,  // ✅ Changed from &[u8]
) -> QualifiedName<'db> {
    let word = Word::new(db, segment);  // ✅ No conversion needed!
    let atom = Atom::new(word);
    let name = Name::new(db, Fixity::Closed, Box::from([atom]));
    QualifiedName::new(db, namespace, name)
}
```

**Similar pattern for `path_to_qname`:**
```rust
// BEFORE
pub fn path_to_qname<'db>(
    db: &'db dyn salsa::Database,
    namespace: Option<QualifiedName<'db>>,
    path: &[u8],
) -> QualifiedName<'db> {
    let segments: Vec<&[u8]> = path.split(|&b| b == b'.').collect();
    // ...
}

// AFTER
pub fn path_to_qname<'db>(
    db: &'db dyn salsa::Database,
    namespace: Option<QualifiedName<'db>>,
    path: &str,  // ✅ Changed from &[u8]
) -> QualifiedName<'db> {
    let segments: Vec<&str> = path.split('.').collect();  // ✅ str split, not bytes
    let mut current = namespace;
    for seg in segments {
        current = Some(str_to_simple_qname(db, current, seg));
    }
    current.expect("path must be non-empty")
}
```

---

### Phase 5: Update All Call Sites

**Files with `from_utf8_lossy` calls (15 total):**

Replace pattern:
```rust
// OLD
let text = String::from_utf8_lossy(&id.value);
let word = Word::new(db, text.as_ref());

// NEW
let word = Word::new(db, &id.value);  // id.value is now &str!
```

**Specific files to update:**
1. `crates/hwml-elab/src/scc.rs:245`
2. `crates/hwml-elab/src/util.rs:16, 34`
3. `crates/hwml-elab/src/scc_elab.rs:113`
4. `crates/hwml-elab/src/kernel/mod.rs:751`
5. `crates/hwml-elab/src/program.rs:233, 248, 263`
6. `crates/hwml-elab/src/elab/decl.rs:106, 241, 496`
7. `crates/hwml-elab/src/elab/expr.rs:89, 127, 140, 173, 369`
8. `crates/hwml-elab/tests/snap_tests.rs:42`

---

## Testing

### Unit Tests

**File:** `crates/hwml-surface/src/lex.rs` (add tests)

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_valid_utf8_identifier() {
        let input = b"cafe";
        let lexer = Lexer::new(input);
        let tokens: Vec<_> = lexer.collect();
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].1, Token::Identifier);
    }

    #[test]
    fn test_invalid_utf8_identifier() {
        let input = b"caf\xFFe";  // Invalid UTF-8
        let lexer = Lexer::new(input);
        let tokens: Vec<_> = lexer.collect();
        // Should produce Error token
        assert!(tokens.iter().any(|(_, tok, _)| *tok == Token::Error));
    }

    #[test]
    fn test_emoji_identifier() {
        let input = "🔥_lit".as_bytes();
        let lexer = Lexer::new(input);
        let tokens: Vec<_> = lexer.collect();
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].1, Token::Identifier);
    }
}
```

---

## Migration Checklist

- [ ] Phase 1: Update `Id` and `Num` to use `Box<str>`
- [ ] Phase 2: Add UTF-8 validation to lexer
- [ ] Phase 3: Update LALRPOP grammar to use `from_utf8_unchecked`
- [ ] Phase 4: Update `names.rs` helper functions
- [ ] Phase 5: Update all 15 call sites in elaborator
- [ ] Add tests for valid/invalid UTF-8
- [ ] Run full test suite
- [ ] Update documentation

---

## Expected Outcome

**Before:**
- Lexer: Implicit validation via regex ⚠️ (not documented)
- Parser: Stores `Box<[u8]>` ❌ (loses UTF-8 guarantee)
- Elaborator: 15 `from_utf8_lossy` calls ❌ (silent masking)

**After:**
- Lexer: Validates UTF-8 by construction ✅ (three-tier token design, documented)
- Parser: 2 `from_utf8_unchecked` calls ✅ (safe because lexer guarantees)
- Surface: Stores `Box<str>` ✅ (type-safe, carries UTF-8 guarantee)
- Elaborator: 0 UTF-8 conversions ✅ (just use `&str`)
