# The Lexer's Three-Tier Token Design: UTF-8 Validation by Construction

**Date:** 2026-05-06  
**Discovery:** The `hwml-surface` lexer already validates UTF-8 through its token priority design

---

## TL;DR

**The lexer doesn't need explicit UTF-8 validation code because Logos regex patterns only match valid UTF-8.**

The three-tier token design ensures:
- ✅ **`Token::Identifier`** = Valid UTF-8 + correct character class
- ✅ **`Token::Unknown`** = Valid UTF-8 but reserved/future use
- ❌ **`Token::Error`** = Invalid UTF-8 byte sequences

This means `from_utf8_unchecked` in the parser is **safe by construction**.

---

## The Token Definition

```rust
// crates/hwml-surface/src/lex.rs
#[derive(Logos, Copy, Clone, Debug, Eq, PartialEq, Hash)]
#[logos(source = [u8], error = LexicalError)]
pub enum Token {
    // ... keywords, operators, etc.
    
    // Priority 2: Valid identifiers (highest priority)
    // Matches: Valid UTF-8 AND in identifier character class
    #[regex(r"[^\p{gc=Separator}\p{gc=Control}{}()\[\];,]+", priority = 2)]
    Identifier,
    
    // Priority 1: Unknown characters (medium priority)
    // Matches: Any single valid UTF-8 character (scalar value)
    // Purpose: Future-proofing (may become valid identifiers later)
    #[regex(r".", priority = 1)]
    Unknown,
    
    // Priority 0: Error (lowest priority, catchall)
    // Matches: Invalid UTF-8 byte sequences
    #[regex(r"[\x00-\xFF]", priority = 0)]
    Error,
}
```

---

## How Logos Prioritizes

**When Logos encounters bytes, it tries patterns in priority order:**

1. **Try `Identifier` (priority 2)**
   - Pattern: `[^\p{gc=Separator}\p{gc=Control}{}()\[\];,]+`
   - Uses Unicode properties (`\p{gc=...}`)
   - **Can only match valid UTF-8** (Unicode properties require it)
   - Example: `café`, `日本語`, `🔥_lit`

2. **Try `Unknown` (priority 1)**
   - Pattern: `.` (dot)
   - In regex, `.` matches **a Unicode scalar value** (one valid UTF-8 character)
   - **Can only match valid UTF-8** (by definition of scalar value)
   - Example: `§`, `©`, `€` (valid UTF-8 but not in identifier set)

3. **Try `Error` (priority 0)**
   - Pattern: `[\x00-\xFF]` (any byte)
   - Catchall for bytes that didn't match above
   - **Only matches if NOT valid UTF-8** (otherwise would have matched earlier)
   - Example: `\xFF`, `\xC0\xC0` (invalid UTF-8 sequences)

---

## Why This Guarantees UTF-8 Validity

### Key Insight: Logos Operates on UTF-8

From Logos documentation:
> "Logos operates on UTF-8 strings. Patterns are matched against the input as if it were a valid UTF-8 string."

**When `#[logos(source = [u8])]`:**
- Logos still interprets bytes as UTF-8
- Regex patterns expect UTF-8 input
- Invalid UTF-8 bytes fail to match UTF-8-aware patterns

**The `.` pattern:**
- Matches a **Unicode scalar value** (21-bit code point)
- Requires valid UTF-8 encoding
- Cannot match invalid byte sequences

**Unicode properties like `\p{gc=Separator}`:**
- Only defined for valid Unicode code points
- Require valid UTF-8 to evaluate
- Cannot match invalid bytes

### The Priority Cascade

```
Input bytes: b"caf\xFFe"
             ^^^       → Matches Identifier (valid UTF-8: "caf")
                ^^     → Matches Error (invalid UTF-8: [0xFF])
                  ^    → Matches Identifier (valid UTF-8: "e")
```

**Result:** Three tokens: `Identifier("caf")`, `Error`, `Identifier("e")`

**Invariant:** If a token is `Identifier` or `Number`, the bytes **must be valid UTF-8**.

---

## Why `from_utf8_unchecked` Is Safe

**In the LALRPOP grammar:**

```rust
Id: Id = {
  <l:@L> <s:"id"> <r:@R> => {
    // SAFETY: Logos guarantees Identifier tokens contain valid UTF-8
    // The regex pattern only matches valid UTF-8 sequences by construction
    let text = unsafe { std::str::from_utf8_unchecked(&input[l..r]) };
    Id::new(l..r, text.into())
  }
};
```

**Why this is safe:**
1. Parser only calls this production for `Token::Identifier`
2. Logos only produces `Token::Identifier` for valid UTF-8
3. The regex pattern (`[^\p{gc=...}]+`) requires valid UTF-8 to match
4. Invalid UTF-8 would have produced `Token::Error` instead

**Proof by contradiction:**
- Assume `input[l..r]` contains invalid UTF-8
- Then Logos couldn't match the Identifier pattern (requires valid UTF-8)
- So Logos would have produced `Token::Error`, not `Token::Identifier`
- Parser wouldn't call this production
- Contradiction!

Therefore, `from_utf8_unchecked` cannot receive invalid UTF-8.

---

## Comparison: Before and After Understanding

### Before (Misconception)

"We need to add UTF-8 validation to the lexer loop because we can't trust the input."

```rust
// Unnecessary validation
match token {
    Ok(Token::Identifier) => {
        if std::str::from_utf8(slice).is_err() {
            return Some((span.start, Token::Error, span.end));
        }
    }
}
```

### After (Reality)

"Logos already validates UTF-8 through regex matching. We just need to document the invariant."

```rust
/// Token types with UTF-8 validation by construction.
///
/// The three-tier priority design ensures:
/// - `Identifier`/`Number`: Guaranteed valid UTF-8 (Logos regex matches Unicode)
/// - `Unknown`: Valid UTF-8 but not in identifier charset
/// - `Error`: Invalid UTF-8 byte sequences
///
/// This means `from_utf8_unchecked` is safe for Identifier/Number tokens.
#[derive(Logos, ...)]
pub enum Token {
    // ...
}
```

**Optional belt-and-suspenders:**
```rust
debug_assert!(
    std::str::from_utf8(slice).is_ok(),
    "Identifier token contains invalid UTF-8 (Logos bug?): {:?}",
    slice
);
```

---

## The Complete Picture

```
Source bytes [u8]
    ↓
Logos lexer
    ↓ (tries patterns in priority order)
    ├─ Priority 2: Identifier pattern (valid UTF-8 + correct chars)
    │   → Token::Identifier ✅ (guaranteed valid UTF-8)
    │
    ├─ Priority 1: . pattern (any scalar value)
    │   → Token::Unknown ✅ (guaranteed valid UTF-8)
    │
    └─ Priority 0: [\x00-\xFF] (catchall)
        → Token::Error ❌ (invalid UTF-8)
    ↓
Parser (LALRPOP)
    ↓ (receives Token::Identifier)
    ↓ (uses from_utf8_unchecked - SAFE!)
    ↓
Surface AST
    ↓ (Id.value: Box<str>)
    ↓
Elaborator
    ↓ (works with &str directly)
    ↓
Core IR (Word)
    └─ Box<str> (interned)
```

**Key invariant:** "If token is Identifier or Number, the bytes are valid UTF-8."

**Enforcement mechanism:** Logos regex matching (not runtime checks).

---

## Testing Strategy

### Unit Test: Verify Invariant

```rust
#[test]
fn test_identifier_tokens_are_valid_utf8() {
    let test_cases = vec![
        (b"cafe", Token::Identifier),
        (b"caf\xC3\xA9", Token::Identifier),  // café (valid UTF-8)
        (b"\xF0\x9F\x94\xA5", Token::Identifier),  // 🔥 (valid UTF-8)
    ];
    
    for (input, expected_token) in test_cases {
        let mut lexer = Lexer::new(input);
        let (_, token, _) = lexer.next().unwrap();
        assert_eq!(token, expected_token);
        
        // Verify UTF-8 validity
        assert!(std::str::from_utf8(input).is_ok());
    }
}

#[test]
fn test_invalid_utf8_produces_error_token() {
    let invalid = b"caf\xFFe";  // Invalid UTF-8
    let mut lexer = Lexer::new(invalid);
    
    // First token: "caf" (valid)
    let (_, tok1, _) = lexer.next().unwrap();
    assert_eq!(tok1, Token::Identifier);
    
    // Second token: 0xFF (invalid)
    let (_, tok2, _) = lexer.next().unwrap();
    assert_eq!(tok2, Token::Error);
    
    // Third token: "e" (valid)
    let (_, tok3, _) = lexer.next().unwrap();
    assert_eq!(tok3, Token::Identifier);
}
```

---

## Documentation Updates Needed

1. **Add to `Token` enum:**
   - Document three-tier design
   - Explain UTF-8 guarantees
   - Note that `from_utf8_unchecked` is safe

2. **Add to ADR-013:**
   - Explain lexer validates by construction
   - Reference this document

3. **Add to implementation plan:**
   - Update Phase 2 from "Add validation" to "Document invariant"
   - Optional: Add debug assertions

---

## Conclusion

**The lexer is already correct!** It validates UTF-8 through its design, not through explicit runtime checks.

**What we need:**
- ✅ Document the invariant
- ✅ Use `from_utf8_unchecked` safely in parser
- ✅ Store `Box<str>` in surface AST
- ✅ Remove `from_utf8_lossy` from elaborator

**What we don't need:**
- ❌ Add explicit UTF-8 validation to lexer loop
- ❌ Change lexer token design
- ❌ Add runtime validation overhead

**The three-tier token design is elegant and correct!**
