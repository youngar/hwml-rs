# ADR-013: UTF-8 as Internal String Representation

**Status:** Approved  
**Date:** 2026-05-06  
**Phase:** Phase 1.5 (In Progress)  
**Confidence:** 0.95  
**Deciders:** Architecture Team  
**Context Tags:** #lexer #parser #elaborator #string-handling #unicode

---

## Context

HWML needs to handle identifiers, module names, and other text throughout the compilation pipeline:
1. **Lexer** tokenizes source files (which may contain arbitrary bytes)
2. **Parser** builds surface syntax AST from tokens
3. **Elaborator** converts surface syntax to core IR, interning names
4. **Diagnostics** must report errors with correct source locations

**Constraints:**
- Must support full Unicode (including emojis, CJK characters, ZWJ sequences)
- Must provide clear error messages for invalid UTF-8 in source files
- Must maintain type safety throughout the pipeline
- Performance matters (string operations are frequent)
- Must work correctly with LSP (UTF-16 position encoding) and CLI (UTF-8 terminals)

**Problem:** What string representation should we use internally? Where should UTF-8 validation happen?

---

## Alternatives Considered

### Option 1: Raw Bytes Throughout (`&[u8]` / `Box<[u8]>`)

**How it works:**
- Lexer operates on `&[u8]`, produces tokens with byte slices
- Parser stores `Box<[u8]>` in surface AST
- Elaborator validates UTF-8 on-demand when creating interned `Word`
- Core IR stores validated `Box<str>` in `Word` (Salsa-interned)

**Pros:**
- Defers validation until needed
- Can handle partially-invalid source files (for IDE scenarios)
- No upfront validation cost

**Cons:**
- **Silent failures**: Current implementation uses `String::from_utf8_lossy()` which replaces invalid bytes with `�`, causing confusing "identifier not found" errors
- Validation scattered across elaborator (15+ call sites)
- Easy to forget validation (no type-level guarantee)
- Unsafe conversions needed throughout elaborator
- Harder to reason about invariants

**Sources:**
- Current HWML implementation (problematic)
- Analysis in `UTF8_CONVERSION_AUDIT.md` (found 15 `from_utf8_lossy` sites)

---

### Option 2: Validate Entire File Upfront, Use `&str` References

**How it works:**
- Parse function takes `&str` instead of `&[u8]`
- Validate entire file before lexing
- Surface AST uses `&'input str` references (zero-copy)
- Lifetime connects AST to input

**Pros:**
- Zero-copy parsing (no string allocations)
- Type-safe (`&str` guarantees UTF-8)
- Clear error point (before lexing starts)

**Cons:**
- **Lifetime pollution**: Surface AST would need `Program<'input>`, breaking architectural separation
- Surface syntax is an intermediate representation that outlives the input
- Can't report precise token-level locations for UTF-8 errors
- Less flexible for IDE scenarios (can't parse partial files with errors)
- Doesn't match production compiler architectures (rust-analyzer, GHC, Lean 4)

**Sources:**
- Considered during design discussion (2026-05-06)
- Rejected because surface AST has no lifetime parameter by design

---

### Option 3: Validate at Lexer, Own Validated Strings (CHOSEN)

**How it works:**
- Lexer uses Logos regex patterns that **only match valid UTF-8**
- Invalid UTF-8 bytes produce `Token::Error` (priority 0, catchall)
- Valid UTF-8 but non-identifier characters produce `Token::Unknown` (priority 1)
- **`Token::Identifier` and `Token::Number` are guaranteed valid UTF-8 by construction**
- Parser uses `from_utf8_unchecked` to convert validated bytes to `&str`
- Surface AST stores `Box<str>` (owned, validated)
- Elaborator works with `&str` directly (no validation needed)

**Pros:**
- **Type-safe**: `Box<str>` guarantees UTF-8 at compile time
- **Clear errors**: Invalid UTF-8 reported as `Token::Error` at lex time with line:column
- **Minimal unsafe**: Only 2 `from_utf8_unchecked` calls (in parser grammar)
- **No unsafe in elaborator**: Works with `&str` directly (15 call sites cleaned up)
- **Matches production compilers**: rust-analyzer (`SmolStr`), GHC (`FastString`), Lean 4 (`String`)
- **Flexible**: Can continue lexing after UTF-8 errors (for IDE scenarios)
- **Built-in validation**: Logos regex patterns only match valid UTF-8 by construction
- **Three-tier token design**: `Identifier` (valid), `Unknown` (valid UTF-8, wrong charset), `Error` (invalid UTF-8)

**Cons:**
- Parser has 2 `unsafe` blocks (but documented and localized)
- Slightly more complex lexer (adds validation step)
- Allocates `Box<str>` instead of `Box<[u8]>` (but same memory footprint)

**Sources:**
- rust-analyzer: Uses `SmolStr` (validated UTF-8, inline or `Arc<str>`)
- GHC: Uses `FastString` (Modified UTF-8, hash-consed)
- Lean 4: Uses `String` (UTF-8 `ByteArray` with invariant)
- Research document: `PRODUCTION_COMPILERS_UTF8_STORAGE.md`

---

## Decision

**Use validated UTF-8 strings internally** with this architecture:

```
Input [u8] → Lexer VALIDATES → Parser from_utf8_unchecked → Surface Box<str> → Word Box<str>
               UTF-8 ✓                  (grammar)              (type-safe!)     (interned)
                ↓ Error                     ↑ SAFE!
         Token::Error              (lexer guaranteed UTF-8)
```

**Validation boundary:** Lexer
**Internal representation:** `Box<str>` (surface syntax), `Box<str>` (core IR `Word`)
**Conversion strategy:** `from_utf8_unchecked` in parser (safe because lexer validated)
**Location tracking:** Byte ranges (`Range<usize>`), lazy conversion to line:column for diagnostics

---

## Rationale

### The Lexer's Three-Tier Token Design

The `hwml-surface` lexer has a clever priority-based token design that validates UTF-8 by construction:

```rust
// Priority 2: Valid identifiers (valid UTF-8 + correct character class)
#[regex(r"[^\p{gc=Separator}\p{gc=Control}{}()\[\];,]+", priority = 2)]
Identifier,

// Priority 1: Valid UTF-8 but not in identifier character set
// (future-proofing: may become valid identifiers later)
#[regex(r".", priority = 1)]
Unknown,

// Priority 0: Invalid UTF-8 bytes (catchall for non-UTF-8)
#[regex(r"[\x00-\xFF]", priority = 0)]
Error,
```

**How Logos prioritizes:**
1. First tries `Identifier` (priority 2) - **only matches valid UTF-8 sequences**
2. Falls back to `Unknown` (priority 1) - matches **any single valid UTF-8 character**
3. Falls back to `Error` (priority 0) - catches **invalid UTF-8 byte sequences**

**Key insight:** Because Logos operates on UTF-8 strings (not arbitrary bytes) and `.` matches a Unicode scalar value, `Identifier` and `Unknown` tokens are **guaranteed to be valid UTF-8 by construction**.

**This means:**
- ✅ **No explicit UTF-8 validation needed in lexer loop**
- ✅ **`Token::Identifier` is always valid UTF-8**
- ✅ **`Token::Number` is always valid UTF-8** (decimal digits are ASCII subset)
- ✅ **`Token::Error` signals invalid UTF-8 to parser**
- ✅ **`Token::Unknown` is valid UTF-8 but reserved for future use**

### Why Validate at Lexer?

1. **Already validated by Logos**: Regex patterns only match valid UTF-8 by design
2. **Three-tier design**: Separates valid identifiers, reserved characters, and invalid UTF-8
3. **Precise error locations**: Token-level errors show exactly which byte sequence is invalid
4. **Early failure**: Catch invalid UTF-8 before parsing starts
5. **Natural boundary**: Lexer already processes every byte, zero additional overhead
6. **Industry standard**: All production compilers validate at lex/parse boundary

### Why Store `Box<str>` in Surface AST?

1. **Type safety**: Rust's type system enforces UTF-8 validity at compile time
2. **No lifetimes needed**: Surface AST is owned data that outlives input
3. **Cleaner elaborator**: Works with `&str` directly, no conversions needed
4. **Matches core IR**: `Word` stores `Box<str>`, so no conversion needed

### Why `from_utf8_unchecked` in Parser?

1. **Performance**: Zero-cost conversion (no validation overhead)
2. **Safety**: Lexer guarantees UTF-8 validity, so unchecked is safe
3. **Localized**: Only 2 call sites (Id and Num productions in LALRPOP grammar)
4. **Documented**: Clear SAFETY comments explain invariant

### Production Compiler Evidence

**rust-analyzer** stores validated UTF-8:
```rust
pub struct SmolStr(Repr);
enum Repr {
    Inline { buf: [u8; 23] },  // Valid UTF-8
    Heap(Arc<str>),            // Valid UTF-8
}
```

**GHC** stores validated Modified UTF-8:
```haskell
data FastString = FastString {
    buf :: ByteString  -- Modified UTF-8 encoding (validated)
}
```

**Lean 4** stores validated UTF-8:
```lean
def String.fromUTF8? (a : ByteArray) : Option String :=
  if a.isValidUTF8 then some (fromUTF8Unchecked a) else none
```

**All validate at boundary, store validated strings, use unchecked conversion internally.**

---

## Consequences

### Positive

✅ **Type safety**: `Box<str>` in surface AST prevents invalid UTF-8 from propagating  
✅ **Clear errors**: Invalid UTF-8 reported at lex time with precise locations  
✅ **Less unsafe code**: Only 2 unsafe blocks (in parser) vs 15+ (scattered in elaborator)  
✅ **Better diagnostics**: Can show exactly which identifier is invalid  
✅ **Industry alignment**: Matches rust-analyzer, GHC, Lean 4 architectures  
✅ **Cleaner elaborator**: Works with `&str` directly, no conversions needed  

### Negative

⚠️ **Lexer complexity**: Adds UTF-8 validation step to lexer loop  
⚠️ **Parser unsafe**: Uses `from_utf8_unchecked` (but safe and documented)  
⚠️ **Memory**: Stores `Box<str>` instead of `Box<[u8]>` (but same size)

### Trade-offs

**Performance vs Safety:**
- Trade: Validate once at lexer (small cost) for type-safe pipeline (large benefit)
- Result: Net positive (avoid repeated validation in elaborator)

**Flexibility vs Simplicity:**
- Trade: Lexer can continue after UTF-8 errors (for IDE) vs simpler "fail fast"
- Result: More flexible (better IDE experience)

**Localized Unsafe vs Scattered Unsafe:**
- Trade: 2 documented `unsafe` blocks in parser vs 15+ potential `unsafe` in elaborator
- Result: Much safer (smaller surface area for bugs)

---

## Implementation

**Phase:** Phase 1.5 (In Progress)  
**Crates:**
- `hwml-surface` (lexer, parser, syntax types)
- `hwml-elab` (elaborator call sites)

**Files Modified:**
- `crates/hwml-surface/src/syntax.rs` (Id, Num use `Box<str>`)
- `crates/hwml-surface/src/lex.rs` (add UTF-8 validation)
- `crates/hwml-surface/src/grammar.lalrpop` (use `from_utf8_unchecked`)
- `crates/hwml-elab/src/names.rs` (accept `&str` instead of `&[u8]`)
- `crates/hwml-elab/src/*.rs` (15 call sites updated)

**Status:** Planned (tasks created, implementation plan documented)

---

## Related Decisions

- [[ADR-001-lcf-kernel]] - Kernel works with interned `Word` (validates UTF-8)
- [[ADR-005-debug-information]] - Diagnostics need precise source locations (UTF-8 errors benefit)
- [[ADR-008-vfs-abstraction]] - VFS provides source bytes, lexer validates

## Related Research

- [[research/utf8-diagnostics-rendering]] - Full UTF-8 support in diagnostics, LSP UTF-16 encoding
- `PRODUCTION_COMPILERS_UTF8_STORAGE.md` - How rust-analyzer, GHC, Lean 4 store strings
- `UTF8_CONVERSION_AUDIT.md` - Analysis of 15 problematic `from_utf8_lossy` sites

## References

### External Projects

- **rust-analyzer**: `smol_str` crate (https://github.com/rust-analyzer/smol_str)
- **GHC**: `FastString` implementation (https://hackage.haskell.org/package/ghc/docs/GHC-Data-FastString.html)
- **Lean 4**: `String` representation (https://lean-lang.org/doc/reference/latest/Basic-Types/Strings/)

### Standards

- **Unicode Standard Annex #31**: Identifier and Pattern Syntax
- **LSP Specification 3.17**: `PositionEncodingKind` (UTF-8, UTF-16, UTF-32)
- **RFC 3629**: UTF-8, a transformation format of ISO 10646

---

## Status History

- 2026-05-06: Proposed after research and codebase audit
- 2026-05-06: Approved (architecture team consensus)
- 2026-05-06: Implementation tasks created
