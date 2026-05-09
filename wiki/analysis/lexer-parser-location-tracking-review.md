# Lexer and Parser Location Tracking Review

**Date:** 2026-05-06
**Purpose:** Review of byte-level span usage in lexer, parser, and AST
**Status:** ✅ Excellent - Following standard patterns correctly

---

## Executive Summary

The HWML lexer and parser are **correctly using byte-level spans** for location tracking, following standard Logos and LALRPOP patterns. The implementation is well-designed with:

✅ **Byte-level lexing** - Logos operates on `&[u8]`
✅ **UTF-8 validation at boundary** - Three-tier token design
✅ **Byte-based spans** - LALRPOP uses `@L` and `@R` for byte offsets
✅ **Surface AST stores byte ranges** - `Range<usize>` in all syntax nodes
✅ **Lazy line:column conversion** - Only when needed for diagnostics/LSP
✅ **No location tracking in core IR** - Keeps core AST lightweight

---

## 1. Lexer Analysis (`hwml-surface/src/lex.rs`)

### ✅ Correctly Using Byte-Level Lexing

```rust
#[derive(Logos, Copy, Clone, Debug, Eq, PartialEq, Hash)]
#[logos(source = [u8], error = LexicalError)]
pub enum Token {
    // ... tokens
}
```

**Standard Pattern:** ✅ Using `#[logos(source = [u8])]` for byte-level input

### ✅ Three-Tier UTF-8 Validation Design

```rust
// Priority 2: Valid identifiers (valid UTF-8 + correct character class)
#[regex(r"[^\p{gc=Separator}\p{gc=Control}{}()\[\];,]+", priority = 2)]
Identifier,

// Priority 1: Valid UTF-8 but not identifier charset
#[regex(r".", priority = 1)]
Unknown,

// Priority 0: Invalid UTF-8 bytes (catchall)
#[regex(r"[\x00-\xFF]", priority = 0)]
Error,
```

**Analysis:**
- ✅ Logos regex patterns only match valid UTF-8 by construction
- ✅ `Token::Identifier` and `Token::Number` guaranteed valid UTF-8
- ✅ Invalid UTF-8 produces `Token::Error` (priority 0 catchall)
- ✅ Allows safe `from_utf8_unchecked` in parser

### ✅ Standard Lexer Design

**Lexer** (for LALRPOP):
```rust
impl Iterator for Lexer<'_> {
    type Item = (usize, Token, usize);  // (start_byte, token, end_byte)
}
```

**Analysis:**
- ✅ Returns byte offsets for LALRPOP
- ✅ Stores byte-based spans in surface AST
- ✅ `LocLexer` exists for optional streaming line:column tracking
- ✅ Current design: Use `Lexer`, convert to line:column lazily when needed

---

## 2. Parser Analysis (`hwml-surface/src/grammar.lalrpop`)

### ✅ Standard LALRPOP Byte Offset Pattern

```lalrpop
extern {
  type Location = usize;  // ✅ Byte offsets
  enum Token { /* ... */ }
}
```

**Standard Pattern:** ✅ LALRPOP's `Location` type is `usize` (byte offset)

### ✅ Using `@L` and `@R` for Byte Spans

```lalrpop
Id: Id = {
  <l:@L> <s:"id"> <r:@R> => {
    // SAFETY: Lexer guarantees valid UTF-8
    let text = unsafe { std::str::from_utf8_unchecked(&input[l..r]) };
    Id::new(l..r, Box::from(text))
  }
}
```

**Analysis:**
- ✅ `@L` = start byte offset
- ✅ `@R` = end byte offset
- ✅ `input[l..r]` slices input bytes
- ✅ `from_utf8_unchecked` is safe (lexer validated UTF-8)
- ✅ Stores both byte range (`l..r`) and validated string (`Box<str>`)

### ✅ Storing Byte Ranges

```lalrpop
Def: Def = {
    <l:@L> "def" <id:Id> <bs:OptionalBindings> <ty:(":" Expr0)?> ":=" <value:Expr0> <r:@R> => {
        Def::new(l..r, id, bs, ty.map(|(_, expr)| expr), value)
    }
};
```

**Analysis:**
- ✅ Captures byte offsets from LALRPOP (`l`, `r`)
- ✅ Stores `Range<usize>` directly in AST nodes
- ✅ No line:column conversion during parsing
- ✅ Conversion happens lazily when needed (diagnostics, LSP)

---

## 3. Surface AST Analysis (`hwml-surface/src/syntax.rs`)

### ✅ Byte Range Storage (Standard Pattern)

```rust
pub struct Def {
    pub loc: Range<usize>,  // Byte range
    pub id: Id,
    pub bindings: Bindings,
    pub ty: Option<Box<Expression>>,
    pub value: Box<Expression>,
}
```

**Analysis:**
- ✅ All surface AST nodes store `loc: Range<usize>` (byte offsets)
- ✅ Simple, lightweight, deterministic
- ✅ No pre-computation needed during parsing
- ✅ Conversion to line:column happens lazily when needed

**Note:** `Namespace` has experimental `line_col: LineColRange` field, but this is
being deprecated in favor of the byte-range-only approach.

### ✅ Validated UTF-8 Strings

```rust
pub struct Id {
    pub loc: Range<usize>,
    pub value: Box<str>,  // Validated UTF-8
}

pub struct Num {
    pub loc: Range<usize>,
    pub value: Box<str>,  // Validated UTF-8
}
```

**Analysis:**
- ✅ `Box<str>` guarantees valid UTF-8
- ✅ Safe because lexer validated at boundary
- ✅ Type system prevents invalid UTF-8 from propagating

---

## 4. Core AST Analysis (`hwml-core/src`)

### ✅ No Location Tracking in Core IR (By Design)

```rust
pub enum Syntax<'db> {
    UniverseCode(usize),
    PiCode(RcSyntax<'db>, BindingSyntax<'db>),
    Lambda(Lambda<'db>),
    Application(Application<'db>),
    // ... NO location fields!
}
```

**Analysis:**
- ✅ **Intentionally lightweight** - Core IR has no location tracking
- ✅ Keeps core AST types small and focused
- ✅ Location information maintained separately when needed
- ✅ Follows principle: error reporting uses surface AST locations

**Rationale:**
- Core IR is the elaborated, type-checked representation
- Location tracking belongs at the surface syntax level
- Error messages reference surface AST spans, not core IR
- Avoids threading location data through normalization/evaluation

### ✅ SourceRange for Error Reporting

```rust
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct SourceRange<'db> {
    pub source: Source<'db>,
    pub range: Range<usize>,  // Byte offsets
}
```

**Analysis:**
- ✅ Used for error reporting when needed
- ✅ Stores byte ranges (not line:column)
- ✅ Attached to errors, not to AST nodes
- ✅ Can be converted to line:column lazily for display

---

## 5. Lazy Conversion Infrastructure

### ✅ LineInfo for On-Demand Conversion

```rust
// From hwml-support crate
pub struct LineInfo {
    line_breaks: Vec<usize>,
}

impl LineInfo {
    pub fn from_bytes(input: &[u8]) -> Self { /* ... */ }

    pub fn loc(&self, offset: usize) -> (usize, usize) {
        // Binary search: O(log N)
    }
}
```

**Analysis:**
- ✅ Used **only** when converting byte offsets to line:column for display
- ✅ **Not** used during parsing (avoids O(N) pre-computation)
- ✅ Created lazily when diagnostics/LSP need line:column positions
- ✅ Binary search O(log N) for byte → line:column conversion

**Usage Pattern:**
```rust
// During parsing: store byte ranges
let ast = parse(input);  // AST contains Range<usize>

// Later, for diagnostics:
let line_info = LineInfo::from_bytes(input);
let (line, col) = line_info.loc(ast.node.loc.start);
eprintln!("Error at {}:{}", line + 1, col + 1);
```

---

## 6. Architecture Decisions & Rationale

### ✅ Decision: Byte-Level Spans Only

**What:** Store `Range<usize>` (byte offsets) in all AST nodes, convert to line:column lazily

**Why:**
1. **Performance** - No O(N) line break scanning during parsing
2. **Deterministic** - Same file always produces same byte offsets
3. **LSP-compatible** - Can convert to UTF-8 or UTF-16 encoding on demand
4. **MLIR-ready** - Can convert to 1-based line:column when lowering to CIRCT
5. **Simple** - No threading of line tracking state through parser

**Trade-off:**
- ✅ Fast parsing (no line scanning)
- ✅ Small AST (no line:column storage)
- ⚠️ Diagnostic rendering needs lazy LineInfo construction (acceptable cost)

### ✅ Decision: No Locations in Core IR

**What:** Core `Syntax<'db>` variants have no location fields

**Why:**
1. **Separation of concerns** - Core IR is semantic, locations are syntactic
2. **Smaller data structures** - Core IR used extensively in type checking/normalization
3. **Error reporting pattern** - Errors reference surface AST spans via separate mapping
4. **Elaboration traces** - Can maintain surface → core mapping separately if needed

**Trade-off:**
- ✅ Lightweight core IR
- ✅ No location threading through elaborator/evaluator
- ⚠️ Error messages reference surface AST (requires maintaining mapping)

### ✅ Decision: UTF-8 Validation at Lexer Boundary

**What:** Three-tier token design validates UTF-8 during lexing, stores `Box<str>` in AST

**Why:**
1. **Type safety** - `Box<str>` prevents invalid UTF-8 from propagating
2. **Clear errors** - Invalid UTF-8 reported at lex time with byte offset
3. **Safe unchecked conversion** - Parser can use `from_utf8_unchecked` safely
4. **Industry standard** - Matches rust-analyzer, GHC, Lean 4 approach

**Trade-off:**
- ✅ Type-safe UTF-8 throughout pipeline
- ✅ Clear error messages for invalid UTF-8
- ⚠️ 2 `unsafe` blocks in parser (but safe and documented)

---

## 7. Recommendations

### Immediate Actions

1. **Clean Up Experimental Code**
   - Remove `LineColRange` type from `hwml-surface/src/syntax.rs`
   - Remove `line_col` field from `Namespace` struct
   - Remove `ParserContext::range_to_line_col()` method
   - Keep only byte-range storage pattern

2. **Fix Error Handling**
   ```rust
   // Current: panics on invalid UTF-8
   Err(_err) => panic!("Lexical error at {}:{}", self.line, self.column);

   // Recommended: return Error token
   Err(_) => return Some((span.start, Token::Error, span.end));
   ```

3. **Document the Pattern**
   - Add doc comments explaining byte-range-only approach
   - Document lazy conversion pattern for diagnostics
   - Reference this analysis in code comments

### When Implementing Diagnostics

4. **Lazy LineInfo Construction**
   ```rust
   fn format_diagnostic(input: &[u8], span: Range<usize>, msg: &str) -> String {
       let line_info = LineInfo::from_bytes(input);
       let (line, col) = line_info.loc(span.start);
       format!("Error at {}:{}: {}", line + 1, col + 1, msg)
   }
   ```

5. **LSP Position Encoding**
   - Build `LineInfo` once per file when LSP requests diagnostics
   - Convert byte offsets to UTF-8 positions (negotiate encoding with client)
   - Cache `LineInfo` per file in LSP server state

---

## 8. Conclusion

**Overall Assessment:** ✅ **Correct architecture - byte ranges only**

The lexer and parser are correctly following standard Logos/LALRPOP patterns:
- ✅ Byte-level lexing with `#[logos(source = [u8])]`
- ✅ UTF-8 validation at lexer boundary (three-tier design)
- ✅ LALRPOP `@L`/`@R` for byte offsets
- ✅ Safe `from_utf8_unchecked` (guaranteed by lexer)
- ✅ Byte ranges stored in surface AST
- ✅ No location tracking in core IR
- ✅ Lazy line:column conversion when needed

**Implementation Status:**
- ✅ Byte-level lexing: **Complete**
- ✅ UTF-8 validation: **Complete**
- ✅ Surface AST byte ranges: **Complete**
- ✅ Core IR (no locations): **Complete**
- 🧹 Cleanup needed: Remove experimental `LineColRange` code

**Key Insight:** This is the **standard pattern** for compilers that use Logos + LALRPOP.
Byte offsets during parsing, lazy conversion to line:column for display. No need to change.
