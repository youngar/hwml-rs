# ADR-014: Byte-Level Location Tracking

**Status:** Approved  
**Date:** 2026-05-06  
**Phase:** Phase 1.5 (Implemented)  
**Confidence:** 0.95  
**Deciders:** Architecture Team  
**Context Tags:** #lexer #parser #location-tracking #diagnostics

---

## Context

HWML needs location information for error reporting and LSP integration. The question is:
**What location representation should we use, and where should we store it?**

### Requirements:
- Precise error messages with file, line, and column information
- LSP integration (UTF-16 or UTF-8 position encoding)
- MLIR/CIRCT integration (1-based line:column)
- Efficient parsing (no unnecessary overhead)
- Support for Unicode (emoji, combining characters, etc.)

### Alternatives Considered:
1. **Line:Column in AST** - Store `Position` structs with 1-based line:column in every node
2. **Byte ranges in AST** - Store `Range<usize>` and convert lazily to line:column
3. **No locations at all** - Rely on external tooling for source mapping

---

## Decision

**Use byte-level spans (`Range<usize>`) in surface AST, with lazy conversion to line:column.**

### Architecture:

```
┌─────────────────────────────────────────────────────────────────┐
│ INPUT: &[u8]                                                    │
└─────────────────────────────────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│ LEXER: Logos                                                    │
│ - Operates on bytes                                             │
│ - Validates UTF-8 (three-tier token design)                     │
│ - Returns (start_byte, Token, end_byte)                         │
└─────────────────────────────────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│ PARSER: LALRPOP                                                 │
│ - Uses @L and @R for byte offsets                               │
│ - Stores Range<usize> in AST nodes                              │
│ - NO line:column tracking during parsing                        │
└─────────────────────────────────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│ SURFACE AST                                                     │
│ - Every node has `loc: Range<usize>`                            │
│ - Strings are `Box<str>` (validated UTF-8)                      │
│ - Byte ranges reference input bytes                             │
└─────────────────────────────────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│ CORE IR (Elaborated)                                            │
│ - NO location fields                                            │
│ - Lightweight, semantic representation                          │
│ - Errors reference surface AST nodes                            │
└─────────────────────────────────────────────────────────────────┘
                            │
                            ▼ (when error occurs)
┌─────────────────────────────────────────────────────────────────┐
│ DIAGNOSTIC RENDERING                                            │
│ - Build LineInfo from input: LineInfo::from_bytes(&input)       │
│ - Convert byte offset to (line, col): line_info.loc(offset)     │
│ - Format error with line:column information                     │
│ - For LSP: convert to UTF-16 if client doesn't support UTF-8    │
└─────────────────────────────────────────────────────────────────┘
```

---

## Rationale

### Why Byte Ranges in AST?

1. **Performance - No Parsing Overhead**
   - No need to scan input for line breaks during parsing
   - Logos naturally produces byte offsets (`span.start`, `span.end`)
   - LALRPOP `@L` and `@R` are byte offsets by default
   - Zero additional computation during parsing

2. **Deterministic**
   - Same input always produces same byte offsets
   - No ambiguity about what "column" means (it's byte offset within line)
   - Easy to test and debug

3. **LSP Compatible**
   - Can convert to UTF-8 positions (byte offset = character offset)
   - Can convert to UTF-16 positions (count UTF-16 code units)
   - Negotiable encoding with LSP 3.17+ clients

4. **MLIR/CIRCT Compatible**
   - Can convert to 1-based line:column when lowering to MLIR
   - `FileLineColLoc` expects byte-based column offsets anyway

5. **Simple Implementation**
   - Rust's `Range<usize>` is 16 bytes (2 pointers)
   - No custom types needed
   - No threading of line-tracking state through parser

### Why No Locations in Core IR?

1. **Separation of Concerns**
   - Core IR is semantic (types, terms, values)
   - Locations are syntactic (source positions)
   - Mixing these violates single responsibility principle

2. **Performance**
   - Core IR used extensively in type checking, normalization, evaluation
   - Adding location fields increases size of every term
   - Most core IR operations don't need locations

3. **Error Reporting Pattern**
   - Errors reference surface AST nodes (which have locations)
   - Elaborator maintains mapping: core term → surface node
   - When error occurs, look up surface node, get byte range, convert to line:column

4. **Industry Practice**
   - GHC: Core has no locations (errors reference source positions separately)
   - Lean 4: Core has no locations (InfoTree maintains mapping)
   - Rust: MIR has no spans (errors reference HIR spans)

### Why Lazy Line:Column Conversion?

1. **Avoids O(N) Pre-computation**
   - Building `LineInfo` requires scanning input for line breaks
   - Only needed when displaying errors (not on happy path)
   - Most successful parses never need line:column information

2. **Cheap Conversion When Needed**
   - Binary search: O(log N) where N = number of lines
   - Typical files have < 10,000 lines, so ~13 comparisons
   - Negligible cost compared to I/O and parsing

3. **Flexible Output Formats**
   - Can convert to 0-based (Rust convention)
   - Can convert to 1-based (MLIR, LSP UTF-8)
   - Can convert to UTF-16 (LSP fallback)

---

## Consequences

### Positive

✅ **Fast parsing** - No line tracking overhead  
✅ **Small AST** - `Range<usize>` is just 16 bytes  
✅ **Deterministic** - Same input → same offsets  
✅ **LSP compatible** - Convert on demand to UTF-8/UTF-16  
✅ **MLIR compatible** - Convert to 1-based line:column when lowering  
✅ **Simple implementation** - Standard Logos + LALRPOP pattern  
✅ **No core IR bloat** - Core IR stays lightweight  

### Negative

⚠️ **Lazy conversion cost** - O(N) to build `LineInfo`, O(log N) per lookup  
⚠️ **Separate error mapping** - Need to maintain surface → core mapping for errors  

### Trade-offs

**Fast Parsing vs Lazy Diagnostics:**
- Most parses succeed and never need line:column
- Worth paying conversion cost only on error path
- **Winner:** Lazy conversion

**Simple AST vs Rich Locations:**
- Rich locations (file + line + column) are ~40 bytes
- Byte ranges are 16 bytes
- Core IR doesn't need locations at all
- **Winner:** Simple byte ranges

---

## Implementation

### Surface AST Node Pattern

```rust
pub struct Def {
    pub loc: Range<usize>,  // Byte range in input
    pub id: Id,
    pub bindings: Bindings,
    pub ty: Option<Box<Expression>>,
    pub value: Box<Expression>,
}
```

### Parser Pattern (LALRPOP)

```lalrpop
Def: Def = {
    <l:@L> "def" <id:Id> <bs:OptionalBindings> <ty:(":" Expr0)?> ":=" <value:Expr0> <r:@R> => {
        Def::new(l..r, id, bs, ty.map(|(_, expr)| expr), value)
    }
};
```

### Diagnostic Rendering Pattern

```rust
fn format_error(input: &[u8], span: Range<usize>, msg: &str) -> String {
    let line_info = LineInfo::from_bytes(input);
    let (line, col) = line_info.loc(span.start);
    format!("Error at {}:{}: {}", line + 1, col + 1, msg)
}
```

### LSP Integration Pattern

```rust
fn byte_to_lsp_position(input: &[u8], offset: usize, encoding: PositionEncoding) -> Position {
    let line_info = LineInfo::from_bytes(input);
    let (line, byte_col) = line_info.loc(offset);
    
    match encoding {
        PositionEncoding::Utf8 => {
            Position { line: line as u32, character: byte_col as u32 }
        }
        PositionEncoding::Utf16 => {
            let line_start = line_info.line_starts[line];
            let line_text = &input[line_start..offset];
            let utf16_col = line_text.encode_utf16().count();
            Position { line: line as u32, character: utf16_col as u32 }
        }
    }
}
```

---

## Related Decisions

- [[ADR-013-utf8-internal-representation]] - UTF-8 validation at lexer boundary
- [[ADR-005-debug-information]] - Error reporting vs debug information distinction

## Related Research

- [[research/utf8-diagnostics-rendering]] - Full UTF-8 support, LSP encoding
- [[analysis/lexer-parser-location-tracking-review]] - Implementation review

---

## References

**Standard Patterns:**
- Logos documentation: `source = [u8]` for byte-level lexing
- LALRPOP documentation: `@L` and `@R` are byte offsets
- LSP 3.17: UTF-8 position encoding support

**Production Examples:**
- rust-analyzer: Byte offsets in syntax trees, lazy LineIndex
- GHC: Byte-based source locations, separate span tracking
- Lean 4: Byte positions in syntax, InfoTree for mapping
