# Location Information - Documentation Review

**Date:** 2026-05-05  
**Purpose:** Review of location information documentation vs implementation status

---

## Summary

**Documentation Quality: Historical** ℹ️
**Implementation Status: Different approach chosen** ✅
**Current Approach:** Byte-level spans only, no line:column in AST

---

## Updated Architecture Decision (2026-05-06)

**Decision:** Use byte-level spans only, no line:column tracking in AST.

### Rationale:
1. **Performance** - No O(N) line scanning during parsing
2. **Deterministic** - Byte offsets are stable and unambiguous
3. **LSP-compatible** - Convert to UTF-8/UTF-16 on demand
4. **Standard pattern** - Matches Logos + LALRPOP best practices
5. **Lazy conversion** - LineInfo only created when formatting diagnostics

### What This Means:
- ✅ Surface AST stores `Range<usize>` (byte offsets)
- ✅ Core IR has NO location fields (by design)
- ✅ `LineInfo` used lazily for diagnostic rendering
- ❌ No line:column fields in AST nodes
- ❌ No location tracking in core IR

---

## Current Implementation Status

### Implemented:
- ✅ `SourceFileId<'db>` - Salsa-interned file IDs
- ✅ `SourceInfo<'db>` - File vs Synthetic distinction
- ✅ `LineInfo` - Byte offset → (line, col) conversion (lazy)
- ✅ Surface syntax - Has byte range `loc: Range<usize>`
- ✅ Error types - Optional `SourceRange` spans (byte-based)
- ✅ UTF-8 validation at lexer boundary
- ✅ `Box<str>` for validated strings in AST

### Intentionally NOT Implemented:
- ❌ `Location<'db>` with line:column ranges - Using byte ranges instead
- ❌ Core IR location fields - Core IR is location-free by design
- ❌ Streaming line:column tracking - Using lazy conversion instead

---

## Error Reporting Strategy (Byte-Range Based)

Error messages reference surface AST byte ranges, converted lazily to line:column:

**Example:**
```rust
fn format_error(input: &[u8], span: Range<usize>, msg: &str) -> String {
    // Lazy LineInfo construction (only when displaying error)
    let line_info = LineInfo::from_bytes(input);
    let (line, col) = line_info.loc(span.start);
    format!("Error at {}:{}: {}", line + 1, col + 1, msg)
}
```

**For metavariable provenance:**
- Track surface AST node that created metavariable
- Store byte range of that node
- Convert to line:column when formatting diagnostic
- No need to store line:column in metavariable struct

---

## Historical Documentation

The following documents describe a **line:column tracking approach** that was considered
but ultimately **not adopted**:

- `design/to-ingest/location-information-design.md` - Historical
- `design/to-ingest/location-example-workflow.md` - Historical
- `wiki/implementation/location/` - Historical (describes different approach)

**Current approach:** Byte ranges only, lazy conversion. See:
- `wiki/analysis/lexer-parser-location-tracking-review.md` - Current architecture
- `wiki/decisions/ADR-013-utf8-internal-representation.md` - Current UTF-8 strategy

---

## Recommendation

**Do not implement** the line:column tracking described in historical docs.

**Current pattern is correct:**
- ✅ Store byte ranges in surface AST
- ✅ No locations in core IR
- ✅ Lazy LineInfo for diagnostics
- ✅ Simple, fast, standard pattern
