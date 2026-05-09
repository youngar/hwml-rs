# ADR-017: Position Caching in Diagnostic Spans

**Status:** Approved  
**Date:** 2026-05-08  
**Phase:** Diagnostic Framework (Week 1 revision)  
**Confidence:** 0.90  
**Deciders:** Architecture Team (after studying Asai source code)  
**Context Tags:** #diagnostics #performance #location-tracking #asai  
**Supersedes:** Initial Week 1 `Span` design (byte offsets only)  
**Reference:** `external/asai/src/Range.ml`, ADR-014

---

## Context

HWML diagnostics need to display source locations to users in **multiple formats**:

1. **Terminal output:** `file.hwml:42:10` (line:column)
2. **LSP protocol:** `Position { line: 41, character: 9 }` (0-indexed)
3. **Error messages:** "at line 42, column 10"
4. **CIRCT/MLIR:** 1-indexed line:column for hardware tools

Our current design (from ADR-014) uses byte offsets in AST nodes and converts to line:column **lazily** during diagnostic rendering.

### The Problem

With many diagnostics, we repeatedly convert the same byte offsets:

```rust
// Current approach (inefficient)
struct Span {
    start: usize,  // Byte offset
    end: usize,    // Byte offset
}

// Every time we render this diagnostic:
let line = line_info.line_number(span.start);  // O(log n) binary search
let col = line_info.column_number(span.start); // O(n) scan from line start
```

For a file with 100 errors, we do 200 binary searches + 200 line scans!

### Asai's Approach

Asai stores **both** byte offsets AND line information in every position:

```ocaml
type position = {
  source : source;
  offset : int;         (* Byte offset - fast, deterministic *)
  start_of_line : int;  (* Byte offset of line start *)
  line_num : int;       (* 1-indexed line number *)
}
```

This is computed **once** during parsing, then reused for all diagnostic rendering.

---

## Alternatives Considered

### Option 1: Byte Offsets Only (Current - Week 1)

Store only byte offsets, compute line:column on demand.

**Pros:**
- Minimal memory (2 × usize per span)
- Simple during parsing (LALRPOP gives byte offsets)
- Deterministic (same bytes = same offsets)

**Cons:**
- ❌ Repeated computation for diagnostics
- ❌ O(log n) binary search per position
- ❌ O(n) line scan for column calculation
- ❌ Need `LineInfo` context for every conversion

**Verdict:** **Works but inefficient** for diagnostic-heavy workloads

### Option 2: Line:Column Only (Rejected)

Store only line:column positions, no byte offsets.

**Pros:**
- Direct display format
- No conversion needed

**Cons:**
- ❌ Hard to compute during parsing (need line tracking)
- ❌ Can't extract source text ranges (need bytes for slicing)
- ❌ LSP needs UTF-16 offsets (different from line:column)
- ❌ Loses the benefits of byte-level precision

**Verdict:** **Rejected** - Loses critical byte offset information

### Option 3: Position with Cached Line Info (Chosen - Asai Approach)

Store byte offset, line start offset, and line number together.

**Pros:**
- ✅ Fast rendering: line number is cached (no search)
- ✅ Fast column: `offset - start_of_line` (constant time)
- ✅ Can still extract byte ranges for source text
- ✅ Single computation during parsing
- ✅ Proven approach (Asai uses this)

**Cons:**
- Larger memory (4 × usize per span instead of 2)
- Slightly more complex during parsing

**Verdict:** **Best balance** - Small memory cost, large performance gain

### Option 4: Separate Position Cache (Rejected)

Keep byte offsets in AST, maintain separate cache of positions.

**Pros:**
- AST stays small
- Cache can be optimized independently

**Cons:**
- ❌ Complex cache invalidation
- ❌ Requires lookups (HashMap overhead)
- ❌ Not obviously better than Option 3

**Verdict:** **Rejected** - Complexity not worth it

---

## Decision

**Use Asai-style `Position` struct that caches line information alongside byte offset.**

### Type Design

```rust
/// A position in source code with cached line information
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Position {
    /// Byte offset from start of file (0-indexed)
    pub offset: usize,
    
    /// Byte offset of the start of this line (0-indexed)
    pub start_of_line: usize,
    
    /// Line number (1-indexed, matching LSP and user expectations)
    pub line_num: usize,
}

impl Position {
    /// Column number (0-indexed) within the line
    pub fn column(&self) -> usize {
        self.offset - self.start_of_line
    }
    
    /// Create position with line info from LineInfo helper
    pub fn from_offset(line_info: &LineInfo, offset: usize) -> Self {
        let line_num = line_info.line_number(offset);
        let start_of_line = line_info.line_start_offset(line_num);
        Self { offset, start_of_line, line_num }
    }
}

/// A span is two positions
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: Position,
    pub end: Position,
}
```

### Migration from Current Design

**Current (Week 1):**
```rust
pub struct Span {
    pub start: usize,
    pub end: usize,
}
```

**Revised (incorporates Position caching):**
```rust
pub struct Span {
    pub start: Position,
    pub end: Position,
}
```

**Migration path:**
1. Update parsing to compute `Position` from byte offsets
2. Update diagnostic builder API to accept `Position`
3. Rendering becomes trivial: `pos.line_num`, `pos.column()`

---

## Rationale

### Performance Analysis

**Without caching (current):**
```
For each diagnostic display:
- Binary search for line number: O(log n)
- Scan from line start for column: O(m) where m = line length
- Total for 100 diagnostics: ~100 × (log n + m)
```

**With caching (revised):**
```
During parsing (once):
- Compute Position for each AST node: O(1) amortized
During diagnostic display:
- Read cached line_num: O(1)
- Compute column: offset - start_of_line: O(1)
- Total for 100 diagnostics: ~100 × 1 = O(100)
```

**Speedup:** ~10-100x for diagnostic-heavy files

### Memory Analysis

**Per AST node:**
- Current: 16 bytes (2 × usize on 64-bit)
- Revised: 48 bytes (6 × usize = 3 fields × 2 positions)
- Increase: 32 bytes per node

**For typical file (1000 AST nodes):**
- Current: ~16 KB
- Revised: ~48 KB
- Increase: ~32 KB

**Trade-off:** 32 KB extra memory for 10-100x diagnostic rendering speedup.

**Verdict:** Absolutely worth it! Modern machines have GB of RAM, and diagnostics are critical path for developer experience.

---

## Consequences

### Positive

✅ **Fast diagnostic rendering** - No repeated line:column computation
✅ **Simple rendering code** - `pos.line_num`, `pos.column()` just read fields
✅ **LSP friendly** - Direct access to line numbers for LSP protocol
✅ **CIRCT friendly** - 1-indexed line numbers for hardware tools
✅ **Proven approach** - Asai validates this works in practice

### Negative

⚠️ **Larger AST** - 3x memory per span (acceptable for benefits)
⚠️ **Parsing complexity** - Need to compute Position from offsets (one-time cost)

### Neutral

- Still compatible with byte-level slicing (offset field preserved)
- Can still use `Range<usize>` internally during parsing, convert to Position afterward

---

## Implementation Notes

### During Parsing (LALRPOP)

```rust
// LALRPOP gives us byte offsets
pub Expr: surface::Expr = {
    <start:@L> <name:Ident> <end:@R> => {
        // Convert to Position with line info
        let start_pos = Position::from_offset(line_info, start);
        let end_pos = Position::from_offset(line_info, end);
        surface::Expr {
            kind: surface::ExprKind::Var(name),
            span: Span { start: start_pos, end: end_pos },
        }
    }
}
```

### LineInfo Helper

```rust
pub struct LineInfo {
    line_starts: Vec<usize>,  // Byte offsets of line starts
}

impl LineInfo {
    pub fn from_source(source: &str) -> Self {
        let mut line_starts = vec![0];
        for (i, byte) in source.bytes().enumerate() {
            if byte == b'\n' {
                line_starts.push(i + 1);
            }
        }
        Self { line_starts }
    }

    pub fn line_number(&self, offset: usize) -> usize {
        match self.line_starts.binary_search(&offset) {
            Ok(line) => line + 1,
            Err(line) => line,
        }
    }

    pub fn line_start_offset(&self, line: usize) -> usize {
        self.line_starts[line - 1]
    }
}
```

---

## Related Decisions

- **ADR-014:** Byte-Level Location Tracking - Foundation for this decision
- **ADR-016:** No Column Alignment - Why we need fast line:column access
- **ADR-013:** UTF-8 Internal Representation - Byte offsets are UTF-8 code units

---

## References

- **Asai Source:** `external/asai/src/Range.ml` - Position type with caching
- **Performance Analysis:** See `design/DIAGNOSTIC-IMPLEMENTATION-PLAN-REVISED.md`

---

## Migration Plan

**Week 1 (In Progress):**
1. ✅ Basic Span with byte offsets (completed)
2. 🔄 Revise to Position-based Span (this ADR)
3. Update builder API
4. Update tests

**Backward Compatibility:**
- Provide helper: `Span::from_offsets(start: usize, end: usize, line_info: &LineInfo)`
- Existing code can be migrated incrementally

---

**Status:** Approved for implementation in Week 1 revision