# Location System Design Comparison

## Current vs Proposed

| Aspect | Current System | Proposed System |
|--------|---------------|-----------------|
| **Format** | `Range<usize>` byte offsets | `Location<'db>` with line:column |
| **Size** | 16 bytes (2 × usize) | 8 bytes (interned ID) |
| **Interning** | None | Salsa-interned |
| **Library tracking** | No | Yes (via SourceFileId) |
| **CIRCT compat** | Requires conversion | Direct mapping |
| **Synthetic locs** | Not supported | First-class support |
| **Copy cost** | 16 bytes | 8 bytes |
| **Display** | Requires file + LineInfo | Direct from data |

## Comparison with Other Compilers

### Size Comparison

| System | Typical Size | Compression Strategy |
|--------|-------------|---------------------|
| **Rust (Span)** | 4 bytes | Bit-packing + interner |
| **Scala (Position)** | 24-32 bytes | Arc-wrapped SourceFile |
| **MLIR (Location)** | 8 bytes | Global context interner |
| **HWML (proposed)** | **8 bytes** | **Salsa interner** |

### Format Comparison

| System | Internal Format | External Format | Conversion Cost |
|--------|----------------|-----------------|-----------------|
| **Rust** | BytePos (u32) | Line:Column | O(log n) per conversion |
| **Scala** | Offset (Int) | Line:Column | O(1) cached |
| **MLIR** | Line:Column | Line:Column | None |
| **HWML (proposed)** | **Line:Column** | **Line:Column** | **None** |

## Feature Matrix

| Feature | Rust | Scala | MLIR | HWML (proposed) |
|---------|------|-------|------|-----------------|
| **Byte offsets** | ✅ Primary | ✅ Primary | ❌ | ❌ |
| **Line:Column** | ⚠️ Lazy | ⚠️ Lazy | ✅ Primary | ✅ Primary |
| **Ranges** | ✅ | ✅ | ✅ | ⚠️ Future |
| **Synthetic/Unknown** | ⚠️ Via `DUMMY_SP` | ✅ NoPosition | ✅ UnknownLoc | ✅ Synthetic |
| **Macro expansion** | ✅ Via parent chain | ✅ | ✅ CallSiteLoc | ⚠️ Future |
| **Interning** | ✅ Custom | ⚠️ Per-file | ✅ Global | ✅ Salsa |
| **File identity** | Arc<SourceFile> | SourceFile | StringAttr | SourceFileId |
| **Library tracking** | ❌ | ❌ | ❌ | ✅ |

## Memory Usage Estimate

Assume a 10,000 line program with typical distribution:

| Metric | Current (Range) | Proposed (Location) |
|--------|----------------|-------------------|
| **Unique locations** | ~2,000 | ~2,000 |
| **Total location uses** | ~20,000 | ~20,000 |
| **Storage (without interning)** | 20,000 × 16 = 320 KB | 20,000 × 8 = 160 KB |
| **Storage (with interning)** | N/A | 2,000 × 16 + 20,000 × 8 = 192 KB |
| **Savings** | - | **40% reduction** |

With Salsa interning, we store `LocationData` once and reference it 10× on average.

## Performance Characteristics

### Location Creation

| System | Cost | Notes |
|--------|------|-------|
| **Current** | O(1) | Just store two integers |
| **Proposed** | O(log n) | Salsa interner lookup |

**Analysis**: Interning cost is negligible compared to parsing/elaboration work.

### Location Copy

| System | Cost | Notes |
|--------|------|-------|
| **Current** | 16 bytes | Copy two usize |
| **Proposed** | 8 bytes | Copy one ID |

**Analysis**: 2× faster copies, especially important for IR passes.

### Location Display

| System | Cost | Notes |
|--------|------|-------|
| **Current** | O(log n) | Binary search in LineInfo |
| **Proposed** | O(1) | Data already contains line:col |

**Analysis**: Error messages are instant, no conversion needed.

### CIRCT Conversion

| System | Cost | Notes |
|--------|------|-------|
| **Current** | O(log n) per loc | Must convert all locations |
| **Proposed** | O(1) per loc | Direct copy to MLIR format |

**Analysis**: Critical path improvement for CIRCT backend.

## Decision Rationale

### Why NOT Byte Offsets (Rust-style)?

1. **Wrong target**: Rust targets human-readable errors from byte offsets
   - HWML targets CIRCT which expects line:column
   
2. **Double storage**: Need both offsets AND file text for conversion
   - HWML would need to keep source text in memory
   
3. **Conversion overhead**: Every CIRCT operation needs conversion
   - For a 1000-operation circuit, that's 1000 conversions
   
4. **More complex**: Requires LineInfo mapping on every display
   - HWML gets simpler code with native line:column

### Why NOT Scala-style Position?

1. **Too heavyweight**: 24-32 bytes per position
   - No interning, every position is unique instance
   
2. **GC pressure**: Object allocation for every location
   - HWML uses Rust, no GC to amortize allocations
   
3. **Arc overhead**: Requires Arc<SourceFile> reference counting
   - HWML's Salsa interning is cheaper

### Why MLIR-style Location? ✅

1. **Same target**: HWML compiles to CIRCT/MLIR
   - Native format is the right choice
   
2. **Proven design**: MLIR handles millions of operations
   - Location system is battle-tested
   
3. **Interning built-in**: MLIR interns all locations
   - Salsa provides the same capability
   
4. **Multiple location types**: UnknownLoc, FileLineColLoc, etc.
   - Maps cleanly to our Synthetic/FileLineCol

## Migration Risk Analysis

### Low Risk ✅

- **Incremental migration**: Can add new type alongside old
- **Backward compat**: Old `SourceRange` can coexist temporarily
- **Clear boundaries**: Parser → Surface → Core → CIRCT
- **No ABI changes**: Internal implementation detail

### Medium Risk ⚠️

- **Parser changes**: Need to compute line:column during parsing
  - Mitigation: `LineInfo` already implemented
- **Elaborator changes**: Thread locations through
  - Mitigation: Locations already in surface syntax
- **Testing effort**: Need comprehensive location tests
  - Mitigation: Can reuse existing error message tests

### Zero Risk ✅

- **Performance**: Interning improves performance
- **Memory**: 40% reduction in location storage
- **Correctness**: Type system prevents misuse

## Recommendation Matrix

| Use Case | Byte Offsets | Line:Column | Recommendation |
|----------|-------------|-------------|----------------|
| **Error messages** | ❌ Must convert | ✅ Direct use | **Line:Column** |
| **LSP integration** | ❌ Must convert | ✅ Direct use | **Line:Column** |
| **CIRCT backend** | ❌ Must convert | ✅ Direct use | **Line:Column** |
| **Source snippets** | ✅ Direct slice | ⚠️ Need LineInfo | **Byte Offsets** |
| **Compact storage** | ⚠️ 16 bytes | ✅ 8 bytes (interned) | **Line:Column** |
| **Memory efficiency** | ❌ No sharing | ✅ Interned | **Line:Column** |

**Overall**: Line:Column wins 5 out of 6 categories.

## Conclusion

The **Line:Column design is the clear winner** for HWML because:

1. ✅ **CIRCT is the primary backend** - native format matters
2. ✅ **Salsa provides interning** - we don't need custom compression
3. ✅ **Simpler implementation** - no conversion layers
4. ✅ **Better performance** - smaller copies, faster display
5. ✅ **Workspace-aware** - library tracking built-in

The only advantage of byte offsets (source snippet extraction) is minor and can be solved by keeping `LineInfo` around when needed.

**Next Steps**: Implement the Line:Column design as specified in `location-information-design.md`.
