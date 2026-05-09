# Location Information Design - Executive Summary

## Decision: Use Full Source Ranges (Line:Column Ranges, Not Byte Offsets)

After researching Rust, Scala, and MLIR/CIRCT, I recommend **storing Line:Column RANGES throughout HWML** instead of byte offsets or single points.

## Why Full Source Ranges?

### ✅ Reasons FOR Ranges (Not Points)
1. **You control the parser** - Already have start/end byte offsets from parsing
2. **MLIR native support** - `FileLineColRange` is a first-class MLIR type
3. **Better diagnostics** - Can highlight exact spans in error messages (e.g., underline entire identifier)
4. **LSP requires ranges** - Language Server Protocol uses ranges, not points
5. **No overhead** - Salsa interning makes storing 4 numbers nearly free
6. **Future-proof** - Won't need to migrate from points to ranges later

### ✅ Reasons FOR Line:Column (Not Byte Offsets)
1. **CIRCT native format** - MLIR expects `FileLineColRange("file.hwml":1:5 to 1:10)` format
2. **No conversion overhead** - Direct use in CIRCT backend
3. **Human-readable** - Easier debugging and error messages
4. **Better for incremental compilation** - More stable than byte offsets

### ❌ Reasons AGAINST Byte Offsets
1. Must convert to line:column for CIRCT (expensive operation)
2. Requires storing file text for conversion (memory overhead)
3. Two representations needed (internal byte, external line:column)
4. Less stable across file edits

## Core Design

### New Types (in `hwml-core/src/source_range.rs`)

```rust
/// Interned location - Copy-able and cheap
#[salsa::interned]
pub struct Location {
    pub data: LocationData<'db>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum LocationData<'db> {
    /// Real source range: File:StartLine:StartCol to EndLine:EndCol (1-based)
    /// Maps directly to MLIR FileLineColRange
    FileLineColRange {
        file: SourceFileId<'db>,
        start_line: u32,
        start_column: u32,
        end_line: u32,
        end_column: u32,
    },
    /// Compiler-generated location with optional label
    Synthetic {
        label: Word<'db>,
    },
}
```

### Key Properties

1. **Salsa-interned**: 1000 identical locations = 1 stored instance
2. **Copy-able**: `Location<'db>` is just 8 bytes (pointer-sized ID)
3. **Full ranges**: Start AND end positions for better error highlighting
4. **1-based**: Line 1, Column 1 = first character (MLIR convention)
5. **Workspace-aware**: `SourceFileId` includes library name

## Integration Points

### Parser (hwml-surface)
- Compute line:column during parsing using existing `LineInfo`
- Store `Location` instead of `Range<usize>` in surface syntax

### Core IR (hwml-core)
- Every `Syntax` node carries a `Location`
- Replace current `SourceRange` with `Location`

### Elaborator (hwml-elab)
- Thread `SourceFileId` through elaboration
- Preserve locations from surface to core

### CIRCT Backend (hwml-circt)
- Direct conversion: `LocationData::FileLineCol` → MLIR `FileLineColLoc`
- Synthetic becomes MLIR `UnknownLoc` or `NameLoc`

### Workspace (hwml-workspace)
- Create `SourceFileId` for each file in library
- Thread through compilation pipeline
- Enable cross-library error reporting

## Example Usage

```rust
// Create a real source range
let lib = Word::new(db, "my-hardware");
let path = Word::new(db, "/path/to/adder.hwml");
let file = SourceFileId::new(db, lib, path);

// Range from "xor a b" spanning columns 16-21 on line 2
let loc = Location::new(db, LocationData::FileLineColRange {
    file,
    start_line: 2,
    start_column: 16,
    end_line: 2,
    end_column: 21,
});

// Display: "/path/to/adder.hwml:2:16 to 2:21"
println!("{}", loc.display(db));

// Convert to MLIR location for CIRCT
let mlir_loc = circt_ctx.to_mlir_location(db, loc);
// Produces: loc("adder.hwml":2:16 to 2:21)  <-- Full range!

// Create synthetic location
let label = Word::new(db, "desugared");
let synth = Location::new(db, LocationData::Synthetic { label });
// Display: "<desugared>"
```

## Benefits

### 1. Performance
- Interning: Massive deduplication of identical locations
- Copy-able: Pass by value, no allocations
- No conversion: Direct use in CIRCT

### 2. Correctness
- Type-safe: Can't confuse byte offsets with line numbers
- Workspace-aware: Library name embedded in file ID
- Stable: Line:column more stable than byte offsets

### 3. Developer Experience
- Readable errors: "adder.hwml:42:10: type mismatch"
- IDE integration: Direct LSP compatibility
- Debuggable: Locations visible in printed IR

## Migration Plan

### Phase 1: Add New Types (1-2 days)
Add `Location` alongside existing `SourceRange`, enable coexistence

### Phase 2: Update Parser (2-3 days)
Surface syntax uses `Location`, compute line:column during parsing

### Phase 3: Update Core IR (3-4 days)
Replace `SourceRange` with `Location` in all syntax nodes

### Phase 4: CIRCT Backend (1-2 days)
Convert `Location` to MLIR `FileLineColLoc`

### Phase 5: Workspace Integration (2-3 days)
Thread `SourceFileId` through multi-library compilation

### Phase 6: Cleanup & Testing (2-3 days)
Remove old code, comprehensive testing

**Total: 11-17 days (2-3.5 weeks)**

## Comparison with Other Systems

| System | Internal Format | Display Format | Interning | Notes |
|--------|----------------|----------------|-----------|-------|
| **Rust** | Byte offsets | Line:Column (lazy) | Aggressive | 4-byte packed spans |
| **Scala** | Mixed (offset + ranges) | Line:Column | Per-source | Flexible Position trait |
| **MLIR** | Line:Column | Line:Column | Global | Multiple location types |
| **HWML (proposed)** | **Line:Column** | **Line:Column** | **Salsa** | **Direct CIRCT compat** |

## Open Questions (For Future)

1. **Ranges**: Should we store end location too? (Start with points, add ranges later if needed)
2. **Macros**: Track expansion chains? (Add `CallSiteLoc`-style later)
3. **Provenance**: Richer synthetic tracking? (Keep simple for now)

## Full Design Document

See [`design/location-information-design.md`](design/location-information-design.md) for:
- Detailed API specifications
- Parser integration examples
- CIRCT backend implementation
- Serialization format for `.hwmli` files
- Comprehensive testing strategy
- Complete implementation checklist

## Recommendation

**Proceed with Line:Column design**. It's the right choice for HWML because:
1. Aligns with CIRCT expectations (primary backend)
2. Salsa provides interning we need
3. Simpler than byte offsets + conversion
4. Better workspace integration
5. More readable and debuggable

The migration can be done incrementally without breaking existing code.
