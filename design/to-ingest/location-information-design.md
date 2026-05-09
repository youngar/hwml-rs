# HWML Location Information Design

## Executive Summary

This document specifies a unified location tracking system for HWML that:
1. **Stores Line:Column natively** (not byte offsets) to match CIRCT/MLIR expectations
2. **Uses aggressive interning** to compress location data (inspired by rustc)
3. **Supports synthetic locations** for compiler-generated code
4. **Preserves locations through Core IR** for CIRCT backend consumption
5. **Integrates with workspace system** for multi-library error reporting

## Research: How Other Systems Handle Locations

### Rust Compiler (rustc)

**Key Insights:**
- Uses **byte positions** internally (`Span` with `lo: BytePos`, `hi: BytePos`)
- **Lazy conversion** to line:column only for display/diagnostics
- **Extremely compact**: `Span` is 4 bytes (compressed using bit packing)
- **Interning**: `SourceFile` is `Arc`-wrapped and shared
- **Stable hashing**: Hashes `(filename, line, col)` for incremental compilation
- Supports **macro expansion tracking** via span chains

**Span Structure:**
```rust
pub struct Span {
    lo_or_index: u32,       // byte offset or index into span interner
    len_with_tag_or_marker: u16,  // length + tag bits
    ctxt_or_parent_or_marker: u16, // syntax context or parent span
}
```

**SourceMap:** Global structure mapping byte positions → `SourceFile` → line/col

### Scala Compiler

**Key Insights:**
- Uses **`Position` trait** with multiple implementations:
  - `NoPosition` - for synthetic/unknown
  - `OffsetPosition(source, point)` - single point
  - `RangePosition(source, start, point, end)` - full range
- **Point-based model**: Every range has a "point" (primary location for errors)
- **SourceFile integration**: Positions hold reference to source
- **Macro support**: Tracks expansion site via `Position.ofMacroExpansion`

### MLIR/CIRCT

**Key Insights:**
- **FileLineColLoc** is the primary location type: `"filename":line:column`
- **Multiple location kinds**:
  - `UnknownLoc` - for synthetic/unknown
  - `FileLineColLoc` - standard file:line:col
  - `NameLoc` - attaches a name to another location
  - `CallSiteLoc` - tracks call chains (callee `at` caller)
  - `FusedLoc` - combines multiple locations
- **Interned by MLIR context** - locations are value types
- **Direct consumption**: CIRCT expects `FileLineColLoc` format for diagnostics

**MLIR Format:**
```mlir
loc("my_file.hwml":42:10)          // FileLineColLoc
loc(unknown)                        // UnknownLoc  
loc("generated"("my_file.hwml":42:10))  // NameLoc wrapping FileLineColLoc
```

## Design Decision: Line:Column vs Byte Offsets

### Why Line:Column (Chosen Approach)

**Pros:**
1. ✅ **CIRCT native format** - no conversion needed at backend
2. ✅ **Human-readable** - directly usable in diagnostics
3. ✅ **LSP-compatible** - Language Server Protocol uses line:column
4. ✅ **Stable across edits** - line:column more stable than byte offsets for incremental compilation
5. ✅ **Simpler serialization** - `.hwmli` files can store line:column directly

**Cons:**
1. ❌ Requires line info computation during parsing (already available)
2. ❌ Slightly larger than byte offsets (4 bytes vs 8 bytes per location)

### Why NOT Byte Offsets

**Pros:**
1. ✅ Compact (4 bytes for start + length)
2. ✅ Easy to extract source snippets

**Cons:**
1. ❌ **Must convert to line:column for CIRCT** - expensive operation
2. ❌ **Requires storing file text** for conversion (increases memory)
3. ❌ **Not stable** - byte offsets change when file is edited
4. ❌ **Two representations** - byte internally, line:column externally

**Decision**: Use Line:Column natively throughout the system.

## Architecture

### Core Types (in `hwml-core/src/source_range.rs`)

```rust
/// A location in source code: File:Line:Column Range or Synthetic.
/// This is the primary location type used throughout HWML.
#[salsa::interned]
pub struct Location {
    pub data: LocationData<'db>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum LocationData<'db> {
    /// A real source range with file, start line:col, and end line:col (1-based).
    /// Maps directly to MLIR's FileLineColRange.
    FileLineColRange {
        file: SourceFileId<'db>,
        start_line: u32,
        start_column: u32,
        end_line: u32,
        end_column: u32,
    },
    /// Synthetic/compiler-generated location with an optional label.
    Synthetic {
        label: Word<'db>,
    },
}

/// Identifies a single source file within a library.
/// This is already implemented and works well.
#[salsa::interned]
pub struct SourceFileId {
    pub library_name: Word<'db>,
    pub canonical_path: Word<'db>,
}
```

### Key Design Properties

1. **Salsa Interning**: `Location` is interned, so identical locations share the same ID
   - Massively reduces memory: 1000 identical locations = 1 stored `LocationData`
   - Copy-able: `Location<'db>` is just a pointer-sized ID
   - Fast equality: pointer comparison

2. **Full Source Ranges**: Store start AND end positions
   - **Better diagnostics**: Can highlight exact span in error messages
   - **MLIR native**: Maps directly to `FileLineColRange`
   - **Parser-friendly**: You already have start/end from parsing
   - **Richer errors**: Show multi-line spans, not just points

3. **Line and Column are 1-based**: Matches MLIR/CIRCT convention
   - Line 1, Column 1 = first character
   - Easy conversion to 0-based LSP format: `lsp_line = line - 1`

4. **No Byte Offsets**: Eliminates conversion overhead to CIRCT
   - Parser computes line:column during parsing (using `LineInfo`)
   - No need to store file text for location conversion

5. **Synthetic Locations**: First-class support for compiler-generated code
   - Labels like `"desugared"`, `"metavar-?42"`, `"quotation"`
   - MLIR `UnknownLoc` or `NameLoc` depending on label

### Integration with hwml-workspace

```rust
// In workspace compilation loop:
for lib_name in workspace.topo_order {
    let lib = &workspace.libraries[lib_name];

    for source_file_path in &lib.source_files {
        // Create SourceFileId for this file
        let library_name = Word::new(db, &lib.name);
        let canonical_path = Word::new(db, source_file_path.to_str().unwrap());
        let file_id = SourceFileId::new(db, library_name, canonical_path);

        // Parse file and get surface program with locations
        let text = std::fs::read_to_string(source_file_path)?;
        let line_info = LineInfo::from_bytes(text.as_bytes());
        let program = parse_with_locations(db, file_id, &text, &line_info)?;

        // Elaborate with locations threaded through
        elab_program(db, &mut global_env, &program)?;
    }
}
```

## Implementation: Parser Integration

### Current State (Byte Offsets in Surface)

The parser currently tracks byte offsets in `Range<usize>`:

```rust
// In hwml-surface/src/syntax.rs
pub struct Def {
    pub loc: Range<usize>,  // byte offsets
    pub id: Id,
    // ...
}
```

### New Approach: Compute Line:Column During Parsing

```rust
// Add to parser state
struct ParserState<'db> {
    db: &'db dyn salsa::Database,
    file_id: SourceFileId<'db>,
    line_info: &'db LineInfo,
}

impl ParserState<'_> {
    /// Convert byte range to Location
    fn location_from_range(&self, start: usize, end: usize) -> Location<'db> {
        let (start_line, start_col) = self.line_info.loc(start);
        let (end_line, end_col) = self.line_info.loc(end);

        Location::new(self.db, LocationData::FileLineColRange {
            file: self.file_id,
            start_line: (start_line + 1) as u32,    // Convert 0-based to 1-based
            start_column: (start_col + 1) as u32,
            end_line: (end_line + 1) as u32,
            end_column: (end_col + 1) as u32,
        })
    }

    /// Create a synthetic location
    fn synthetic(&self, label: &str) -> Location<'db> {
        let word = Word::new(self.db, label);
        Location::new(self.db, LocationData::Synthetic { label: word })
    }
}
```

## Implementation: Core IR Changes

### Replace SourceRange with Location

**Current:**
```rust
pub struct SourceRange<'db> {
    pub source: Source<'db>,
    pub range: Range<usize>,  // byte offsets
}
```

**New:**
```rust
// SourceRange becomes just an alias
pub type SourceRange<'db> = Location<'db>;

// All syntax nodes carry a Location
impl<'db> Syntax<'db> {
    pub fn location(&self) -> Location<'db> {
        // Every syntax variant stores a Location
    }
}
```

### Update HasSourceRange Trait

```rust
pub trait HasSourceRange<'db> {
    fn location(&self) -> Location<'db>;
}

impl<'db> HasSourceRange<'db> for RcSyntax<'db> {
    fn location(&self) -> Location<'db> {
        self.as_ref().location()
    }
}
```

## Implementation: CIRCT Backend Integration

### Convert Location to MLIR MlirLocation

```rust
// In hwml-circt/src/context.rs
impl CirctContext {
    /// Convert HWML Location to MLIR location
    pub fn to_mlir_location<'db>(
        &self,
        db: &'db dyn salsa::Database,
        loc: Location<'db>,
    ) -> MlirLocationWrapper {
        match loc.data(db) {
            LocationData::FileLineColRange {
                file,
                start_line,
                start_column,
                end_line,
                end_column,
            } => {
                // Get the file path
                let path = file.canonical_path(db).text(db);

                // Create MLIR FileLineColRange (full range support!)
                unsafe {
                    let filename_str = mlirStringRefCreateFromCString(
                        path.as_ptr() as *const i8
                    );

                    // Use mlirLocationFileLineColRangeGet for full range
                    let raw_loc = mlirLocationFileLineColRangeGet(
                        self.context.as_raw(),
                        filename_str,
                        *start_line,
                        *start_column,
                        *end_line,
                        *end_column,
                    );
                    MlirLocationWrapper::from_raw(raw_loc)
                }
            }
            LocationData::Synthetic { label } => {
                // For synthetic, use UnknownLoc or NameLoc
                let unknown = MlirLocationWrapper::unknown(&self.context);

                if !label.text(db).is_empty() {
                    // Wrap with NameLoc for labeled synthetic locations
                    unsafe {
                        let name_attr = mlirStringAttrGet(
                            self.context.as_raw(),
                            mlirStringRefCreateFromCString(
                                label.text(db).as_ptr() as *const i8
                            ),
                        );
                        let raw_loc = mlirLocationNameGet(
                            self.context.as_raw(),
                            name_attr,
                            unknown.as_raw(),
                        );
                        MlirLocationWrapper::from_raw(raw_loc)
                    }
                } else {
                    unknown
                }
            }
        }
    }
}
```

## Implementation: Display and Diagnostics

### Format Locations for Error Messages

```rust
impl<'db> Location<'db> {
    /// Format location in MLIR style: "file.hwml:1:5 to 1:10"
    pub fn display<Db>(&self, db: &'db Db) -> String
    where
        Db: salsa::Database,
    {
        match self.data(db) {
            LocationData::FileLineColRange {
                file,
                start_line,
                start_column,
                end_line,
                end_column,
            } => {
                let path = file.canonical_path(db).text(db);
                if start_line == end_line {
                    // Same line: "file.hwml:1:5 to 1:10"
                    format!("{}:{}:{} to {}:{}",
                        path, start_line, start_column, end_line, end_column)
                } else {
                    // Multi-line: "file.hwml:1:5 to 3:10"
                    format!("{}:{}:{} to {}:{}",
                        path, start_line, start_column, end_line, end_column)
                }
            }
            LocationData::Synthetic { label } => {
                let text = label.text(db);
                if text.is_empty() {
                    "unknown".to_string()
                } else {
                    format!("<{}>", text)
                }
            }
        }
    }

    /// Get just the filename (for compact display)
    pub fn filename<Db>(&self, db: &'db Db) -> Option<&'db str>
    where
        Db: salsa::Database,
    {
        match self.data(db) {
            LocationData::FileLineColRange { file, .. } => {
                let path = file.canonical_path(db).text(db);
                std::path::Path::new(path)
                    .file_name()
                    .and_then(|s| s.to_str())
            }
            _ => None,
        }
    }

    /// Convert to LSP Range (0-based line and column)
    pub fn to_lsp_range<Db>(&self, db: &'db Db)
        -> Option<((u32, u32), (u32, u32))>
    where
        Db: salsa::Database,
    {
        match self.data(db) {
            LocationData::FileLineColRange {
                start_line,
                start_column,
                end_line,
                end_column,
                ..
            } => {
                // Convert 1-based to 0-based for LSP
                Some((
                    (start_line - 1, start_column - 1),
                    (end_line - 1, end_column - 1),
                ))
            }
            _ => None,
        }
    }
}
```

## Implementation: Serialization for .hwmli

### Stable Representation

When serializing locations to `.hwmli` files, we need a stable format:

```rust
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub enum SerializedLocation {
    FileLineCol {
        library_name: String,
        file_path: String,  // Relative to library root for portability
        line: u32,
        column: u32,
    },
    Synthetic {
        label: String,
    },
}

impl<'db> Location<'db> {
    /// Serialize location for .hwmli format
    pub fn serialize<Db>(&self, db: &'db Db) -> SerializedLocation
    where
        Db: salsa::Database,
    {
        match self.data(db) {
            LocationData::FileLineCol { file, line, column } => {
                SerializedLocation::FileLineCol {
                    library_name: file.library_name(db).text(db).to_string(),
                    file_path: file.canonical_path(db).text(db).to_string(),
                    line: *line,
                    column: *column,
                }
            }
            LocationData::Synthetic { label } => {
                SerializedLocation::Synthetic {
                    label: label.text(db).to_string(),
                }
            }
        }
    }

    /// Deserialize location from .hwmli format
    pub fn deserialize<Db>(
        db: &'db Db,
        serialized: &SerializedLocation,
    ) -> Location<'db>
    where
        Db: salsa::Database,
    {
        match serialized {
            SerializedLocation::FileLineCol {
                library_name,
                file_path,
                line,
                column,
            } => {
                let lib_word = Word::new(db, library_name.as_str());
                let path_word = Word::new(db, file_path.as_str());
                let file_id = SourceFileId::new(db, lib_word, path_word);

                Location::new(db, LocationData::FileLineCol {
                    file: file_id,
                    line: *line,
                    column: *column,
                })
            }
            SerializedLocation::Synthetic { label } => {
                let word = Word::new(db, label.as_str());
                Location::new(db, LocationData::Synthetic { label: word })
            }
        }
    }
}
```

## Migration Path

### Phase 1: Add New Location Type (Non-Breaking)

1. Add `Location` and `LocationData` to `hwml-core/src/source_range.rs`
2. Keep existing `SourceRange` type for now
3. Add conversion functions between old and new

### Phase 2: Update Parser

1. Update surface syntax to use `Location` instead of `Range<usize>`
2. Compute line:column during parsing using `LineInfo`
3. Thread `SourceFileId` through parser

### Phase 3: Update Core IR

1. Replace `SourceRange` with `Location` in `Syntax` nodes
2. Update all elaboration code to preserve locations
3. Update CIRCT backend to use new location format

### Phase 4: Cleanup

1. Remove old `SourceRange` type
2. Update all documentation
3. Add comprehensive tests

## Testing Strategy

### Unit Tests

```rust
#[test]
fn test_location_display() {
    let db = Database::new();
    let lib = Word::new(&db, "my-lib");
    let path = Word::new(&db, "/path/to/file.hwml");
    let file_id = SourceFileId::new(&db, lib, path);

    let loc = Location::new(&db, LocationData::FileLineCol {
        file: file_id,
        line: 42,
        column: 10,
    });

    assert_eq!(loc.display(&db), "/path/to/file.hwml:42:10");
}

#[test]
fn test_synthetic_location() {
    let db = Database::new();
    let label = Word::new(&db, "desugared");
    let loc = Location::new(&db, LocationData::Synthetic { label });

    assert_eq!(loc.display(&db), "<desugared>");
}

#[test]
fn test_location_interning() {
    let db = Database::new();
    let lib = Word::new(&db, "my-lib");
    let path = Word::new(&db, "/path/to/file.hwml");
    let file_id = SourceFileId::new(&db, lib, path);

    let loc1 = Location::new(&db, LocationData::FileLineCol {
        file: file_id,
        line: 42,
        column: 10,
    });

    let loc2 = Location::new(&db, LocationData::FileLineCol {
        file: file_id,
        line: 42,
        column: 10,
    });

    // Interning means they should be the same ID
    assert_eq!(loc1, loc2);
}
```

### Integration Tests

1. **Parser test**: Parse a multi-line file and verify locations
2. **Workspace test**: Compile multi-library project and verify cross-library locations
3. **CIRCT test**: Generate MLIR with locations and verify format
4. **Serialization test**: Round-trip through `.hwmli` format

## Benefits of This Design

### 1. Performance
- **Interned locations**: 1000 identical locations = 1 stored instance
- **Copy-able**: `Location<'db>` is pointer-sized (8 bytes on 64-bit)
- **No conversion overhead**: Line:column is native format

### 2. CIRCT Integration
- **Direct mapping**: `LocationData::FileLineCol` → MLIR `FileLineColLoc`
- **No translation**: CIRCT backend receives locations in expected format
- **Rich diagnostics**: CIRCT can show exact source locations in errors

### 3. Workspace Integration
- **Library tracking**: `SourceFileId` includes library name
- **Cross-library errors**: Can show "error in library foo at file.hwml:10:5"
- **Portable**: `.hwmli` files can store relative paths

### 4. Developer Experience
- **Human-readable**: Line:column easier to understand than byte offsets
- **IDE integration**: Direct LSP compatibility
- **Debuggability**: Locations visible in printed IR

## Comparison with Alternatives

### Alternative 1: Byte Offsets (Rust-style)

**Approach**: Store `Range<usize>` byte offsets, convert to line:column on demand

**Rejected because**:
- ❌ Must convert for CIRCT (expensive)
- ❌ Requires storing file text for conversion
- ❌ Two representations (internal vs external)
- ❌ Less stable for incremental compilation

### Alternative 2: Span Interner (Rust-style compression)

**Approach**: Pack locations into 4 bytes using bit manipulation and interner

**Rejected because**:
- ❌ Over-optimization for current needs
- ❌ Complex implementation (bit packing, span tables)
- ❌ Still need line:column for CIRCT
- ✅ Salsa interning already provides compression

### Alternative 3: Keep Current SourceRange

**Approach**: Use existing `SourceRange` with byte offsets

**Rejected because**:
- ❌ Doesn't match CIRCT expectations
- ❌ No workspace integration
- ❌ No library tracking
- ❌ Conversion overhead

## Open Questions

### Q1: Should we store end column for ranges?

~~**Decision**: Start with single point, add ranges later if needed~~

**REVISED DECISION**: ✅ **Use full ranges (FileLineColRange) from day 1**

**Reasons**:
1. ✅ **You control the parser** - Already have start/end byte offsets
2. ✅ **MLIR native support** - `FileLineColRange` is a first-class type
3. ✅ **Better diagnostics** - Can highlight exact spans in errors
4. ✅ **LSP compatibility** - LSP expects ranges, not points
5. ✅ **No overhead** - Salsa interning makes this nearly free
6. ✅ **Future-proof** - Won't need to migrate later

**MLIR syntax examples**:
```mlir
// Single point (old style)
loc("file.hwml":10:5)

// Full range (what we'll use)
loc("file.hwml":10:5 to 10:15)
loc("file.hwml":10:5 to 12:8)  // Multi-line span
```

### Q2: How to handle macro expansion chains?

**Current design**: No explicit macro tracking

**Future work**: Add `CallSiteLoc`-style tracking
```rust
LocationData::Expansion {
    macro_name: Word<'db>,
    call_site: Location<'db>,  // Where macro was invoked
    expansion_site: Location<'db>,  // Where expanded code came from
}
```

### Q3: Should synthetic locations track provenance?

**Current design**: Simple label

**Alternative**: Richer provenance
```rust
LocationData::Synthetic {
    label: Word<'db>,
    origin: Option<Location<'db>>,  // Original source location if any
    reason: SyntheticReason,  // Why synthetic?
}

enum SyntheticReason {
    Desugaring,
    Metavariable,
    Quotation,
    Implicit,
}
```

**Decision**: Keep simple for now, add if needed

## Implementation Checklist

### Phase 1: Core Types (1-2 days)
- [ ] Add `Location` and `LocationData` to `hwml-core/src/source_range.rs`
- [ ] Implement `Display` trait for locations
- [ ] Add LSP conversion methods
- [ ] Write unit tests for location creation and display

### Phase 2: Parser Integration (2-3 days)
- [ ] Update `hwml-surface` to use `Location` instead of `Range<usize>`
- [ ] Thread `SourceFileId` through parser
- [ ] Compute line:column during parsing using `LineInfo`
- [ ] Update all surface syntax types

### Phase 3: Core IR Integration (3-4 days)
- [ ] Update `Syntax` nodes to store `Location`
- [ ] Update elaborator to preserve and thread locations
- [ ] Update all IR construction to include locations
- [ ] Remove old `SourceRange` type

### Phase 4: CIRCT Backend (1-2 days)
- [ ] Implement `CirctContext::to_mlir_location()`
- [ ] Update all CIRCT translation to use new locations
- [ ] Test MLIR output includes correct FileLineColLoc

### Phase 5: Workspace Integration (2-3 days)
- [ ] Update workspace to create `SourceFileId` for each file
- [ ] Thread file IDs through compilation pipeline
- [ ] Update error messages to show library names
- [ ] Test multi-library error reporting

### Phase 6: Serialization (2-3 days)
- [ ] Implement `SerializedLocation` type
- [ ] Add serialize/deserialize methods
- [ ] Test round-trip through `.hwmli` format
- [ ] Ensure portable paths (relative to library root)

### Total Estimate: 11-17 days (2-3.5 weeks)

## Conclusion

This design provides:
1. **Native CIRCT format** - Line:column throughout
2. **Aggressive compression** - Salsa interning
3. **Workspace integration** - Library tracking built-in
4. **Synthetic support** - First-class compiler-generated locations
5. **Future-proof** - Extensible to ranges, macros, etc.

The migration can be done incrementally, with minimal disruption to existing code.

## References

- [Rust Compiler Span Design](https://rustc-dev-guide.rust-lang.org/appendix/glossary.html#span)
- [MLIR Location Design](https://mlir.llvm.org/docs/Diagnostics/#source-locations)
- [Scala Position API](https://www.scala-lang.org/api/2.13.0/scala-reflect/scala/reflect/api/Position.html)
- [LSP Position Specification](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#position)
- [HWML Package Manager Design](./package-manager.md) - See "Source Location Architecture" section
