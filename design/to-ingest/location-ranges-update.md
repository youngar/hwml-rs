# Updated Design: Full Source Ranges (Not Points)

## Key Insight from User

> "Does CIRCT support source ranges as locations? I feel like it's a slightly better fit for us since we own the parser"

**Answer**: ✅ YES! MLIR has `FileLineColRange` as a first-class location type.

## Revised Decision

**Use `FileLineColRange` with full start/end positions from day 1**

```rust
LocationData::FileLineColRange {
    file: SourceFileId<'db>,
    start_line: u32,
    start_column: u32,
    end_line: u32,
    end_column: u32,
}
```

## Why This Is Better

### 1. You Control the Parser
When parsing, you already have:
```rust
// From lalrpop or hand-written parser
let def_span = (start_offset: 0, end_offset: 14);  // "def half_adder"
```

Converting to ranges is trivial:
```rust
let (start_line, start_col) = line_info.loc(start_offset);
let (end_line, end_col) = line_info.loc(end_offset);

Location::new(db, LocationData::FileLineColRange {
    file: file_id,
    start_line: (start_line + 1) as u32,
    start_column: (start_col + 1) as u32,
    end_line: (end_line + 1) as u32,
    end_column: (end_col + 1) as u32,
})
```

### 2. MLIR Native Support

MLIR's `FileLineColRange` type:
```c
// From MLIR C API
MlirLocation mlirLocationFileLineColRangeGet(
    MlirContext context,
    MlirStringRef filename,
    unsigned startLine,
    unsigned startColumn,
    unsigned endLine,
    unsigned endColumn
);
```

This is **exactly** what we're storing! Direct mapping, zero conversion.

### 3. Better Error Messages

**With points only:**
```
error: type mismatch at adder.hwml:2:16
  Expected: Bit
  Got: Bit × Bit
```

**With full ranges:**
```
error: type mismatch at adder.hwml:2:16-21
    2 |   let sum := xor a b in
      |              ^^^^^^^
  Expected: Bit
  Got: Bit × Bit
```

Much better! Can show exact code span.

### 4. LSP Compatibility

Language Server Protocol **requires ranges**, not points:
```typescript
// LSP Range type
interface Range {
  start: Position;  // { line: number, character: number }
  end: Position;
}
```

Our `FileLineColRange` converts directly:
```rust
pub fn to_lsp_range<Db>(&self, db: &'db Db) 
    -> Option<((u32, u32), (u32, u32))>
{
    match self.data(db) {
        LocationData::FileLineColRange {
            start_line, start_column,
            end_line, end_column, ..
        } => {
            Some((
                (start_line - 1, start_column - 1),
                (end_line - 1, end_column - 1),
            ))
        }
        _ => None,
    }
}
```

### 5. No Memory Overhead (Thanks to Interning)

**Without interning:**
- Point: 16 bytes (file_id + line + col)
- Range: 24 bytes (file_id + start_line + start_col + end_line + end_col)

**With Salsa interning:**
- Both: 8 bytes (just the interned ID!)
- Actual data stored once per unique location

Since we use Salsa, storing ranges is nearly **free**.

## MLIR Examples

### Single Line Range
```mlir
loc("adder.hwml":2:16 to 2:21)
```
Represents `xor a b` on line 2, columns 16-21.

### Multi-Line Range
```mlir
loc("adder.hwml":2:10 to 4:5)
```
Represents a multi-line expression spanning lines 2-4.

### Point (Still Supported)
If start == end:
```mlir
loc("adder.hwml":2:16)
```
MLIR optimizes single-point ranges automatically.

## Migration From Current Design

### Current (in docs, not implemented)
```rust
SourceRange<'db> {
    source: Source<'db>,
    range: Range<usize>,  // byte offsets
}
```

### New
```rust
pub type SourceRange<'db> = Location<'db>;

Location<'db> {
    data: LocationData::FileLineColRange {
        file: SourceFileId<'db>,
        start_line, start_column,
        end_line, end_column,
    }
}
```

**Key change**: Replace byte `Range<usize>` with line:column ranges.

## Implementation Notes

### Parser Integration
```rust
// In your parser action
fn make_def(
    db: &dyn Database,
    file_id: SourceFileId,
    line_info: &LineInfo,
    span_start: usize,
    span_end: usize,
    // ... other fields
) -> Def {
    let (start_line, start_col) = line_info.loc(span_start);
    let (end_line, end_col) = line_info.loc(span_end);
    
    let loc = Location::new(db, LocationData::FileLineColRange {
        file: file_id,
        start_line: (start_line + 1) as u32,
        start_column: (start_col + 1) as u32,
        end_line: (end_line + 1) as u32,
        end_column: (end_col + 1) as u32,
    });
    
    Def { loc, /* ... */ }
}
```

### Display Formatting
```rust
impl<'db> Location<'db> {
    pub fn display<Db>(&self, db: &'db Db) -> String {
        match self.data(db) {
            LocationData::FileLineColRange {
                file, start_line, start_column,
                end_line, end_column,
            } => {
                let path = file.canonical_path(db).text(db);
                if start_line == end_line {
                    format!("{}:{}:{} to {}:{}",
                        path, start_line, start_column,
                        end_line, end_column)
                } else {
                    // Multi-line
                    format!("{}:{}:{} to {}:{}",
                        path, start_line, start_column,
                        end_line, end_column)
                }
            }
            // ...
        }
    }
}
```

## Conclusion

Using `FileLineColRange` instead of single points is the right choice because:

1. ✅ **Parser-friendly** - You already have start/end from parsing
2. ✅ **MLIR-native** - Direct API support, zero conversion
3. ✅ **Better UX** - Can highlight exact spans in errors
4. ✅ **LSP-ready** - Ranges are what LSP expects
5. ✅ **Zero cost** - Salsa interning makes it free

There's no downside, only benefits!
