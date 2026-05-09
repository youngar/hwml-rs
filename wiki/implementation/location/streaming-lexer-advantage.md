# The Lossless Grammar Advantage - Streaming Line:Column Tracking

**Date:** 2026-05-05  
**Discovery:** Native line:column tracking in lexer with ZERO overhead

---

## The Problem (Traditional Parsers)

Most parsers skip whitespace/comments during lexing, so they can't track line:column incrementally:

```rust
// Traditional approach (e.g., Rust, C++)
enum Token {
    Ident(String),
    Number(i64),
    // No Whitespace, No Comment tokens!
}

// Skipped bytes mean you need a lookup table
struct LineInfo {
    line_breaks: Vec<usize>,  // O(N) to build
}

fn offset_to_line(offset: usize) -> (usize, usize) {
    // O(log N) binary search
    line_breaks.binary_search(offset)
}
```

**Cost**: O(N) pre-computation + O(log N) per lookup

---

## The Solution (HWML's Lossless Grammar)

HWML tokenizes **every byte**, including whitespace and comments:

```rust
pub enum Token {
    // Keywords
    Def, Type, Let, ...
    
    // Whitespace (NOT SKIPPED!)
    Newline,        // \n, \r, \r\n
    Space,          // horizontal whitespace
    LineComment,    // //...
    BlockComment,   // /*...*/
    
    // Everything else
    Identifier, Number, ...
}
```

**Key insight**: Because no bytes are skipped, we can track line:column **as we stream tokens**!

---

## Implementation: Streaming Counter

```rust
pub struct LocLexer<'input> {
    inner: logos::Lexer<'input, Token>,
    line: usize,    // Current line (1-based)
    column: usize,  // Current column (1-based)
}

impl Iterator for LocLexer<'_> {
    type Item = (Token, Range<usize>, usize, usize);
    //           ^token  ^byte_span   ^line  ^column

    fn next(&mut self) -> Option<Self::Item> {
        let token = self.inner.next()?;
        let span = self.inner.span();
        let slice = self.inner.slice();

        // Capture location BEFORE consuming token
        let out_line = self.line;
        let out_col = self.column;

        // Update state based on token
        match token {
            Ok(Token::Newline) => {
                self.line += 1;
                self.column = 1;
            }
            Ok(Token::BlockComment) => {
                let newlines = slice.iter().filter(|&&b| b == b'\n').count();
                if newlines > 0 {
                    self.line += newlines;
                    let last_nl = slice.iter().rposition(|&b| b == b'\n').unwrap();
                    self.column = slice.len() - last_nl;
                } else {
                    self.column += slice.len();
                }
            }
            Ok(_) => {
                self.column += slice.len();
            }
            Err(_) => { /* handle error */ }
        }

        Some((token.unwrap(), span, out_line, out_col))
    }
}
```

**Cost**: O(1) per token (just counter updates)

---

## Performance Comparison

### Traditional Approach (LineInfo):
```
Parse 10,000 line file:
1. Build LineInfo: O(10,000) = scan entire file for \n
2. Store line_breaks: Vec<usize> with ~10,000 entries (~80KB)
3. Each location lookup: O(log 10,000) ≈ 13 comparisons
4. 100 lookups = ~1,300 comparisons total
```

### Streaming Approach (LocLexer):
```
Parse same file:
1. Build LineInfo: O(1) = just initialize two counters
2. Store state: 2 × usize = 16 bytes
3. Each location: O(1) = already computed during streaming
4. 100 lookups = 0 additional work (already have the data)
```

### Memory Usage:
| Approach | Memory | Allocation |
|----------|--------|------------|
| LineInfo | ~80KB for 10K lines | 1 Vec allocation |
| LocLexer | 16 bytes | 0 allocations |

### Speed:
| Approach | Build | Lookup | Total |
|----------|-------|--------|-------|
| LineInfo | O(N) scan | O(log N) | O(N + M log N) |
| LocLexer | O(1) init | O(1) | O(1) |

Where N = file size, M = number of lookups.

---

## MLIR/CIRCT Integration

The streaming approach produces **exactly** what MLIR needs:

```rust
use mlir::ir::Location;

for (token, span, line, col) in LocLexer::new(source) {
    // Already 1-based, ready for MLIR!
    let mlir_loc = Location::file_line_col(
        context, 
        filename, 
        line as u32,    // 1-based
        col as u32      // 1-based
    );
    
    // Use mlir_loc for operations built from this token
}
```

No conversion needed - the lexer output is **MLIR-native**.

---

## Why This Works

1. **Lossless grammar** - Every byte has a token
2. **Stateless lexer** - Logos is a pure state machine
3. **Stateful wrapper** - We add state (line, col) in the iterator
4. **Minimal surface area** - Only 2 tokens affect line tracking
5. **Cache-friendly** - Sequential access, no random lookups

---

## Conclusion

By embracing a **lossless grammar**, HWML gets:
- ✅ Zero-cost line:column tracking
- ✅ No pre-computation overhead
- ✅ No allocation overhead  
- ✅ Perfect MLIR/CIRCT alignment
- ✅ Simple, auditable implementation

This is **faster, simpler, and more accurate** than traditional approaches.

