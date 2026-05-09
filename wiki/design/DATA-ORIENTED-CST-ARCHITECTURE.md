# Data-Oriented CST Architecture for LSP

## Executive Summary

**The Holy Grail:** Pre-lex the entire file into a flat, contiguous array of 8-byte tokens. This is how the fastest modern compilers (Zig, V) achieve ridiculous compilation speeds.

**Key Innovation:** Absolute byte offsets + flat token arrays = **cache-line perfection** + **error recovery without Red/Green trees**.

**Critical Insight:** LSP compilers are **pull-based query engines**, not push-based pipelines. You must be demand-driven from Day 1.

---

## Part 1: The Data-Oriented Token Array

### Cache-Line Perfection

**Problem with interleaved lex/parse:** Pulling characters one-by-one while building tree nodes trashes your CPU's instruction cache and branch predictor.

**Solution:** Pre-lex everything into a tight, flat array:

```rust
#[repr(C)]
struct Token {
    kind: u16,   // TokenKind enum (Identifier, Plus, LBrace, etc.)
    start: u32,  // Absolute byte offset in source string
    len: u16,    // Token length (65k byte limit per token is fine)
}
// Total: 8 bytes per token
```

**Why this is fast:**
- **Cache-friendly:** Flat array streams into L1 cache via CPU prefetcher
- **No string ops during parsing:** Parser just jumps through pure integers
- **SIMD-ready:** Can vectorize token scanning with AVX2/NEON
- **Predictable branches:** Tight loop, CPU branch predictor loves it

### The Pipeline

```
Source String (immutable)
    ↓
[Lexer: tight byte-scanning loop]
    ↓
Flat Token Array: [Token; N]  (8 bytes × N, contiguous)
    ↓
[Parser: array traversal with sync recovery]
    ↓
Flat Node Array: [Node; M]  (immutable CST with absolute spans)
    ↓
[Variational Solver]
    ↓
Disambiguated AST + Diagnostics/Fixits
```

---

## Part 2: Error Recovery Without Red/Green Trees

### The Secret: Absolute Byte Offsets

**The problem we're solving:** How do you prevent a missing semicolon from shifting all token offsets and destroying the rest of the file's byte spans?

**Answer:** Use **absolute byte offsets** (`start: u32`) tied to the original, immutable source string.

**Why this works:**
- Spans **never shift** because they're absolute positions in the current buffer
- When user deletes a semicolon, next token's offset simply reflects its actual position in the new text
- Re-lex + re-parse whole file on every keystroke (fast enough with flat arrays!)
- Parser always operates on the absolute truth of current text buffer
- **No "old tree" to sync with** = no cascading offset bugs

### Panic Mode Synchronization with Poison Nodes

When parser hits syntax error (e.g., `let x = ;`):

1. **Detect Error:** Parser expects expression after `=`, but sees `;`
2. **Emit Diagnostic:** Fire error to diagnostic system: *"Expected expression, found `;` at span X"*
3. **Synchronize:** Enter recovery loop, skip tokens until finding synchronization point:
   - For statements: `;`, `}`, or keywords like `let`, `fn`, `def`
   - For expressions: `)`, `]`, `,`
4. **Insert Poison Node:** Create `Error` node in CST covering all skipped garbage tokens
5. **Resume:** Seamlessly continue parsing next valid statement

```rust
enum NodeKind {
    FunctionDef,
    VariableDecl,
    Expression,
    // ...
    Error {  // Poison node
        span: Span,           // Covers all garbage tokens
        expected: &'static str,  // What we expected to see
        found: TokenKind,     // What we actually found
    },
}
```

### Fixits on Broken Trees

Because your CST explicitly contains `Error` nodes with exact byte spans:

```rust
// User types: fn foo() { let x = 5 }  (missing semicolon)

// Parser flow:
1. Parse `let x = 5` successfully
2. Expect `;`, find `}`
3. Create Error node at position after `5`
4. Emit diagnostic: "Expected `;`"
5. Continue parsing

// Fixit engine:
1. See Error node
2. Check token stream: last valid token was `5` at offset 250
3. Emit TextEdit: { range: 250..250, new_text: ";" }
4. LSP client inserts semicolon
5. Re-parse: Error gone!
```

**Mathematical guarantee:** Local syntax error will **never corrupt** byte spans of surrounding code.

---

## Part 3: LSP as a Pull-Based Query Engine

### Traditional vs LSP Compilers

**Traditional (push pipeline):**
```
File → Lex → Parse → Typecheck → Codegen → Binary
       (one direction, batch processing)
```

**LSP (pull-based queries):**
```
Editor asks: "What's the type at line 14, col 22?"
Compiler: "Let me check... only recompute what changed... here's the type"
```

**Critical difference:** Do the **absolute minimum** work to answer the specific question.

### The Virtual File System (VFS)

LSP compiler can't read `std::fs` - truth lives in unsaved editor buffers!

```rust
struct SourceDatabase {
    files: HashMap<FileId, String>,
    versions: HashMap<FileId, u32>,  // Revision tracking
}

// On textDocument/didChange:
1. Update in-memory string for that file
2. Assign new version number
3. Invalidate cached data derived from old version
```

**We already have this!** HWML uses `hwml-vfs` with Salsa.

### Demand-Driven Computation (Salsa Queries)

Can't re-run entire semantic analyzer on every keystroke - need memoization!

```rust
// Instead of calling functions, request data from database

#[salsa::tracked]
fn get_ast(db: &dyn Db, file: SourceFile) -> Arc<CstRoot> {
    // Cached! Only recomputes if file version changed
}

#[salsa::tracked]  
fn get_function_type(db: &dyn Db, func_id: FunctionId) -> Type {
    // Cached! Only recomputes if function signature changed
}
```

**If user edits body of Function B:**
- VFS increments version for that file
- Editor asks for autocomplete in Function A
- System realizes signature of B hasn't changed
- **Uses cached semantic data** - instant response!

**We already have this!** HWML uses Salsa queries throughout.

### Line/Column ↔ Byte Offset Bridge

**LSP Protocol Flaw:** Talks in `(Line, Column)` coordinates (UTF-16 code units!), but fast parsers use **absolute byte offsets**.

**Solution:** Fast index for instant translation:

```rust
struct LineIndex {
    line_starts: Vec<u32>,  // Byte offset where each line begins
}

impl LineIndex {
    fn offset_to_position(&self, offset: u32) -> (u32, u32) {
        // Binary search line_starts
    }
    
    fn position_to_offset(&self, line: u32, col: u32) -> u32 {
        self.line_starts[line] + col
    }
}
```

**We already have this!** HWML has `LineInfo` in `hwml-support`.

### Find Node at Offset

Flat CST with absolute spans = **binary search** or simple recursive descent:

```rust
// LSP: textDocument/hover at offset 402
1. Binary search CST array for narrowest node containing offset 402
2. Find Identifier node → "user_id"
3. Resolve "user_id" in symbol table
4. Return type info to LSP

// O(log N) because flat array with sorted spans!
```

---

## Part 4: Robust Name Resolution on Broken Code

**Example:**
```rust
fn process() {
    let config = load_config();
    confi  // Cursor here, waiting for autocomplete (no semicolon!)
}
```

**Traditional parser:** Crashes or stops after `confi`

**Our parser:**
1. Parse `let config = ...` successfully
2. Hit `confi`, expect semicolon, find EOF
3. Create `Error` node after `confi`
4. **Don't drop the AST!** Keep `config` in scope

**LSP autocomplete at cursor:**
1. Find `Error` node at cursor
2. Walk up tree: find enclosing block
3. Collect all variables declared before cursor
4. Successfully suggest `config`!

**This is why Poison Nodes are crucial** - they preserve scope even in broken code.

---

## Part 5: Day-1 LSP Architecture Stack

If building from scratch today:

```
┌─────────────────────────────────────┐
│  LSP Router (JSON-RPC)              │  ← textDocument/hover, etc.
└──────────────┬──────────────────────┘
               ↓
┌─────────────────────────────────────┐
│  Query Engine (Salsa)               │  ← Memoization, incremental
└──────────────┬──────────────────────┘
               ↓
┌─────────────────────────────────────┐
│  Parser (Flat CST + Error Nodes)    │  ← Panic mode recovery
└──────────────┬──────────────────────┘
               ↓
┌─────────────────────────────────────┐
│  Pre-Lexer (Flat Token Array)       │  ← 8-byte tokens, cache-perfect
└──────────────┬──────────────────────┘
               ↓
┌─────────────────────────────────────┐
│  VFS + Line Indexer                 │  ← String storage, LSP ↔ offset
└─────────────────────────────────────┘
```

**HWML already has most of this!**
- ✅ VFS: `hwml-vfs`
- ✅ Line Indexer: `hwml-support/LineInfo`
- ✅ Query Engine: Salsa everywhere
- ✅ LSP Router: `hwml-lsp-server`
- ⚠️  Parser: LALRPOP (not error-recovering yet)
- ❌ Pre-Lexer: Need to add flat token array

---

## Part 6: Migration Path for HWML

### Current State (AST with LALRPOP)
```
Source → LALRPOP → AST (no error recovery)
                    ↓
                 Salsa queries
                    ↓
                 LSP features
```

**Problems:**
- LALRPOP stops on first error
- No Poison Nodes for broken code
- Lexing interleaved with parsing (slower)

### Future State (Flat CST with Error Recovery)
```
Source → Pre-Lexer → [Token] → Parser → [Node] (CST with Error nodes)
           ↓                               ↓
        Cache-perfect              Salsa queries
                                       ↓
                                  LSP features
```

**Wins:**
- ✅ Continues parsing after errors
- ✅ Poison Nodes preserve scope
- ✅ 2-10x faster (cache-friendly)
- ✅ Better autocomplete on broken code

### Incremental Migration Steps

1. **Phase 1: Keep LALRPOP, Add Better Diagnostics** (Week 4-5)
   - Improve error messages (✅ DONE!)
   - Add basic fixits using byte offsets
   - Works with current AST

2. **Phase 2: Add Pre-Lexer** (Post-MVP)
   - Write flat token array lexer
   - Keep LALRPOP for now, feed it tokens
   - Benchmark: should be 2x faster

3. **Phase 3: Replace Parser with Error Recovery** (Future)
   - Hand-written recursive descent or combinator parser
   - Emit Poison Nodes on errors
   - Full IDE experience on broken code

4. **Phase 4: Add Trivia Tokens** (Polish)
   - Roslyn-style leading/trailing trivia
   - Format-preserving fixits
   - Production quality

---

## Conclusion

**Data-oriented design principles:**
1. **Flat arrays over pointer-chasing** - CPU loves sequential access
2. **Absolute positions over relative** - no offset math, no bugs
3. **Immutability everywhere** - share via Arc, zero copies
4. **Poison Nodes over crashes** - preserve partial information
5. **Pull-based queries over push pipelines** - only compute what's needed

**HWML is well-positioned!** We already have VFS, Salsa, and LSP infrastructure. The path forward is clear: add pre-lexing and error recovery to unlock 10x better IDE experience.

**References:**
- Zig compiler architecture
- V compiler (pure C, blazingly fast)
- rust-analyzer rowan library
- Salsa query system
