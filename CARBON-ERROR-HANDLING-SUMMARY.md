# Carbon Error Handling - Key Findings

**Date:** 2026-05-12  
**Source:** Analysis of CARBON-ERROR-RECOVERY-COMPARISON.md and related documentation

---

## Core Philosophy (Identical to HWML)

> **"On invalid input, maintain a structurally valid parse tree"**

Both parsers follow the same principle:
- ✅ Never crash on bad input
- ✅ Always produce a tree (even with errors)
- ✅ Mark errors but keep structure intact
- ✅ Enable tools (formatters, IDEs) to work on broken code

---

## Error Tracking Mechanisms

### Carbon's Approach

**Node-level error flags:**
```cpp
struct ParseNode {
    NodeKind kind;
    Lex::TokenIndex token;
    int subtree_start;
    bool has_error;  // ← Marks this node as erroneous
};
```

**Error propagation:**
```cpp
if (!state.has_error) {
    context.emitter().Emit(error_message);
}
context.ReturnErrorOnState();  // Set has_error on parent
```

### HWML's Approach (Better!)

**Type-safe error variants:**
```rust
pub enum Expression {
    // ... normal variants ...
    Error(ExpressionError),  // ← Dedicated error variant
}

pub enum Statement {
    // ... normal variants ...
    Invalid(StatementError),  // ← Dedicated error variant
}
```

**Context tracking via state stack:**
```rust
pub fn emit_error(&mut self, msg: impl Into<String>) {
    let mut error_msg = msg.into();
    
    // Scan state stack backwards for context
    for state in self.state_stack.iter().rev() {
        if let Some(context) = state.diagnostic_context() {
            error_msg.push_str(&format!("\n  while {}", context));
        }
    }
    
    self.errors.push(ParseError { message: error_msg, ... });
}
```

**Result:** Context is automatic!
```
Expected ':=' after def type
  while in definition 'foo'
  while in namespace 'Std.Nat'
```

---

## Error Recovery Strategies

### 1. Invalid Parse Nodes

**When:** Structure is too broken to recover specific construct.

**Carbon:**
```cpp
context.AddLeafNode(NodeKind::InvalidParse, context.Consume(), /*has_error=*/true);
```

**HWML:**
```rust
self.push_expr(self.make_error_expr("malformed expression"));
```

**Same strategy:** Mark error, continue parsing.

---

### 2. Synchronization Points

**When:** Need to skip ahead to known safe point.

**Carbon's sync points:**
- Semicolons (`;`)
- Closing braces (`}`)
- Statement keywords
- Lesser indent level

**HWML's sync points:**
- Statement keywords (`def`, `namespace`, `inductive`, etc.)
- Closing braces (`}`)
- EOF

**Skip implementation:**

```rust
pub fn skip_to_statement_boundary(&mut self) {
    while !self.at_end() && !self.at_sync_point() {
        self.advance();
    }
}
```

---

### 3. Bracket-Aware Skipping

**Carbon's advantage:** Pre-computed bracket matching in lexer.

```cpp
// Carbon: TokenizedBuffer pre-computes bracket matches
// Used for skipping bracketed regions during recovery
context.SkipTo(closing_bracket);
```

**HWML's current state:** Tracks brackets but doesn't use for recovery.

```rust
// We have these!
brace_stack: Vec<Range<usize>>,
paren_stack: Vec<Range<usize>>,

// But we don't use them for recovery yet
// ← OPPORTUNITY FOR IMPROVEMENT (Phase 1 of plan)
```

---

### 4. Redundant Error Suppression

**Goal:** Avoid cascading errors from single mistake.

**Carbon:**
```cpp
if (!state.has_error) {
    // Only emit if child didn't already error
    context.emitter().Emit(...);
}
```

**HWML:**
```rust
if matches!(partial.as_ref(), Expression::Error(_)) {
    // Don't emit redundant "expected )" error
    return;
}
```

**Same concept:** Check if child already errored before adding parent error.

---

## Comparison Table

| Feature | Carbon | HWML | Winner |
|---------|--------|------|--------|
| **Error marking** | `has_error` flag | Error variants | 🤝 Tie (different styles) |
| **Propagation** | `ReturnErrorOnState()` | Error nodes propagate | ✅ HWML (simpler) |
| **Context tracking** | Separate mechanism | State stack scan | ✅ HWML (automatic) |
| **Type safety** | Runtime flag | Compile-time variant | ✅ HWML (type-safe) |
| **Statement sync** | ✅ Yes | ✅ Yes | 🤝 Tie |
| **Expression sync** | ✅ Yes | ❌ No | ✅ Carbon |
| **Bracket-aware skip** | ✅ Yes | ❌ No | ✅ Carbon |
| **Tree validation** | ✅ `Tree::Verify()` | ❌ No | ✅ Carbon |
| **Never crash** | ✅ Yes | ✅ Yes | 🤝 Tie |

---

## What HWML Does Better

1. **Type-safe error variants** - Compile-time guarantees vs runtime flags
2. **Automatic context** - State stack provides context for free
3. **Simpler error propagation** - Error nodes naturally bubble up

---

## What Carbon Does Better

1. **Bracket-aware skipping** - Pre-computed bracket matches enable fast skip
2. **Expression-level sync** - More granular recovery points
3. **Tree validation** - Debug-mode verification catches parser bugs
4. **Battle-tested** - Production use at Google

---

## Recommendations for HWML

### ✅ Already Excellent (Keep)

1. ✅ Error variants (type-safe, idiomatic Rust)
2. ✅ State stack context tracking (elegant, automatic)
3. ✅ Top-level recovery loop (prevents infinite loops)

### 🔄 Improvements Needed (Add)

1. ❌ **Use bracket stacks for recovery** (Phase 1)
   - Infrastructure exists, just not used
   - Enable fast skip of balanced regions
   
2. ❌ **Expression-level sync points** (Phase 2)
   - Currently only sync at statement boundaries
   - Add comma, paren, brace as expr sync points
   
3. ❌ **Tree validation pass** (Phase 3)
   - Add `verify_program()` like Carbon's `Tree::Verify()`
   - Debug-mode only, catches parser bugs early
   
4. ❌ **Populate handle_recovery.rs** (Phases 1-4)
   - Currently empty placeholder
   - Add all recovery helper functions

---

## Conclusion

**HWML's error recovery is already production-quality:**
- ✅ Same core philosophy as Carbon
- ✅ Better in some areas (type safety, context tracking)
- 🔄 Gaps are **implementation details**, not fundamental design flaws

**With the planned improvements:**
- HWML will match or exceed Carbon's capabilities
- While maintaining superior type safety and simplicity
- Estimated 20-28 hours of work for full parity

**Verdict:** Our design is sound, just needs to leverage existing infrastructure!

---

## References

- `CARBON-ERROR-RECOVERY-COMPARISON.md` - Full comparison document
- `ERROR-RECOVERY-IMPROVEMENT-PLAN.md` - Implementation plan
- `crates/hwml-surface/src/parse/` - Current implementation
