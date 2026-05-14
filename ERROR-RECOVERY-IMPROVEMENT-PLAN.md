# HWML Parser Error Recovery - Implementation Plan

**Date:** 2026-05-12  
**Goal:** Improve error recovery based on Carbon parser comparison  
**Estimated Effort:** 20-28 hours (2-3 weeks)  
**Risk Level:** LOW (all additive changes)

---

## Executive Summary

### Current State ✅

The hwml-surface parser has **solid foundations**:
- ✅ Type-safe error variants (`Expression::Error`, `Statement::Invalid`)
- ✅ Automatic context tracking via state stack
- ✅ Statement-level synchronization working well
- ✅ Infrastructure exists (bracket tracking, block depth)
- ✅ Never crashes on bad input

### Identified Gaps 🔄

Based on Carbon comparison (see `CARBON-ERROR-RECOVERY-COMPARISON.md`):
1. ❌ Bracket stacks tracked but **not used for recovery**
2. ❌ No expression-level sync points (only statement-level)
3. ❌ No AST validation pass (Carbon has `Tree::Verify()`)
4. ❌ `handle_recovery.rs` is empty placeholder
5. ❌ Limited pattern recovery strategies
6. ❌ Some test coverage gaps

### Comparison with Carbon

| Feature | Carbon | HWML Current | HWML After Plan |
|---------|--------|--------------|-----------------|
| Error marking | `has_error` flag | Error variants | ✅ Keep variants |
| Statement sync | ✅ Yes | ✅ Yes | ✅ Yes |
| Expression sync | ✅ Yes | ❌ No | ✅ **Add** |
| Bracket-aware skip | ✅ Yes | ❌ No | ✅ **Add** |
| Tree validation | ✅ `Tree::Verify()` | ❌ No | ✅ **Add** |
| Context tracking | Separate | State stack | ✅ Keep (better!) |

---

## Implementation Phases

### Phase 1: Bracket-Aware Recovery [HIGH PRIORITY]

**Effort:** 4-6 hours | **Risk:** LOW | **Files:** `handle_recovery.rs`, `test_recovery.rs`

**Goal:** Use existing `brace_stack` and `paren_stack` for smart error recovery.

**Functions to implement in `handle_recovery.rs`:**

```rust
impl<'input> Context<'input> {
    /// Skip to the matching closing brace using brace_stack
    pub(super) fn skip_to_matching_brace(&mut self) -> bool { ... }
    
    /// Skip to the matching closing paren using paren_stack  
    pub(super) fn skip_to_matching_paren(&mut self) -> bool { ... }
    
    /// Skip entire bracketed region when recovery needed
    pub(super) fn skip_bracketed_region(&mut self) { ... }
    
    /// Enhanced statement boundary skip with bracket awareness
    pub(super) fn skip_to_statement_boundary_smart(&mut self) { ... }
}
```

**Integration points:**
- Use in `handle_namespace.rs` when namespace body has errors
- Use in `handle_match.rs` when match clause is malformed
- Use in `handle_expr.rs` when parenthesized expression fails

**Tests to add (4 new):**
1. `test_skip_to_matching_brace_simple`
2. `test_skip_nested_braces`
3. `test_skip_to_matching_paren`
4. `test_skip_bracket_region_at_eof`

**Example:**
```hwml
namespace Foo { bad content with { nested } braces } def bar := 1
```
- Before: Skips token-by-token, many errors, may fail to parse `bar`
- After: Skips to outer `}`, focused error, successfully parses `bar`

---

### Phase 2: Expression-Level Sync Points [HIGH PRIORITY]

**Effort:** 3-4 hours | **Risk:** LOW | **Files:** `context.rs`, `handle_expr.rs`, `test_recovery.rs`

**Goal:** Add fine-grained synchronization within expressions.

**Functions to add in `context.rs`:**

```rust
/// Check if at expression synchronization point
pub fn at_expr_sync_point(&self) -> bool {
    matches!(self.peek(),
        Some(Token::Comma) | Some(Token::RParen) | Some(Token::RBrace) |
        Some(Token::Pipe) | Some(Token::FatArrow) |
        // Statement keywords also sync expressions
        Some(Token::Def) | Some(Token::Meta) | ... | None
    )
}

/// Skip to next expression boundary
pub(super) fn skip_to_expr_boundary(&mut self) {
    while !self.at_end() && !self.at_expr_sync_point() {
        self.advance();
    }
}
```

**Integration in `handle_expr.rs`:**
- Before pushing `Expression::Error`, call `skip_to_expr_boundary()`
- Check `at_expr_sync_point()` to avoid eating delimiters

**Tests to add (3 new):**
1. `test_expr_recovery_at_comma`
2. `test_expr_recovery_missing_operand`
3. `test_expr_recovery_invalid_operator`

**Example:**
```hwml
def foo := (1 + bad stuff , 2)
```
- Before: Error on `bad`, skips entire expression, loses `2`
- After: Error on `bad`, syncs at `,`, successfully parses `2`

---

### Phase 3: Tree Validation [MEDIUM PRIORITY]

**Effort:** 6-8 hours | **Risk:** LOW | **Files:** `syntax/validation.rs` (new), `syntax/mod.rs`, `context.rs`

**Goal:** Add debug-mode AST validation like Carbon's `Tree::Verify()`.

**Create `syntax/validation.rs`:**
```rust
#[cfg(debug_assertions)]
pub fn verify_program(program: &Program) { /* verify all statements */ }

#[cfg(debug_assertions)]
fn verify_expression(expr: &Expression) {
    match expr {
        Expression::App(app) => assert!(app.elements.len() >= 2),
        Expression::Id(id) => assert!(&*id.value != "<error>"),
        // ...
    }
}
```

**Integration:** Call from `Context::finalize()` in debug builds only.

**Tests:** 3 new validation tests.

---

### Phase 4: Pattern Recovery [MEDIUM PRIORITY]

**Effort:** 3-4 hours | **Risk:** LOW | **Files:** `handle_pattern.rs`, `test_recovery.rs`

**Goal:** Pattern-specific sync points (FatArrow, Pipe, Comma).

**Tests:** 2 new pattern recovery tests.

---

### Phase 5: Comprehensive Testing [LOW PRIORITY]

**Effort:** 4-6 hours | **Files:** `test_recovery.rs`

**Goal:** 30+ tests covering all edge cases (see plan for categories).

---

## Summary

| Phase | Priority | Effort | Key Outcome |
|-------|----------|--------|-------------|
| 1. Bracket-aware | HIGH | 5h | Skip balanced regions |
| 2. Expression sync | HIGH | 3.5h | Fine-grained recovery |
| 3. Tree validation | MEDIUM | 7h | Debug AST checks |
| 4. Pattern recovery | MEDIUM | 3.5h | Pattern sync points |
| 5. Testing | LOW | 5h | 30+ error tests |
| **TOTAL** | | **24h** | **Production-grade recovery** |

**See full details above for implementation specifics, examples, and testing strategy.**
