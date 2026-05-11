# Design vs Implementation: Detailed Comparison

**Date:** 2026-05-11
**Status:** Post-provenance-stack-removal analysis
**Session:** Continuation-based parser refactoring

---

## Executive Summary

### What We Built vs What Was Designed

| Aspect | Design Documents | Actual Implementation | Match? |
|--------|-----------------|----------------------|--------|
| **Core Architecture** | State machine with typed stacks | ✅ Implemented exactly as designed | ✅ YES |
| **Provenance Tracking** | Separate `provenance_stack` | ❌ **REMOVED** - Uses `state_stack` instead | ⚠️ **BETTER** |
| **Diagnostic Context** | Via separate ParseContext enum | Via `State::diagnostic_context()` | ⚠️ **SIMPLER** |
| **Continuation Pattern** | Implied but not explicit | ✅ **Explicitly documented via user correction** | ⚠️ **CLEARER** |
| **Error Recovery** | Block-depth aware | ✅ Implemented | ✅ YES |
| **Typed Stacks** | expr_stack, statement_stack, etc. | ✅ Implemented | ✅ YES |

**Key Discovery:** The design called for a `provenance_stack`, but the implementation proved that **the state stack IS the provenance stack** because parent states remain as continuations.

---

## Part 1: Provenance Tracking - Design vs Reality

### Design Document Said (PARSER-PROVENANCE-TRACKING.md):

```rust
pub struct Context<'input> {
    // ... existing fields
    provenance_stack: Vec<ParseContext>,  // ← SEPARATE STACK
}

impl Context {
    pub fn enter_context(&mut self, ctx: ParseContext) {
        self.provenance_stack.push(ctx);
    }

    pub fn exit_context(&mut self) {
        self.provenance_stack.pop();
    }
}
```

**Pattern:** Manually push/pop `ParseContext` as you enter/exit parsing operations.

---

### What We Actually Built:

```rust
pub struct Context<'input> {
    // NO provenance_stack!
    state_stack: Vec<State>,  // ← This IS the provenance
}

impl State {
    pub fn diagnostic_context(&self) -> Option<String> {
        match self {
            State::NamespaceEnd { name, .. } =>
                Some(format!("in namespace '{}'", name.value)),
            State::DefAfterValue { name, .. } =>
                Some(format!("in definition '{}'", name.value)),
            // ... other continuation states
            _ => None  // Micro-states return None
        }
    }
}

impl Context {
    pub fn emit_error(&mut self, msg: impl Into<String>) {
        let mut error_msg = msg.into();

        // Scan state_stack backwards for context
        for state in self.state_stack.iter().rev() {
            if let Some(context) = state.diagnostic_context() {
                error_msg.push_str(&format!("\n  while {}", context));
            }
        }

        self.errors.push(ParseError { message: error_msg, ... });
    }
}
```

**Pattern:** Parent continuation states REMAIN on the stack. Just scan them for context.

---

## Part 2: Why The Implementation Is Better

### The Design's Hidden Flaw

The design assumed state_stack is "ephemeral" - states are immediately popped.

**But that's wrong for continuation-based parsing!**

```


### Continuation-Based Architecture (The Truth)

When parsing `namespace Std { def foo := 42 }`, the state stack progression is:

```
Step 1: Parse "namespace Std {"
  Stack: [NamespaceEnd, NamespaceBody]  ← Parent continuation STAYS

Step 2: NamespaceBody pops, sees "def", pushes Statement
  Stack: [NamespaceEnd, Statement]

Step 3: Statement pops, pushes DefStart
  Stack: [NamespaceEnd, DefStart]

Step 4: DefStart pops, pushes DefAfterName
  Stack: [NamespaceEnd, DefAfterName]

... (more def states)

Step N: DefAfterValue completes, pops, creates Def statement
  Stack: [NamespaceEnd]  ← Parent STILL THERE!

Step N+1: NamespaceEnd pops, collects statements, done
  Stack: []
```

**KEY INSIGHT:** `NamespaceEnd` remains on the stack from Step 1 through Step N!

---

### User's Correction (The Breakthrough)

> "The state stack MUST hold the parent context. Parent states act as **continuations**."

This means:
1. **State stack = Call stack** (in a traditional recursive parser)
2. **Parent states = Return addresses** (continuations)
3. **Scanning state_stack = Walking the call stack** (for diagnostics)

Therefore:
- ✅ `state_stack` has all the context we need
- ❌ `provenance_stack` is redundant
- ✅ Just add `diagnostic_context()` to filter out micro-states

---

## Part 3: The Async Pattern Discovery

### Problem We Hit

Initial handlers were **synchronous**:

```rust
// WRONG - Doesn't work with state machine!
pub fn handle_def_after_bindings(...) {
    self.consume(Token::Colon);
    self.parse_expression(Precedence::Lowest);  // Pushes state
    let ty = self.pop_expr();  // PANIC! Not parsed yet!
}
```

### The Fix - Continuation Pattern

```rust
// CORRECT - Continuation-based
pub fn handle_def_after_bindings(...) {
    self.consume(Token::Colon);

    // 1. Push continuation (runs LAST)
    self.push_state(State::DefAfterType {
        loc, name, bindings,
        ty: dummy_expr  // Ignored
    });

    // 2. Push parser (runs FIRST)
    self.parse_expression(Precedence::Lowest);

    // 3. Return immediately
}

pub fn handle_def_after_type(..., _ty: Box<Expression>) {
    let ty = self.pop_expr();  // Pop real value
    // Continue...
}
```

**This is the critical pattern the design didn't make explicit!**

---

## Part 4: What Matches Perfectly

### ✅ State Enum with Data

```rust
pub enum State {
    DefAfterType {
        loc: Range<usize>,
        name: Id,
        bindings: Bindings,
        ty: Box<Expression>,
    },
}
```

### ✅ Typed Value Stacks

```rust
expr_stack: Vec<Box<Expression>>,
statement_stack: Vec<Statement>,
// No downcasting needed!
```

### ✅ Main Parse Loop

```rust
while !self.context.at_end() {
    self.context.push_state(State::Statement);
    while let Some(state) = self.context.pop_state() {
        self.handle_state(state);
    }
}
```

---

## Part 5: Test Results vs Timeline

**Design Timeline:** 4 weeks (22 days)

**Actual Progress (after file recovery):**
- Day 1-2: Foundation + Statements ✅
- Day 3: Refactor provenance ✅
- **Current Status:** 40/66 tests passing (60.6%)

**On track for:** ~2.5 weeks total (ahead of schedule despite setback!)

---

## Part 6: Design Improvements Made

### 1. Simpler Diagnostic Context

**Design:** Separate `ParseContext` enum

**Better:** Just add method to existing `State` enum

### 2. No Redundant Stack

**Design:** Both `state_stack` and `provenance_stack`

**Better:** Just `state_stack` (it IS the context!)

### 3. Explicit Continuation Documentation

**Design:** Implied but not stated

**Better:** User correction made it crystal clear

---

## Summary Table

| Feature | Design Spec | Implementation | Status |
|---------|------------|----------------|--------|
| State machine | ✓ Specified | ✓ Built | ✅ Match |
| Typed stacks | ✓ Specified | ✓ Built | ✅ Match |
| Block depth tracking | ✓ Specified | ✓ Built | ✅ Match |
| Main loop | ✓ Specified | ✓ Built | ✅ Match |
| Provenance stack | ✓ Specified | ❌ **Removed** | ⚠️ **Better** |
| Diagnostic context | Implied | ✓ Explicit method | ⚠️ **Clearer** |
| Continuation pattern | Implied | ✓ Documented | ⚠️ **Clearer** |
| Error recovery | ✓ Specified | ✓ Built | ✅ Match |

**Legend:**
- ✅ Match = Follows design exactly
- ⚠️ Better/Clearer = Improvement over design
- ❌ Removed = Correctly identified as redundant

---

## Key Learnings

1. **The state stack IS the provenance** - No separate tracking needed
2. **Continuation pattern is critical** - Must be explicit in design
3. **Async state machine** - Can't mix sync/async patterns
4. **User guidance was right** - Local AI hallucinated flaws

The implementation is **better than the design** because we discovered the hidden architectural truth: in a continuation-based parser, the state stack serves triple duty (execution, context, diagnostics).
