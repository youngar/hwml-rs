# Analysis: State vs Provenance in HWML Parser

**Date:** 2026-05-11
**Question:** Why do we have both `state_stack` and `provenance_stack`? Could they be unified?

---

## TL;DR - Key Differences

| Aspect | **State Stack** | **Provenance Stack** |
|--------|----------------|---------------------|
| **Purpose** | Controls parser execution flow | Tracks context for error messages |
| **Lifetime** | Very short (popped immediately when processed) | Longer (spans entire parsing operation) |
| **Structure** | Carries partial parse results | Carries human-readable context |
| **Updates** | Every micro-step of parsing | Only at significant boundaries |
| **Usage** | Dispatcher reads to know what to do next | Error handler reads to explain what went wrong |

---

## The Core Architectural Difference

### State Stack: The **Control Flow Machine**

The `state_stack` is the **work queue** for the parser. It answers: **"What should I do next?"**

```rust
pub enum State {
    DefStart { loc },
    DefAfterName { loc, name },
    DefAfterBindings { loc, name, bindings },
    DefAfterType { loc, name, bindings, ty },
    DefAfterValue { loc, name, bindings, ty },
}
```

**Characteristics:**
- **High churn rate**: States are pushed and popped constantly (multiple per token)
- **Carries intermediate results**: `name`, `bindings`, `ty` accumulate as parsing proceeds
- **Ephemeral**: `DefAfterName` exists for ~5 tokens, then is popped forever
- **Execution semantics**: Dispatcher pattern-matches on State variants to call handlers

**Example flow for `def foo : Nat := 42`:**
```
Push DefStart
Pop DefStart → handle_def_start → Push DefAfterName{name: "foo"}
Pop DefAfterName → handle_def_after_name → Push DefAfterType{name, ty}
Pop DefAfterType → handle_def_after_type → Push DefAfterValue{name, ty}
Pop DefAfterValue → handle_def_after_value → Create Def statement
```

### Provenance Stack: The **"Where Am I" Context**

The `provenance_stack` is the **breadcrumb trail**. It answers: **"What operation is in progress?"**

```rust
pub enum ParseContext {
    Def { name: String, loc: Range<usize> },
    Namespace { name: String, loc: Range<usize> },
    FunLambda { loc: Range<usize> },
}
```

**Characteristics:**
- **Low churn rate**: Pushed once when entering an operation, popped once when exiting
- **No intermediate results**: Only stores human-readable strings and locations
- **Long-lived**: `Def { name: "foo" }` stays on stack for hundreds of tokens while parsing body
- **Diagnostic semantics**: Used to build error messages like "while parsing def 'foo'"

**Example flow for same `def foo : Nat := 42`:**
```
Enter context: Def { name: "foo", loc }
  ... (parse bindings, type, value - provenance stays constant)
Exit context
```

---

## Why They Can't Be Unified

### Attempted Unification #1: "Use State for Provenance"

**Problem:** States don't live long enough.

When parsing `def foo (x : Nat) : Nat := x + 1`, if an error occurs in the body expression `x + 1`:
- **State stack** at error: `[ExprStart, ExprFinish{partial: "x"}]`
  - No mention of "def" or "foo"! Those states were popped 50 tokens ago.
- **Provenance stack** at error: `[Def { name: "foo" }]`
  - Still knows we're in def "foo" because we entered context once and haven't exited yet.

### Attempted Unification #2: "Keep States on Stack Longer"

**Problem:** This breaks the state machine architecture.

The Carbon-style explicit state machine requires states to be **immediately popped and processed**. Keeping them on the stack would:
1. Defeat the purpose of the flat call stack (we'd build up depth)
2. Require scanning through the stack to find "what to do next"
3. Lose the accumulation pattern (later states carry results from earlier states)

### Attempted Unification #3: "Use Provenance for Control Flow"

**Problem:** Provenance lacks execution details.

`ParseContext::Def` doesn't know:
- Whether we've parsed the name yet
- What bindings we've accumulated
- Whether we have a type annotation
- Where the value expression is stored

It only knows: "We're parsing a def named 'foo'". This is perfect for errors, useless for execution.

---

## Concrete Example: Nested Match in Def

```hwml
def foo (x : Bool) : Nat :=
    match x with
    | true => 1
    | false => <ERROR HERE>
    end
```

**At the error location:**

### State Stack (Work Queue)

```
[
    MatchClauses {
        loc: 5..80,
        scrutinee: Identifier("x"),
        clauses: [Clause { pattern: "true", body: "1" }]
    },
    ExprStart { min_prec: Lowest }  // ← Currently parsing the body expression
]
```
**Contains:** What we're doing RIGHT NOW (parsing an expression in the second match clause).
**Missing:** That we're in a def named "foo". That context was popped 100 tokens ago.

### Provenance Stack (Context Breadcrumbs)
```
[
    Def { name: "foo", loc: 0..200 },
    MatchExpression { loc: 5..80 },
    MatchClause { pattern_loc: 50..60 }
]
```
**Contains:** The full context path: "In def 'foo', inside a match, in the second clause".
**Missing:** That we've already parsed one clause, what precedence level we're at, etc.

### Error Message Quality

**Without provenance (state only):**
```
Error: Unexpected end of match clause
  at line 4, column 20
```

**With provenance:**
```
Error: Unexpected end of match clause
  at line 4, column 20
  while parsing match clause for pattern 'false'
    in match expression
      in definition 'foo'
```

---

## The Original Intuition Was Partially Correct

You said: "My original thinking is that these would actually be the same thing - the error message looks at the parsing state to figure out what we were doing when everything went wrong."

This **would** work in a traditional recursive descent parser:

```rust
// Traditional recursive descent
fn parse_def() -> Def {
    let name = parse_name()?;
    let bindings = parse_bindings()?;
    let value = parse_expr()?;  // ← If error here, Rust call stack = context!
    //                             Stack: [parse_program, parse_def, parse_expr]
    Def { name, bindings, value }
}
```

In traditional recursive descent:
- **Rust call stack = parse context**
- You can walk the stack to see "parse_def → parse_expr"
- Don't need a separate provenance stack

But in the **Carbon-style flat state machine**:
- **Rust call stack is always depth 1**: `main_loop → dispatcher → handler → return`
- The execution context (what to do next) lives in the **state stack**
- The semantic context (what operation we're in) needs a **separate tracking mechanism**

---

## Should They Be Different? YES

### 1. **Separation of Concerns**

**State Stack:**
- Concern: Parser execution mechanics
- Owned by: The parser implementation
- Changes: Every parse step

**Provenance Stack:**
- Concern: Error reporting and diagnostics
- Owned by: The error system
- Changes: Only at semantic boundaries

### 2. **Different Lifecycles**

**State:** Microstate
- Lives for 1-10 tokens
- Popped as soon as processed
- High frequency push/pop

**Provenance:** Macro-context
- Lives for 10-1000 tokens
- Persists across entire parsing operation
- Low frequency push/pop

### 3. **Different Consumers**

**State Stack:**
- Read by: `handle_state()` dispatcher
- Purpose: Determine which handler to call
- Access pattern: Pop one, process, maybe push more

**Provenance Stack:**
- Read by: `emit_error()` and `capture_provenance()`
- Purpose: Build human-readable error messages
- Access pattern: Clone entire stack when creating error nodes

### 4. **Type Safety**

**State:** Strongly typed variants carrying exact data needed for next step
```rust
DefAfterName { loc: Range<usize>, name: Id }
```

**Provenance:** Simplified view for human consumption
```rust
Def { name: String, loc: Range<usize> }
```

Provenance doesn't need `Id` (with provenance tracking) - just the string name for error messages.

---

## The Confusion Point

The confusion likely comes from seeing operations like:

```rust
// In handle_def_start
self.enter_context(ParseContext::Def { name, loc });
self.push_state(State::DefAfterName { loc, name });
```

It looks like we're duplicating information! But:
- **State** carries the actual `Id` struct (with provenance) for use in construction
- **Context** carries just the string name for human error messages
- State will be popped in 10 tokens; Context will remain for 1000 tokens

---

## Analogy: Web Request Tracing

### State Stack = Call Stack
```javascript
execute_handler(request) {
    const user = parseUser(request);
    const action = parseAction(request);
    const result = performAction(user, action);
    return result;
}
```
**Purpose:** Control flow - what function runs next
**Lifetime:** Ephemeral - functions return immediately

### Provenance Stack = Trace Context
```javascript
trace.startSpan("handling-checkout-request", {
    userId: "123",
    cartId: "abc"
});
// ... many function calls ...
trace.endSpan();
```
**Purpose:** Observability - what operation is in progress
**Lifetime:** Long - spans entire operation including sub-calls

---

## Conclusion

**State and Provenance serve fundamentally different purposes and cannot be unified.**

| Question | Answer |
|----------|--------|
| Could we use state for provenance? | No - states are too short-lived |
| Could we use provenance for control flow? | No - provenance lacks execution details |
| Is the duplication wasteful? | No - they have different lifecycles and consumers |
| Should they be merged in the future? | No - separation of concerns is correct |

The architecture is sound. The state stack is the **engine** (controls execution), and the provenance stack is the **telemetry** (explains what's happening for diagnostics). Both are essential and complementary.
