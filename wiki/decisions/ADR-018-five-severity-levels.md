# ADR-018: Five Severity Levels (Add Bug Level)

**Status:** Approved  
**Date:** 2026-05-08  
**Phase:** Diagnostic Framework (Week 1 revision)  
**Confidence:** 0.95  
**Deciders:** Architecture Team (from Asai + LSP spec analysis)  
**Context Tags:** #diagnostics #severity #error-handling #asai #lsp  
**Reference:** `external/asai/src/Diagnostic_data.ml`, LSP specification

---

## Context

Diagnostic systems categorize messages by severity to help users prioritize what to fix. The question is: **How many severity levels do we need, and what should they be?**

### Requirements

1. **User errors** - Code the user wrote incorrectly
2. **Warnings** - Suspicious but not fatal
3. **Internal errors** - Compiler bugs users should report
4. **LSP compatibility** - Map to LSP diagnostic severity levels
5. **Clear semantics** - Developers know when to use each level

---

## Alternatives Considered

### Option 1: Two Levels (Error/Warning)

Minimal set: errors stop compilation, warnings don't.

**Pros:**
- Simple to understand
- Clear semantics

**Cons:**
- ❌ No way to indicate compiler bugs vs. user errors
- ❌ Can't distinguish hints from warnings
- ❌ LSP has 4 levels (Hint/Info/Warning/Error) - lossy mapping

**Verdict:** **Too coarse** - loses important distinctions

### Option 2: Four Levels (LSP Standard)

Match LSP exactly: Hint, Information, Warning, Error.

```rust
enum Severity {
    Error,
    Warning,
    Information,  
    Hint,
}
```

**Pros:**
- ✅ Direct LSP mapping (no conversion needed)
- Standard across language servers
- Clear IDE rendering

**Cons:**
- ❌ No distinction for compiler bugs vs. user errors
- ❌ When elaborator panics, how do we categorize it?
- ❌ Users can't filter "show me only bugs I should report"

**Verdict:** **Good but incomplete** - missing internal error category

### Option 3: Five Levels with Bug (Chosen - Asai Approach)

Add `Bug` severity for internal compiler errors.

```rust
enum DiagnosticSeverity {
    Bug,      // Internal compiler error - please report!
    Error,    // User error - fix your code
    Warning,  // Suspicious - might want to fix
    Info,     // Informational - FYI
    Hint,     // Code smell - consider refactoring
}
```

**Pros:**
- ✅ Clear distinction: Bug (us) vs. Error (user)
- ✅ Users know which errors to report as issues
- ✅ Can surface elaborator/kernel bugs explicitly
- ✅ LSP mapping: Bug → Error (acceptable)
- ✅ Matches Asai (proven in production)
- ✅ Helps with quality metrics (track internal bugs separately)

**Cons:**
- One more level than LSP (but maps cleanly)

**Verdict:** **Best option** - adds critical distinction

### Option 4: Six+ Levels (Rejected)

Add even more granularity (Fatal, Bug, Error, Warning, Info, Hint, Deprecation, etc.).

**Pros:**
- Maximum expressiveness

**Cons:**
- ❌ Diminishing returns
- ❌ Unclear when to use each level
- ❌ Complicates UI (too many colors/icons)

**Verdict:** **Rejected** - unnecessary complexity

---

## Decision

**Use five severity levels: Bug, Error, Warning, Info, Hint.**

### Type Definition

```rust
/// Diagnostic severity level
///
/// Ordered from most to least severe.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DiagnosticSeverity {
    /// Internal compiler bug - the compiler has a bug, not the user's code.
    /// Users should report these as issues.
    /// 
    /// Example: "elaborator panic: unexpected None in solve_constraint"
    Bug,
    
    /// User error - the code is incorrect and cannot be compiled.
    /// 
    /// Example: "type mismatch: expected Nat, found Bool"
    Error,
    
    /// Warning - the code is suspicious but might be intentional.
    /// 
    /// Example: "unused variable 'x'"
    Warning,
    
    /// Informational message - FYI, not a problem.
    /// 
    /// Example: "inferred type for 'x' is Nat"
    Info,
    
    /// Hint - code smell or style suggestion.
    /// LSP spec: "not shown as squiggles, just in problems panel"
    /// 
    /// Example: "this pattern match is exhaustive but could be simplified"
    Hint,
}
```

### LSP Mapping

```rust
impl DiagnosticSeverity {
    pub fn to_lsp(&self) -> lsp_types::DiagnosticSeverity {
        match self {
            Self::Bug => lsp_types::DiagnosticSeverity::ERROR,
            Self::Error => lsp_types::DiagnosticSeverity::ERROR,
            Self::Warning => lsp_types::DiagnosticSeverity::WARNING,
            Self::Info => lsp_types::DiagnosticSeverity::INFORMATION,
            Self::Hint => lsp_types::DiagnosticSeverity::HINT,
        }
    }
}
```

**Note:** Both `Bug` and `Error` map to LSP `ERROR`. In LSP, we can distinguish via the diagnostic message or code (e.g., "INTERNAL ERROR:" prefix or "BUG" code prefix).

---

## Rationale

### Why `Bug` Severity is Critical

**1. User Experience**

When users see "type mismatch" they know it's their code. When they see "INTERNAL ERROR: elaborator panic" they know to report it to us, not debug their code.

**Bad (without Bug):**
```
error: unexpected None in solve_constraint
```
User thinks: "What did I do wrong?"

**Good (with Bug):**
```
bug: INTERNAL COMPILER ERROR
╭ This is a bug in the HWML compiler, not your code.
│ Please report this at: https://github.com/hwml/hwml/issues
│
│ Error: unexpected None in solve_constraint
│ Location: hwml-elab/src/solver.rs:142
│ Elaborating: function 'process' at main.hwml:42
╯
```
User thinks: "OK, I'll file a bug report with this info."

**2. Quality Metrics**

Track internal errors separately:
- `Bug` count = bugs in our code (should trend to zero)
- `Error` count = bugs in user code (expected)

This helps prioritize compiler fixes.

**3. Debuggability**

Bug diagnostics can include:
- Rust backtrace
- Elaborator state dump
- Provenance trail
- AST at failure point

This is inappropriate for user errors.

### Asai Evidence

Asai has exactly this 5-level system:

```ocaml
type severity =
  | Hint
  | Info
  | Warning
  | Error
  | Bug    (* "A serious error likely caused by a bug in the proof assistant" *)
```

From Asai docs:
> "**Bug:** A serious error likely caused by a bug in the proof assistant. You would want the end user to report the bug back to you. This is useful for indicating that certain branches in a pattern matching should be 'impossible', while printing out debugging information in case the program logic is flawed."

This is **exactly our use case** - elaborator reaching "impossible" states, kernel violations, etc.

---

## Consequences

### Positive

✅ **Clear user communication** - Users know what to report
✅ **Better metrics** - Track compiler bugs separately
✅ **Debuggability** - Can include more info in Bug diagnostics
✅ **Matches Asai** - Proven approach in production theorem provers
✅ **LSP compatible** - Clean mapping to LSP severity

### Negative

⚠️ **Five levels vs. four** - One more than LSP (but acceptable)

### Implementation Impact

**Example Usage:**

```rust
// User error
Diagnostic::error("type mismatch")
    .with_code("E0308")
    .with_explanation("expected Nat, found Bool")
    .build()

// Compiler bug
Diagnostic::bug("elaborator panic")
    .with_code("BUG001")
    .with_explanation("This is an internal compiler error.")
    .with_backtrace(/* Rust backtrace */)
    .with_note("Please report at https://github.com/...")
    .build()
```

---

## Terminal Rendering

**Colors (ANSI):**
- `Bug`: Red background + white text (very visible!)
- `Error`: Red text
- `Warning`: Yellow text
- `Info`: Cyan text
- `Hint`: Blue text (dim)

**Icons:**
- `Bug`: 🐛 or ￫ (special marker)
- `Error`: ￫ (error marker)
- `Warning`: ⚠ (warning triangle)
- `Info`: ℹ (info symbol)
- `Hint`: 💡 (lightbulb)

---

## Related Decisions

- **ADR-001:** LCF Kernel - Kernel violations should be `Bug` severity
- **ADR-016:** No Column Alignment - Terminal rendering for all severities

---

## References

- **Asai Source:** `external/asai/src/Diagnostic_data.ml`
- **LSP Specification:** https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#diagnostic
- **Asai Documentation:** Design rationale for Bug severity

---

## Migration Plan

**Week 1 (In Progress):**
1. ✅ Initial 4-level system (Error/Warning/Info/Hint)
2. 🔄 Add `Bug` level (this ADR)
3. Update builder API
4. Add terminal colors for Bug

**Usage Guidelines:**

Use `Bug` when:
- Elaborator reaches "impossible" state
- Kernel rejects term it should accept (kernel bug)
- Salsa query panics unexpectedly
- Metavar solver hits assertion failure
- Pattern match assumed unreachable

Use `Error` when:
- Type mismatch
- Name not in scope
- Arity mismatch
- Parse error
- Any user code problem

---

**Status:** Approved for implementation in Week 1 revision
