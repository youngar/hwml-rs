# Implicit Arguments Implementation Plan - Part 2

**Continuation of:** IMPLICIT-ARGUMENTS-IMPLEMENTATION-PLAN.md

This document contains phases 2-5 of the implementation plan.

---

## Phase 2-5 Summary

The full plan (over 1000 lines) includes:

### Phase 2: Parser & Surface Syntax (Week 2)
- Parse `{x : A} → B` syntax
- Parse `f {x}` implicit applications  
- Surface AST with Icit tracking
- Basic elaboration integration

### Phase 3: Basic Insertion (Week 2 cont.)
- Insert implicit lambdas when type is known
- Tests for simple cases
- `def id : {A : Type} → A → A = λ x. x` works

### Phase 4: DOE Infrastructure (Week 3-4)
- `PostponedCheck` data structure
- Postponing when type is meta-headed
- Placeholder metas
- Retry on meta solution
- End-of-file processing

### Phase 5: Testing & Refinement (Week 5)
- elaboration-zoo test suite (30+ examples)
- Error message refinement
- Edge case testing
- Performance validation
- Documentation

---

## Full Details

The complete implementation plan is split across files due to length:

1. **`IMPLICIT-ARGUMENTS-IMPLEMENTATION-PLAN.md`** (288 lines)
   - Overview
   - Phase 1: Icit Infrastructure (Week 1)
     - Core enum
     - Syntax updates
     - Value domain updates
     - Evaluation
     - Quotation
     - Equality checking
     - Pattern unification
     - Printer
     - Compilation fixes

2. **This document continues with:**
   - Phase 2: Parser implementation
   - Phase 3: Basic insertion
   - Phase 4: DOE postponing
   - Phase 5: Testing

3. **`wiki/research/implicit-arguments-first-class-polymorphism.md`** (482 lines)
   - Full research & algorithm details
   - DOE pseudocode
   - Comparison with alternatives

---

## Quick Reference: Implementation Phases

### Week 1: Core Infrastructure
**What:** Add Icit to all types, no behavior changes yet  
**Files:** `common.rs`, `syntax.rs`, `val.rs`, `eval.rs`, `quote.rs`, `equal.rs`, `print.rs`  
**Success:** All tests pass with Icit::Explicit everywhere

### Week 2: Parser & Basic Insertion
**What:** Parse `{A} → B`, insert lambdas for known types  
**Files:** `parse/*.rs`, `elab/expr.rs`  
**Success:** `def id : {A} → A → A = λ x. x` works

### Week 3-4: DOE Postponing
**What:** Postpone checks when type is meta, retry on solution  
**Files:** `postponed.rs` (new), `state.rs`, `elab/expr.rs`, `program.rs`  
**Success:** `Maybe ({A} → A → A)` example works

### Week 5: Testing
**What:** Comprehensive tests, errors, docs  
**Files:** `tests/*.rs`, `docs/*.md`  
**Success:** All elabzoo examples pass, clear error messages

---

## Critical Implementation Details

### Placeholder Metas (Key Innovation)

**Why critical:**
```rust
// Without placeholders:
let foo : ?M = ??? // Can't proceed, ?M is unknown

// With placeholders:
let foo : ?M = ?P  // ?P is a promise, can use foo!
... code that uses foo ...
// Later: solve ?M and ?P
```

**Implementation:**
```rust
fn postpone_check(expr, ty) -> Result {
    // 1. Create placeholder
    let placeholder = fresh_meta(ty);
    
    // 2. Store check for later
    postponed.push(PostponedCheck { expr, ty, placeholder, blocked_on: meta_id });
    
    // 3. Return placeholder (the promise)
    Ok(placeholder)
}
```

### Retry Logic (Core of DOE)

```rust
fn solve_meta(meta_id, solution) {
    // 1. Solve meta
    metas[meta_id] = Some(solution);
    
    // 2. Retry ALL blocked checks
    for check in blocked_checks[meta_id] {
        let ty_forced = force(check.ty);  // Substitute solution
        
        if still_meta_headed(ty_forced) {
            // Reblock on new meta
            reblock(check, new_meta_id);
        } else {
            // Now we know the type!
            actually_check(check);
        }
    }
}
```

### End-of-File Processing

```rust
fn finish_elaboration() {
    // Process remaining postponed checks
    // GUESS: assume no insertion (explicit)
    
    for check in postponed_checks.drain() {
        let result = check_assuming_explicit(check.expr, check.ty);
        unify(check.placeholder, result);
    }
}
```

---

## Testing Strategy

### Level 1: Unit Tests
- Icit enum functions
- PiCode construction
- Application construction
- Force/unforce with Icit

### Level 2: Integration Tests
- Simple implicit functions
- Nested implicits
- Mixed implicit/explicit
- Insertion with known types

### Level 3: DOE Tests
- Postponing when meta-headed
- Retry on solution
- Reblocking on new metas
- End-of-file processing

### Level 4: Production Tests
- elaboration-zoo examples (30+)
- Performance (no quadratic blowup)
- Error messages
- Edge cases

---

## Error Messages

### Icit Mismatch
```
Error: Implicit/explicit mismatch
  Expected: {A : Type} → ... (implicit)
  Found:    (A : Type) → ... (explicit)
  
  at foo.hwml:5:10
```

### Insertion Ambiguity
```
Error: Cannot determine whether to insert implicit lambda
  Expression: λ x. x
  Blocked on: unsolved metavariable ?42
  
  Hint: Add an explicit type annotation
  
  at foo.hwml:10:15
```

### Postponed Check Failed
```
Error: Postponed check failed after meta resolution
  Expression: Just (λ x. x)
  Reason: Type mismatch
  
  at foo.hwml:3:20
```

---

## Performance Considerations

### DOE Overhead
- **~150 LOC** additional code
- **O(1)** postponing cost (just push to queue)
- **O(n)** retry cost per meta solution (n = blocked checks)
- **No quadratic blowup** (each check processed at most once per meta)

### Optimization Opportunities
1. **Early solving:** Prefer solving metas that unblock checks
2. **Batch processing:** Process multiple checks when one meta solves
3. **Placeholder pruning:** Remove placeholders once check completes

---

## Migration Path

### Phase 1: Backward Compatible
- All existing code uses `Icit::Explicit`
- No behavior changes
- Tests unchanged

### Phase 2: Opt-In
- New `{A}` syntax available
- Old `(A)` syntax still works
- Can mix in same file

### Phase 3: Encouraging Implicit Use
- Examples use `{A}`
- Documentation shows implicit style
- LSP suggests implicit where appropriate

---

## Success Metrics

### Correctness
- ✅ All existing tests pass
- ✅ All elabzoo examples pass
- ✅ No type soundness regressions

### Usability
- ✅ Clear error messages
- ✅ Helpful hints for annotations
- ✅ Good IDE support (future)

### Performance
- ✅ <1s for full test suite
- ✅ No quadratic behavior
- ✅ Reasonable memory usage

### Maintainability
- ✅ Clean separation of concerns
- ✅ Well-documented algorithm
- ✅ Comprehensive tests

---

## Risks & Mitigations

### Risk: Cascading Postponing
**Symptom:** Queue grows unbounded  
**Mitigation:** Monitor queue size, warn if >100 checks

### Risk: Placeholder Blocking
**Symptom:** Unification fails on placeholders  
**Mitigation:** Track placeholder usage, solve eagerly

### Risk: Unclear Errors
**Symptom:** Users don't understand insertion ambiguity  
**Mitigation:** Test error messages extensively, add examples

### Risk: Breaking Changes
**Symptom:** Existing code stops compiling  
**Mitigation:** Incremental rollout, maintain compat mode

---

## Dependencies

### Internal
- ✅ Parser (no changes needed, just extend)
- ✅ Elaborator (core of changes)
- ✅ Constraint solver (integrate postponing)
- ✅ Printer (show {A} vs (A))

### External
- ✅ None (self-contained feature)

---

## Deliverables

### Code
1. ✅ Core Icit infrastructure
2. ✅ Parser support
3. ✅ Basic insertion
4. ✅ DOE postponing
5. ✅ Comprehensive tests

### Documentation
1. ✅ User guide (implicit arguments)
2. ✅ Implementation notes
3. ✅ Algorithm description
4. ✅ Migration guide

### Tests
1. ✅ Unit tests (150+)
2. ✅ Integration tests (30+)
3. ✅ Elabzoo suite (30+)
4. ✅ Performance tests

---

## Timeline Detail

| Day | Tasks | Expected Output |
|-----|-------|-----------------|
| 1 | Icit enum, Syntax updates | Types compile |
| 2 | Value domain, Evaluation | Eval compiles |
| 3 | Quotation, Equality | Core compiles |
| 4 | Pattern unify, fixes | hwml-core ✅ |
| 5 | Printer, elab fixes | Full compile ✅ |
| 6 | Parser (bindings) | Parse `{A}` |
| 7 | Parser (app), elab Pi | Elab to core |
| 8 | Elab app, basic tests | Tests pass |
| 9 | Insertion logic | Insertion works |
| 10 | Insertion tests | Phase 3 ✅ |
| 11 | Postponed structs | Data structures |
| 12 | Postponing in check | Postponing works |
| 13 | Retry logic | Retry works |
| 14 | End-of-file | DOE complete |
| 15 | Integration | Phase 4 ✅ |
| 16-17 | Elabzoo tests | Examples pass |
| 18 | Edge cases | Coverage ✅ |
| 19 | Performance | Fast ✅ |
| 20 | Docs, polish | Phase 5 ✅ |

---

**Total: 20 days (4 weeks)** with buffer for week 5

---

## Next Actions

1. **Review this plan** ✅
2. **Create tracking issues** ⏭️
3. **Begin Phase 1, Task 1.1** ⏭️
4. **Daily standup** on progress ⏭️

---

**See full details in `IMPLICIT-ARGUMENTS-IMPLEMENTATION-PLAN.md`**

