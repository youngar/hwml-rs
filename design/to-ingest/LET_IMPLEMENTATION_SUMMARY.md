# Let Expression Implementation - Summary & Review

## Quick Overview

We're adding `let` expressions to hwml-rust Core IR with these properties:

1. **Syntax**: `let %name : type = expr; body`
2. **Preservation**: Let structure survives eval/quote roundtrip
3. **Transparency**: Supports definitional equality (let x = e; x ≡ e)
4. **Simplicity**: No gluing (yet) - use Let as a Value constructor

## What You Provided

You gave me:

1. **Research on Glued Evaluation** - The industry-standard solution (Agda/Lean/Hazel)
2. **Formal Core IR Spec** - Precise typing rules and operational semantics
3. **Clear Requirements** - Preserve structure while maintaining transparency

## My Proposed Solution

### Architecture: "Let as Value Constructor" (Simplified Approach)

Instead of implementing full glued evaluation immediately, I propose:

```rust
// Syntax (Core IR)
enum Syntax {
    Let(Let),  // let %name : type = expr; body
}

struct Let {
    name: String,
    type_ann: RcSyntax,  // Explicit type
    expr: RcSyntax,       // Bound expression
    body: RcSyntax,       // Body (uses de Bruijn index 0)
}

// Semantic Domain
enum Value {
    Let(Let),  // Preserved structure
}

struct Let {
    name: String,
    ty: Rc<Value>,       // Evaluated type
    value: Rc<Value>,    // Evaluated expression
    body: Closure,       // Body as closure
}
```

### Why This Approach?

**Compared to Eager Substitution:**
- ✅ Preserves Let structure (eager substitution loses it)
- ✅ Enables pretty printing of Let bindings
- ✅ Maintains source-level structure in Core IR

**Compared to Full Glued Evaluation:**
- ✅ Much simpler to implement (no Lazy, no dual representation)
- ✅ Follows existing patterns (Pi, Lambda use similar structure)
- ✅ Can upgrade to gluing later if needed
- ⚠️ Less elegant for δ-reduction (but we can add it incrementally)

### Key Implementation Points

**1. Evaluation** - Preserve structure:
```rust
fn eval_let(env, let_expr) {
    let ty = eval(env, let_expr.type_ann);
    let value = eval(env, let_expr.expr);
    let body = Closure::new(env.local, let_expr.body);
    Value::Let { name, ty, value, body }  // Don't substitute!
}
```

**2. Quotation** - Reconstruct syntax:
```rust
fn quote_let(let_val, body_ty, depth) {
    let ty_syn = quote(let_val.ty, Universe);
    let val_syn = quote(let_val.value, let_val.ty);
    
    // Quote body with fresh variable
    let var = fresh_variable(depth, let_val.ty);
    let body_val = run_closure(let_val.body, [var]);
    let body_syn = quote(body_val, body_ty, depth + 1);
    
    Syntax::Let { name, type_ann: ty_syn, expr: val_syn, body: body_syn }
}
```

**3. Typechecking** - Synth mode:
```rust
fn synth_let(ctx, let_expr) {
    // Check type annotation is a type
    check(ctx, let_expr.type_ann, Type);
    let ty = eval(let_expr.type_ann);
    
    // Check expression has that type
    check(ctx, let_expr.expr, ty);
    
    // Synthesize body type in extended context
    let value = eval(let_expr.expr);
    ctx.push(name, ty, value);
    let body_ty = synth(ctx, let_expr.body);
    ctx.pop();
    
    body_ty  // Type of let expression = type of body
}
```

**4. Conversion** - Structural comparison:
```rust
fn equate_let(lhs, rhs, ty) {
    type_equiv(lhs.ty, rhs.ty)?;
    equate(lhs.value, rhs.value, lhs.ty)?;
    
    let var = fresh_variable(lhs.ty);
    let lhs_body = run_closure(lhs.body, [var]);
    let rhs_body = run_closure(rhs.body, [var]);
    equate(lhs_body, rhs_body, ty)?;  // ty = body type
}
```

## Open Questions for Review

### Question 1: Body Type Tracking

When quoting a Let value, we need the body's type. Three options:

- **A**: Store `body_ty` in the Let value itself
- **B**: Re-synthesize during quotation (requires typechecker access)
- **C**: Pass body type as parameter to `quote`

**My recommendation:** Option C (pass as parameter)

**Your input needed:** Do you agree, or prefer A or B?

### Question 2: δ-Reduction Strategy

When should we unfold Let bindings during conversion checking?

- **Phase 1** (current plan): Never - only structural comparison
- **Phase 2** (future): Add fallback when comparing Let vs non-Let
- **Phase 3** (future): Full gluing with transparent unfolding

**My recommendation:** Start with Phase 1, add Phase 2 when needed

**Your input needed:** Is this incremental approach acceptable?

### Question 3: Environment Binding

Should we bind the value in the environment during body evaluation?

- **Option A**: No - keep value in Let structure, extend environment only when needed
- **Option B**: Yes - bind immediately for performance

**My recommendation:** Option A (cleaner, preserves structure)

**Your input needed:** Any performance concerns?

## Files to Modify

1. `crates/hwml-core/src/syn/basic.rs` - Add Let to Syntax ✓ (started)
2. `crates/hwml-core/src/val.rs` - Add Let to Value
3. `crates/hwml-core/src/eval.rs` - Implement eval_let
4. `crates/hwml-core/src/quote.rs` - Implement quote_let
5. `crates/hwml-core/src/check.rs` - Implement check_let
6. `crates/hwml-core/src/equal.rs` - Implement equate_let
7. `crates/hwml-core/src/syn/print.rs` - Implement print_let
8. `crates/hwml-core/src/syn/parse.rs` - Implement parse_let
9. `docs/src/core/overview.md` - Document Let expressions

## Next Steps (Pending Your Approval)

1. **Review this plan** - Confirm architectural approach
2. **Answer open questions** - Body type, δ-reduction, environment binding
3. **Implement Phase 1** - Core data structures (Syntax, Value)
4. **Implement Phase 2** - Evaluation and quotation
5. **Implement Phase 3** - Typechecking
6. **Implement Phase 4** - Conversion checking
7. **Implement Phase 5** - Printing and parsing
8. **Implement Phase 6** - Testing
9. **Update documentation** - Add Let to Core IR reference

## Success Criteria

- [ ] `quote(eval(let x : T = e; body))` preserves Let structure
- [ ] `let x : T = e; x` typechecks correctly
- [ ] Conversion checking works for identical Let bindings
- [ ] All existing tests pass
- [ ] New tests for Let expressions pass
- [ ] Documentation updated

## What I Need From You

1. **Architectural approval**: Is "Let as Value Constructor" acceptable, or do you want full gluing now?
2. **Answer open questions**: Body type tracking, δ-reduction strategy, environment binding
3. **Priority guidance**: Should I implement all phases, or stop after a certain point?
4. **Testing requirements**: Any specific test cases you want to see?

## Estimated Effort

- **Phase 1-4** (Core functionality): ~2-3 hours
- **Phase 5** (Printing/Parsing): ~1 hour  
- **Phase 6** (Testing): ~1-2 hours
- **Documentation**: ~30 minutes

**Total**: ~5-7 hours of implementation work

---

**Ready to proceed?** Please review and let me know:
1. Approve the approach, or suggest changes
2. Answer the open questions
3. Confirm which phases to implement

