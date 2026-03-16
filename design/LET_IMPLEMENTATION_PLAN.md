# Let Expression Implementation Plan

## Overview

This document outlines the plan to add `let` expressions to the hwml-rust Core IR, following the formal specification provided in the research document.

## Goals

1. **Preserve Let structure** through evaluation and quotation (no eager substitution)
2. **Enable definitional equality** through δ-reduction in conversion checking
3. **Maintain bidirectional typechecking** with explicit type annotations
4. **Follow existing architectural patterns** in the codebase

## Non-Goals (for initial implementation)

- Full glued evaluation (can be added later if needed)
- Lazy evaluation of let bindings
- Let-polymorphism or generalization
- Surface-level let syntax (this is Core IR only)

## Architecture Decision: Simplified Approach

Instead of implementing full glued evaluation immediately, we'll use a **simpler approach**:

1. **Syntax**: `Let { name, type_ann, expr, body }`
2. **Value**: `Let { name, ty, value, body }` - preserves structure
3. **Evaluation**: Evaluate `expr` to `value`, then evaluate `body` with `value` in environment
4. **Quotation**: Quote back to `Let` syntax, preserving structure
5. **Conversion**: Compare Let bindings structurally, with δ-reduction fallback

This avoids the complexity of gluing while still preserving Let structure for readback.

## Implementation Phases

### Phase 1: Core Data Structures ✓ (Started)

**Files to modify:**
- `crates/hwml-core/src/syn/basic.rs` - Add `Let` variant to `Syntax` enum ✓
- `crates/hwml-core/src/val.rs` - Add `Let` variant to `Value` enum

**Syntax Structure:**
```rust
pub struct Let<'db> {
    pub name: String,           // Variable name (for printing)
    pub type_ann: RcSyntax<'db>, // Explicit type annotation
    pub expr: RcSyntax<'db>,     // The bound expression
    pub body: RcSyntax<'db>,     // The body (uses de Bruijn index 0)
}
```

**Value Structure:**
```rust
pub struct Let<'db> {
    pub name: String,           // Variable name (for printing)
    pub ty: RcValue<'db>,     // Evaluated type
    pub value: RcValue<'db>,  // Evaluated expression
    pub body: Closure<'db>,     // Body as closure
}
```

### Phase 2: Evaluation

**Files to modify:**
- `crates/hwml-core/src/eval.rs`

**Implementation:**
```rust
fn eval_let<'db, 'g>(
    env: &mut Environment<'db, 'g>,
    let_expr: &syn::Let<'db>,
) -> Result<RcValue<'db>, Error> {
    // 1. Evaluate type annotation
    let ty = eval(env, &let_expr.type_ann)?;
    
    // 2. Evaluate the bound expression
    let value = eval(env, &let_expr.expr)?;
    
    // 3. Create closure for body
    let body = Closure::new(env.local.clone(), let_expr.body.clone());
    
    // 4. Return Let value (preserves structure)
    Ok(Rc::new(Value::Let(val::Let {
        name: let_expr.name.clone(),
        ty,
        value,
        body,
    })))
}
```

**Key Decision**: We preserve the Let structure in the semantic domain rather than eagerly substituting.

### Phase 3: Quotation

**Files to modify:**
- `crates/hwml-core/src/quote.rs`

**Implementation Strategy:**
- Quote Let values back to Let syntax
- Recursively quote type, value, and body
- Preserve variable names for readability

### Phase 4: Typechecking

**Files to modify:**
- `crates/hwml-core/src/check.rs`

**Typing Rule (Synth mode):**
```
Γ ⊢ type_ann ⇐ Type
A = eval(type_ann)
Γ ⊢ expr ⇐ A
Γ, x : A ⊢ body ⇒ B
─────────────────────────
Γ ⊢ let x : type_ann = expr; body ⇒ B
```

**Implementation:**
1. Check `type_ann` is a type
2. Evaluate `type_ann` to get `A`
3. Check `expr` against `A`
4. Extend context with `x : A` (binding the evaluated value)
5. Synthesize type of `body`
6. Return synthesized type

### Phase 5: Conversion Checking

**Files to modify:**
- `crates/hwml-core/src/equal.rs`

**Strategy:**
- Add `equate_let` function
- Compare Let bindings structurally
- For now, no δ-reduction (can add later if needed)

**Implementation:**
```rust
pub fn equate_let<'db>(
    global: &GlobalEnv<'db>,
    depth: usize,
    lhs: &val::Let<'db>,
    rhs: &val::Let<'db>,
) -> Result<'db> {
    // Compare types
    type_equiv(global, depth, &lhs.ty, &rhs.ty)?;
    
    // Compare bound values
    equate(global, depth, &lhs.value, &rhs.value, &lhs.ty)?;
    
    // Compare bodies (eta-expand with fresh variable)
    let var = Rc::new(Value::variable(Level::new(depth), lhs.ty.clone()));
    let lhs_body = run_closure(global, &lhs.body, [var.clone()])?;
    let rhs_body = run_closure(global, &rhs.body, [var])?;
    
    // Body type is unknown here - we'd need to track it
    // For now, use structural comparison
    // TODO: Determine correct type for body comparison
    
    Ok(())
}
```

### Phase 6: Printing

**Files to modify:**
- `crates/hwml-core/src/syn/print.rs`

**Syntax:** `let %name : type = expr; body`

### Phase 7: Parsing

**Files to modify:**
- `crates/hwml-core/src/syn/parse.rs`

**Grammar:** `"let" identifier ":" expr "=" expr ";" expr`

### Phase 8: Testing

**Files to create/modify:**
- Add tests in `crates/hwml-core/src/` test modules

**Test cases:**
1. Basic let binding: `let x : Nat = zero; x`
2. Let with dependent types
3. Nested let bindings
4. Let in function bodies
5. Conversion checking with let
6. Quotation preserves let structure

## Open Questions

1. **Body type tracking**: How do we determine the type of the body for conversion checking?
   - Option A: Store body type in Let value
   - Option B: Re-synthesize during conversion
   - Option C: Use untyped structural comparison (current plan)

2. **δ-reduction**: When should we unfold Let bindings during conversion?
   - Current plan: Never (structural comparison only)
   - Future: Add when comparing Let against non-Let values

3. **Environment binding**: Should we bind the value in the environment during evaluation?
   - Current plan: No, preserve in closure
   - Alternative: Yes, for better performance (but loses structure)

## Success Criteria

- [ ] Let expressions parse correctly
- [ ] Let expressions typecheck according to the formal rule
- [ ] Let structure is preserved through eval/quote roundtrip
- [ ] Conversion checking works for identical Let bindings
- [ ] All existing tests still pass
- [ ] New tests for Let expressions pass

## Future Enhancements

1. **Glued Evaluation**: Implement full gluing for better δ-reduction
2. **Performance**: Optimize Let evaluation with environment binding
3. **Pretty Printing**: Improve output formatting for nested Lets
4. **Surface Syntax**: Add surface-level let syntax in elaborator

