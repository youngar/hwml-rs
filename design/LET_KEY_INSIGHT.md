# The Key Insight: Transparent Bindings

## The Problem

We need Let expressions that are:
1. **Preserved** - Structure survives eval/quote roundtrip
2. **Transparent** - Support definitional equality (let x = e; x ≡ e)

These seem contradictory:
- Preservation requires NOT substituting
- Transparency requires substituting

## The Solution: Transparent Bindings

The key insight is that we can have **both** by using a special kind of environment binding:

### During Evaluation

```rust
// When evaluating: let x : Nat = zero; succ x

// 1. Evaluate the bound expression
let value = eval(zero) = Value::DataConstructor(zero, [])

// 2. Push TRANSPARENT binding to environment
env.push_transparent("x", value)
//   This does TWO things:
//   - Adds x to local env as a VARIABLE (for structure preservation)
//   - Records that x is transparently bound to 'value' (for δ-reduction)

// 3. Evaluate body
eval(succ x)
  = eval(succ) applied to eval(x)
  = eval(x) looks up x in environment
  = Returns Value::Rigid(Variable(x))  ← PRESERVES STRUCTURE!
  = Result: Value::DataConstructor(succ, [Rigid(x)])

// 4. Return Let value with EVALUATED body
Value::Let {
    name: "x",
    ty: Nat,
    value: DataConstructor(zero, []),
    body: DataConstructor(succ, [Rigid(x)])  ← Body is EVALUATED but PRESERVES x!
}
```

**Key Point:** The variable `x` appears in the evaluated body as `Rigid(x)`, not substituted!

### During Quotation

```rust
// When quoting the Let value above:

quote(Value::Let { ... }, depth) {
    // Quote type: Nat → Syntax::Constant("Nat")
    // Quote value: DataConstructor(zero) → Syntax::Constant("zero")
    
    // Quote body: DataConstructor(succ, [Rigid(x)])
    //   Rigid(x) quotes to Variable(0)
    //   Result: Syntax::Application(Constant("succ"), Variable(0))
    
    // Reconstruct Let syntax
    Syntax::Let {
        name: "x",
        type_ann: Constant("Nat"),
        expr: Constant("zero"),
        body: Application(Constant("succ"), Variable(0))
    }
}
```

**Result:** Perfect structure preservation! ✅

### During Conversion Checking

```rust
// When checking: let y = f x; refl : Eq Nat (f x) y

// Expected type: Eq Nat (f x) y
// Synthesized type of refl: Eq Nat (f x) (f x)

// Conversion must prove: y ≡ f x

equate(Rigid(y), Application(f, x), Nat) {
    // Structural comparison fails: Rigid ≠ Application
    
    // ✅ δ-reduction fallback:
    // Look up y in transparent bindings
    // Find: y → Application(f, x)
    
    // Unfold and retry:
    equate(Application(f, x), Application(f, x), Nat)
    // ✓ Success!
}
```

**Result:** Transparency works! ✅

## The Magic: Two Faces of the Same Variable

A transparently-bound variable has **two faces**:

1. **Syntactic Face** (for preservation):
   - When evaluated, returns `Value::Rigid(var)`
   - When quoted, produces `Syntax::Variable(index)`
   - Structure is preserved!

2. **Semantic Face** (for transparency):
   - Stored in transparent environment
   - Used by conversion checker for δ-reduction
   - Definitional equality works!

## Comparison with Other Approaches

### Eager Substitution (REJECTED)
```rust
eval(let x = zero; succ x)
  = eval(succ zero)  ← x is substituted immediately
  = DataConstructor(succ, [zero])

quote(DataConstructor(succ, [zero]))
  = Application(succ, zero)  ← Let structure LOST!
```

### Full Glued Evaluation (FUTURE)
```rust
Value::Glued {
    rigid: Neutral::Var(x),      // Syntactic face
    semantic: Lazy(zero),         // Semantic face (lazy)
}
```
- More complex (requires Lazy evaluation)
- More elegant (built into Value representation)
- Can upgrade to this later if needed

### Transparent Bindings (CHOSEN)
```rust
// Variable in environment: Rigid(x)
// Transparent binding: x → zero
```
- Simpler (no Lazy, no dual representation)
- Pragmatic (achieves both goals)
- Follows existing patterns

## Implementation Checklist

To make this work, we need:

1. ✅ **TransparentEnv** - Track Let bindings separately
2. ✅ **push_transparent()** - Add binding during evaluation
3. ✅ **lookup_transparent()** - Query binding during conversion
4. ✅ **Value::Let with evaluated body** - Store `Rc<Value>`, not `Closure`
5. ✅ **δ-reduction in equate()** - Unfold transparent bindings when structural equality fails

## Why This Works

**Preservation:**
- Variables evaluate to `Rigid(var)` (not substituted)
- Body is fully evaluated but contains variables
- Quotation reconstructs Let syntax perfectly

**Transparency:**
- Transparent bindings track the semantic meaning
- Conversion checker can unfold when needed
- Definitional equality works correctly

**NbE Compliance:**
- All Values are fully evaluated (no Closures in Let)
- Evaluation and quotation are properly separated
- Type-directed quotation works as expected

## The Bottom Line

**Transparent bindings give us the best of both worlds:**
- Structure preservation (like not substituting)
- Definitional equality (like substituting)
- Without the complexity of full glued evaluation

This is the **pragmatic middle-ground** that makes Let expressions work correctly in a dependently-typed NbE system!

