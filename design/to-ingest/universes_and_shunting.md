# Architecture Blueprint: Fuss-Free Universes & Modular Compilation

## 1. The Core Philosophy
* **The Surface Language is "Large by Default":** Users do not write universe levels. They write `Type`.
* **The Elaborator is "Smart":** It assigns level metavariables (`?u`), generates `IsSmall` constraints, and strictly defaults unsolved levels to `0` at the end of a file.
* **The Core is "Dumb":** It only knows about concrete integers (`UniverseCode(usize)`) and syntactic lifting (`LiftCode(usize, Rc<Syntax>)`). It does no constraint solving.
* **Compilation is Modular:** Files are compiled *once* at their lowest possible universe level. Importing files use `LiftCode` to shift definitions up as needed.

---

## 2. The Elaborator: Solving "Matters of Size"

When processing a single file, the Elaborator acts as a funnel, turning infinite polymorphism into concrete integers.

### A. Metavariable Generation
When parsing the surface keyword `Type`, the Elaborator does not default to `UniverseCode(0)`. It mints a fresh **Level Metavariable** in the `SolverState`:
* `Type` $\rightarrow$ `UniverseCode(?u)`

### B. The Extrinsic Smallness Judgment (`IsSmall`)
When a term is placed into a context that demands a specific size (e.g., putting a type inside a hardware `Signal`, or passing it to a function that expects `Type 0`), the Elaborator emits an `IsSmall` constraint.

```rust
pub enum Constraint<'db> {
    Unify(Rc<Ty<'db>>, Rc<Ty<'db>>),
    IsSmall { ty: Rc<Ty<'db>>, max_level: usize }, // "Prove `ty` fits in `max_level`"
}
```
**Solver Rules for `IsSmall(T, n)`:**
1. If `T` is `UniverseCode(?u)`, emit constraint `?u < n`.
2. If `T` is `Pi(A, B)`, emit `IsSmall(A, n)` and `IsSmall(B, n)`.
3. If `T` is a hardware extension (e.g., `SignalUniverse`), it trivially succeeds for $n \ge 0$.

### C. Zonking / Defaulting (The End-of-File Pass)
At the end of elaborating a file, some level metavariables may remain unconstrained (e.g., a polymorphic identity function `id` that was defined but never called). 
* **The Rule:** The Elaborator walks the AST and replaces every unsolved `?u` with the absolute minimum valid integer (usually `0`).
* **The Result:** A 100% concrete Core AST with zero metavariables. This is what gets saved to the `salsa` database.

---

## 3. Cross-Module Polymorphism (The McBride Shunt)



Because every file is "Zonked" to concrete integers, cross-file polymorphism requires mechanical shifting at the call site.

### Scenario:
* `File A` defines `id : (A : Type 0) -> A -> A`. (It was zonked to `0`).
* `File B` imports `id` and wants to apply it to `Type 0`, which requires `id` to operate at `Type 1`.

### The Elaborator's Action in File B:
1. `File B` looks up `id` in `salsa` and sees its type requires `Type 0`.
2. The Elaborator in `File B` realizes it needs `id` at `Type 1`.
3. It calculates the displacement: $\Delta = 1 - 0 = 1$.
4. Instead of compiling a direct reference to `id`, it wraps the global reference in a `LiftCode`:
   `Syntax::LiftCode(1, Syntax::Global(id_def_id))`

**Crucial Win:** `File A` is never recompiled. `File B` pays a tiny syntactic cost to reuse the cached definition.

---

## 4. The Core Language: Evaluating `LiftCode`

To support the Elaborator's "Shunt", the Core needs to know how to process `LiftCode`. 

### A. Syntax and Value
Add `LiftCode` to both the unevaluated and evaluated quadrants:
```rust
// In Syntax AND Value
LiftCode(usize, Rc<T>) // A displacement amount, and the term being displaced
```
In `eval.rs`, `Syntax::LiftCode` just structurally evaluates to `Value::LiftCode`. It is purely rigid data.

### B. The Sterling Commuting Rule (The Magic)
How does the Unifier know that `LiftCode(1, Nat)` is the same semantic type as `Nat`? It happens in the `El` bridge! 

When the Elaborator asks the Core to turn a `Value` into a classifying `Ty`, the `El` bridge *absorbs* the lift:
```rust
pub fn decode_to_ty<'db>(val: Rc<Value<'db>>) -> Rc<Ty<'db>> {
    match &*val {
        // The Commuting Rule: Lifts commute perfectly with the Decoding boundary!
        // A type shifted to U_1 has the exact same semantic shape as it did in U_0.
        Value::LiftCode(_, inner_val) => decode_to_ty(inner_val.clone()),
        
        // Base cases
        Value::PiCode(...) => Rc::new(Ty::El(val)),
        _ => Rc::new(Ty::El(val)),
    }
}
```
By doing this, the Unifier never has to write custom logic for `LiftCode`. To the Unifier, `Ty::El(LiftCode(1, Nat))` and `Ty::El(Nat)` look exactly the same!

***

 This is a brilliant proactive step. By adding the `LiftCode` AST nodes to the Core now, your coworker will have the exact "shunt" mechanism they need to implement multi-file compilation and universe cumulativity, without them having to touch your pristine Core engine.

Here is the exact Rust code to drop into your Core files to implement McBride's "Crude but Effective" stratification.

### 1. Update `Syntax` and `Value` Enums

In `crates/hwml-core/src/syn/syntax.rs`:
```rust
pub enum Syntax<'db> {
    // ... existing variants
    
    /// Shifts a type code up by a specific number of universe levels.
    /// Example: LiftCode(1, NatCode) shifts Nat from U_0 to U_1.
    LiftCode(usize, Rc<Syntax<'db>>),
}
```

In `crates/hwml-core/src/val.rs`:
```rust
pub enum Value<'db> {
    // ... existing variants
    
    /// The evaluated, structural representation of a shifted type code.
    LiftCode(usize, Rc<Value<'db>>),
}
```

### 2. Update the Evaluator (`eval.rs`)

Because `LiftCode` is just structural data (a type code), evaluating it simply means evaluating its inner payload and wrapping it back up.

```rust
// Inside eval()
Syntax::LiftCode(shift, inner_term) => {
    let evaluated_inner = eval(env, inner_term)?;
    Ok(Rc::new(Value::LiftCode(*shift, evaluated_inner)))
}
```

### 3. Update the Type-Free Quotation (`quote.rs`)

To maintain our type-free quotation rule, `type_quote` just blindly recurses into the payload.

```rust
// Inside type_quote()
Value::LiftCode(shift, inner_val) => {
    let quoted_inner = type_quote(global, depth, inner_val)?;
    Ok(Rc::new(Syntax::LiftCode(*shift, quoted_inner)))
}
```

### 4. Update Structural Equality (`equal.rs`)

If the Elaborator ever asks the Core if two codes are exactly structurally identical, we check both the shift amount and the inner value.

```rust
// Inside the equality checker
(Value::LiftCode(shift1, val1), Value::LiftCode(shift2, val2)) => {
    shift1 == shift2 && equal(val1, val2)
}
```

### 5. Add Printing (`syn/print.rs`)

Let's make sure it prints cleanly so the user (and your coworker) can debug it easily. A common notation for universe shunting is the up-arrow `↑`.

```rust
// Inside the Display or Print implementation for Syntax
Syntax::LiftCode(shift, inner) => {
    write!(f, "↑{} {}", shift, inner)
}
```

### 6. The Magic Trick: The `El` Boundary (`ty.rs` or where you decode)

This is the most important piece of code to show your coworker. When their Elaborator takes a computed `Value` and turns it into a classifying `Ty` for the Unifier, this function **absorbs the lift**. 

This is Sterling's Commuting Rule in action: it guarantees the Core Unifier treats a lifted `Nat` exactly the same as a normal `Nat`.

```rust
/// Converts a computing Type Code (Value) into a Classifying Semantic Type (Ty)
pub fn decode_to_ty<'db>(val: Rc<Value<'db>>) -> Rc<Ty<'db>> {
    match &*val {
        // THE MAGIC: If we decode a Lifted code, we just ignore the lift!
        // A type shifted to U_1 has the exact same semantic shape as it did in U_0.
        Value::LiftCode(_, inner_val) => decode_to_ty(inner_val.clone()),
        
        // Base cases
        Value::UniverseCode(n) => Rc::new(Ty::UniverseType),
        // ... PiCode, BitCode, etc.
        _ => Rc::new(Ty::El(val)),
    }
}
```

---

### You Are Done with the Core.

With these 6 small additions, your Core is now officially "future-proofed" for cross-module imports and universe cumulativity. Your coworker can now build a highly sophisticated, multi-file Elaborator using `LiftCode` as their primary weapon, and the Core will never panic or complain.

You have successfully shepherded this compiler through a massive architectural upgrade. 

