Cross-Stage Persistence (CSP) allows you to use a **computed meta-value** (like a calculated integer or boolean) as a **constant** in your object code.

Without CSP, you can rearrange wires, but you can't "bake in" configuration values calculated at compile time.

### 1. The Concept: CSP vs. Splice

It is crucial to distinguish these two operations, as they are often confused:

* **Splice (`~t`)**: `t` is *already* Code (an AST). You are pasting that AST into a larger AST.
* **Lift / CSP (`%t`)**: `t` is a **Value** (e.g., `Int`, `Bool`). You are converting that value into a **Literal AST node** (e.g., `OInt 5`).

### 2. Implementation Steps

To support `lift` (often denoted `%` in surface syntax), you need to extend your evaluator to handle the conversion from **Semantic Values** to **Syntactic Literals**.

#### Step A: Extend the Object Syntax

Your AST needs to represent literals and "stuck lifts."

```haskell
data ObjectSyntax
  = OVar String
  | OBit Bool               -- Literal: High/Low
  | OInt Int                -- Literal: 32-bit integer constant
  -- ... existing constructors ...
  | OEmbed Neutral          -- Stuck Splice (~x)
  | OLift Neutral           -- Stuck Lift (%x) <--- NEW

```

*Note: You can reuse `OEmbed` for stuck lifts if you are careful, but having a distinct `OLift` constructor makes Readback (pretty-printing) much more accurate.*

#### Step B: Extend the Evaluator (`evalObject`)

You need a new case in your `evalObject` function to handle the `%` operator.

```haskell
evalObject :: Term -> Env -> ObjectSyntax
evalObject term env = case term of
  
  -- ... existing cases (Splice, ObjAnd, etc.) ...

  -- === Cross-Stage Persistence (%t) ===
  Lift t ->
    case eval t env of
      -- 1. It evaluated to a concrete constant
      VBool b -> OBit b
      VInt i  -> OInt i
      
      -- 2. It got stuck! (Neutral)
      -- We are trying to lift a variable, e.g., < %x >
      -- We can't generate the hardware constant yet.
      VNeutral n -> OLift n
      
      -- 3. Error
      _ -> error "CSP Error: Can only lift base types (Int/Bool) into hardware!"

```

### 3. Example: Parameterized HardwareUniverse Generation

Let's look at a concrete example of how this enables powerful hardware generators.

**Scenario:** We want a function `pulse_generator` that takes a meta-level integer `n` and generates hardware that checks if a counter equals that constant `n`.

**Meta-Code:**

```haskell
let pulse_generator = \n -> 
  -- We are inside a Quote < ... >
  -- We use %n to bake the value of n into the circuit
  < input_signal == %n >

```

**Execution Trace:**

1. **User calls:** `pulse_generator 5`
* `eval` binds `n` to `VInt 5`.
* Enters the quote `< ... >`.
* Calls `evalObject(input_signal == %n)`.


2. **Evaluating `%n`:**
* `evalObject` sees `Lift (Var "n")`.
* Calls `eval("n")` -> returns `VInt 5`.
* Matches `VInt i`. Returns AST node `OInt 5`.


3. **Resulting AST:**
`OEq (OVar "input_signal") (OInt 5)`

The hardware is now hardcoded to check against 5.

### 4. Handling Stuck Lifts (The "Opaque" Constant)

What if we partially apply the function?

**Meta-Code:**

```haskell
let check_x = \x -> < input == %x >

```

**Trace:**

1. `eval` binds `x` to `VNeutral (NVar "var_0")`.
2. `evalObject` sees `%x`.
3. Calls `eval("x")` -> returns `VNeutral`.
4. Matches `VNeutral`. Returns `OLift (NVar "var_0")`.

**Resulting AST:**
`OEq (OVar "input") (OLift (NVar "var_0"))`

This represents a valid piece of hardware syntax that contains a "hole" waiting for a meta-integer. If you later substitute `x` with `10`, the `OLift` node will dissolve into `OInt 10`.

### Summary of the 2LTT Architecture

We have built a complete Staged NbE pipeline. Here is the final cheat sheet for how the pieces fit together:

| Concept | Surface Syntax | Semantic Action | AST Representation |
| --- | --- | --- | --- |
| **Object Term** | `NOT x` | Reconstruct | `ONot (OVar "x")` |
| **Splice** | `~x` | `eval` -> Unwrap Code | `Code`  `AST` |
| **Stuck Splice** | `~x` (x is neutral) | Embed Neutral | `OEmbed neutral` |
| **Lift (CSP)** | `%x` | `eval` -> Make Literal | `Int`  `OInt 5` |
| **Stuck Lift** | `%x` (x is neutral) | Embed Neutral | `OLift neutral` |

### A Next Step for You

You now have a system that supports uninterpreted terms, quoting, splicing, and lifting.

The logical next step is **Type Inference for the Object Language**. Since your object terms are just "data," you can easily write a function `infer :: ObjectSyntax -> Maybe ObjectType` in your meta-language.

**Would you like to see how to implement the `infer` function to ensure the hardware you generated is actually valid (e.g., checking bit-widths)?**