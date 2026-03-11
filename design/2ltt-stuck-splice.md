Handling stuck splices is the "secret sauce" that allows your Two-Level Type Theory to manipulate **open code templates** (meta-functions that generate code but haven't received their arguments yet).

Without this, you could only generate code from fully closed static constants. With this, you can write high-level generators like `map`, `fold`, or parameterizable modules.

Here is the complete recipe for embedding neutrals.

### 1. The Core Concept: The "Escape Hatch"

You need to extend your **Object Syntax** (the AST) with a special constructor that says: *"I don't know what this part of the circuit is yet because it depends on a meta-variable `x` that hasn't been defined."*

We usually call this constructor `OEmbed` (Embed Neutral) or `OStuck`.

### 2. The Data Structures

You need three distinct types interacting here.

```haskell
-- 1. META VALUES (Standard NbE)
data Value 
  = VLam (Value -> Value)
  | VCode ObjectSyntax       -- A computed piece of hardware AST
  | VNeutral Neutral         -- A stuck meta-computation
  | ...

-- 2. NEUTRALS (Stuck Meta-Computations)
-- These represent computations blocked by a missing variable
data Neutral
  = NVar String              -- A meta-variable (e.g., function arg 'x')
  | NApp Neutral Value       -- A function call stuck on 'x'
  | NProj1 Neutral           -- Projection stuck on 'x'
  
-- 3. OBJECT SYNTAX (Extended with the Escape Hatch)
data ObjectSyntax
  = OVar String              -- A literal object wire name (e.g. "clk")
  | OAnd ObjectSyntax ObjectSyntax
  | OEmbed Neutral           -- <=== THE ESCAPE HATCH

```

### 3. The Implementation: `evalObject`

The logic handles the `Splice` case by checking if the result is a "clean" AST (`VCode`) or a "stuck" computation (`VNeutral`).

```haskell
evalObject :: Term -> Env -> ObjectSyntax
evalObject term env = case term of
  
  -- Standard Object Constructors
  ObjAnd t1 t2 -> OAnd (evalObject t1 env) (evalObject t2 env)
  
  -- The Splice (~t)
  Splice t -> 
    case eval t env of
      -- Case A: Success!
      -- The meta-computation finished and produced a Code value.
      -- We extract the inner AST and paste it here.
      VCode ast -> ast
      
      -- Case B: Stuck! (The Critical Fix)
      -- The meta-computation hit a neutral variable.
      -- Instead of erroring, we wrap it in OEmbed and return it 
      -- as a valid piece of syntax.
      VNeutral n -> OEmbed n
      
      -- Case C: Type Error
      _ -> error "Runtime Type Error: Splicing a non-Code value"

```

### 4. Tracing the "Identity Generator"

Let's see this in action with the simplest possible staged function: `\x. < ~x >`.

* **Goal:** A meta-function that takes a piece of code `x` and returns it.
* **Input:** We apply this function to a fresh Neutral variable `var_0`.

**Trace:**

1. **User defines:** `gen = \x -> < ~x >`
2. **NbE calls:** `eval (App gen (Neutral var_0))`
3. **Beta Reduction:** The body `< ~x >` is evaluated in environment `{ x: VNeutral (NVar "var_0") }`.
4. **Quote:** `eval` sees `< ... >`. It calls `evalObject (~x)`.
5. **Splice:** `evalObject` sees `~x`. It calls `eval(x)`.
6. **Lookup:** `eval(x)` returns `VNeutral (NVar "var_0")`.
7. **Embedding:** `evalObject` sees the Neutral. It returns `OEmbed (NVar "var_0")`.
8. **Result:** The final value is `VCode (OEmbed (NVar "var_0"))`.

We have successfully represented "Code containing a variable" without crashing!

### 5. Why is this useful? (Re-Splicing)

The magic happens when you **use** this result later.

Suppose you have the result from above: `res = VCode (OEmbed (NVar "var_0"))`.
Now you substitute `var_0` with actual code, say `< true >`.

In NbE, substitution is handled by the environment. If we re-evaluate that `OEmbed` node in a new environment where `var_0 = VCode OTrue`:

1. The evaluator encounters `OEmbed (NVar "var_0")`.
2. It looks up `var_0`.
3. It finds `VCode OTrue`.
4. It **dissolves** the `OEmbed` wrapper and replaces it with `OTrue`.

The "Hole" in the AST has been filled.

### 6. Readback (Displaying the term)

Finally, when you want to print the term back to the user (Readback), you need to handle `OEmbed`.

```haskell
readbackObject :: ObjectSyntax -> Term
readbackObject ast = case ast of
  OAnd a b -> ObjAnd (readbackObject a) (readbackObject b)
  
  -- Converting the stuck splice back to surface syntax
  OEmbed n -> Splice (readback n) 

```

So `VCode (OEmbed (NVar "x"))` reads back as the term `< ~x >`.

### Summary

* **Don't Error:** When a splice evaluates to a `VNeutral`, it's not a bug; it's a feature.
* **Wrap it:** Store the `Neutral` value inside your AST using `OEmbed`.
* **Unwrap it:** If that AST is ever re-evaluated in a context where the variable is defined, the `OEmbed` will naturally vanish (because `eval` will resolve the variable).

**Would you like to see how to handle "Cross-Stage Persistence" (Lifting `Lift`)?** (This is the opposite problem: using a meta-level `Int` inside object-level code).