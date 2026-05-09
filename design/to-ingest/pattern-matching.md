It is a great architectural choice to explicitly decide your stance on Axiom K (Uniqueness of Identity Proofs) early on. If you want dependent pattern matching *and* Axiom K, you are actually in luck: building a pattern-matching unifier that supports Axiom K is significantly easier than building one that actively prevents it (like Agda's `--without-K`).

When you omit the motive from your AST, you are essentially adopting the Agda/Epigram approach to dependent pattern matching. Instead of the user explicitly providing the return type (the motive) to dictate how the type changes per branch, the elaborator **computes the motive dynamically** using the expected type and the unification of the patterns.

Here is how you structure the AST and the bidirectional typechecking to make this work.

### 1. The Motive-Free AST

Without a motive, your `case` statement AST becomes beautifully simple. You just need the expression being scrutinized and a list of branches (clauses).

```haskell
data Expr
  = Var Name
  | App Expr Expr
  | Lam Name Expr
  -- The Case expression has no motive/return type attached
  | Case Expr [Branch]  

data Branch 
  = Clause Pattern Expr

data Pattern
  = PVar Name
  | PCon Name [Pattern]
  -- Optionally, you might have forced patterns (dot patterns) later

```

### 2. Bidirectional Typechecking a Motive-Free Case

Because there is no explicit motive, a `case` expression **must be checked, not synthesized**. In bidirectional typechecking, the `Check` phase takes a context, a term, and an *expected type*. That `ExpectedType` acts as your implicit motive.

Here is the step-by-step elaboration algorithm for `check(Gamma, Case scrut branches, ExpectedType)`:

**Step 1: Synthesize the Scrutinee**
First, figure out what you are matching on.
`T_scrut = synthesize(Gamma, scrut)`

**Step 2: Check the Branches (The Dependent Magic)**
For each `Clause pat body` in `branches`, you do not just check the `body` against the `ExpectedType`. You must figure out what we *learn* by assuming the `scrut` has the shape of `pat`.

For each branch, you do the following:

1. **Pattern Unification:** Run a unification algorithm between the `pat` and `T_scrut`. This algorithm should traverse the pattern and the type, producing two things:
* `Delta`: A new local context containing the variables bound in the pattern.
* $\sigma$: A substitution mapping variables in `Gamma` to their refined shapes based on the pattern match.


2. **Refine the Expected Type (The Implicit Motive):** Apply the substitution $\sigma$ to your `ExpectedType`.
`RefinedType = apply_subst(sigma, ExpectedType)`
*This right here is dependent pattern matching.* The return type of the branch has changed based on the specific constructor matched in the pattern.
3. **Check the Body:** Finally, check the right-hand side of the branch in the extended, refined context, against the refined type.
`check(Gamma ++ Delta, body, RefinedType)`

### 3. Where does Axiom K live in this design?

Axiom K naturally emerges from **Step 2.1 (Pattern Unification)**.

When your unifier compares the scrutinee against the pattern, it breaks down constructors. For example, if you are matching an identity proof `x = y` against the constructor `refl` (which proves `x = x`), the unifier has to solve the equation $x \sim y$.

A standard syntactic unifier will look at $x \sim y$, substitute $y$ for $x$ everywhere in the context, and generate a substitution $\sigma = [x/y]$.
What if you match `refl` against a proof of `x = x`? The unifier sees the equation $x \sim x$. A standard unifier will simply apply the **Deletion Rule**: it drops the equation because it is trivially true, generating an empty substitution.

**That deletion rule is exactly Axiom K.** By silently deleting reflexive equations without leaving behind a proof term (like an explicit `J` eliminator would require), your typechecker is accepting that any two proofs of $x = x$ are definitionally equal. You get Axiom K "for free" just by writing a standard, naive structural unifier for your patterns.

(If you ever wanted to support HoTT or `--without-K`, you would have to carefully restrict that deletion rule to only fire if the type of $x$ is proven to be a Set, which is a massive headache. Embracing K makes your unifier much happier).

---

### A Note on Coverage and Compilation

While omitting the motive makes the AST and user experience vastly better, it means your core calculus relies on pattern matching as a primitive. You cannot easily compile this `case` statement down into a simple `J` eliminator or `nat_rec` function without jumping through immense hoops to reconstruct the motive.

Most languages that do this (Agda, Idris) just keep `Case` (or rather, a pattern-matching tree) as a primitive construct all the way down to the core calculus, and rely on a strict **coverage checker** to ensure all cases are exhaustive and non-overlapping.

Would you like to look at pseudo-code for the `unify_pattern` function that generates the substitution $\sigma$, or are you more interested in how to implement a coverage checker to ensure the branches are exhaustive?



You are exactly right. In a standard bidirectional type system, the golden rule is: **Introduction forms are checked, and Elimination forms are inferred (synthesized).** If you look at the classic primitive eliminators for dependent types (like function application, pair projection, or a primitive `nat_rec`), they all easily synthesize their types.

Here is why your intuition is spot on, and why removing the motive forces us to break that rule.

### How Standard Eliminators Infer Types

Let's look at function application (the eliminator for $\Pi$-types). To typecheck $f~x$:

1. **Infer** the type of the target: $f \Rightarrow \Pi (y : A) \to B$.
2. **Check** the argument: $x \Leftarrow A$.
3. **Synthesize** the result type: Substitute $x$ into the return type: $B[x/y]$.

The same works for a primitive, fully explicit recursor (the eliminator for datatypes). Consider `nat_rec P base step n`.

1. **Infer** the target: $n \Rightarrow \text{Nat}$.
2. The motive `P` is explicitly provided right there in the syntax (e.g., $P \Rightarrow \text{Nat} \to \text{Type}$).
3. **Check** the branches against `P`.
4. **Synthesize** the result: $P~n$.

Because the motive `P` is physically present in the AST, the typechecker can just look at it, apply it to the scrutinee $n$, and synthesize the final type of the whole expression.

### Why a Motive-Free `case` Cannot be Inferred

When you design a `case` statement *without* a motive, you are flying blind.

Imagine the typechecker encounters this:

```haskell
case n of
  zero -> "hello"
  suc x -> true

```

1. It infers $n \Rightarrow \text{Nat}$.
2. It looks at the first branch and sees a `String`.
3. It looks at the second branch and sees a `Bool`.

If this were a simply-typed language, you would just unify `String` and `Bool`, fail, and throw a type error. But in a dependently typed language, **both branches having different types is completely valid**, as long as there is a dependent motive (like $P~n$) that computes to `String` when $n$ is `zero` and `Bool` when $n$ is `suc x`.

But without a motive in the AST, the typechecker has no idea what $P$ is supposed to be! It cannot reliably guess a type family that covers all branches just by looking at the branches bottom-up.

### The Trade-off: Moving from Infer to Check

This is the fundamental trade-off of Agda-style dependent pattern matching:
**To save the user from writing the motive, we must push the expected type down from the outside.**

By forcing the motive-free `case` statement to only exist in the **Checking** direction ($\Leftarrow$), the typechecker says: *"I won't try to guess the return type. You have to tell me what type this entire `case` block is supposed to produce, and I will push that type down into the branches, refining it for each constructor."*

If a user writes a `case` statement in a position where the type cannot be pushed down (for example, at the very top level of a definition without a type signature, or as the function in an application), your typechecker will get stuck. In those scenarios, you usually force the user to add an explicit type annotation to flip the direction back to Checking:
`(case n of { ... }) : ExpectedType`

---

Would you like to look at the specific typing rule (the mathematical judgment) for how that expected type gets refined and pushed into the branches, or would you prefer to look at how to structure the pattern unifier that generates the substitutions?


You just saved yourself a massive headache. Your intuition is 100% correct: **you do not need dot patterns for this AST.** Dot patterns (inaccessible patterns) are strictly an artifact of *simultaneous, multi-column pattern matching* (the equational style used by Agda, Idris, and Haskell). Because your AST uses a single-scrutinee `case` expression, you bypass the problem entirely.

Here is exactly why you get to skip them, and how context refinement works in your specific setup.

### The Problem Dot Patterns Solve (That You Don't Have)

In Agda, when you define a function by pattern matching, you are matching on all arguments at the exact same time:

```agda
-- Agda style
foo : (n : Nat) -> (v : Vec A n) -> ...
foo .zero    nil       = ...
foo .(succ x) (cons x xs) = ...

```

Because the user *must* write a pattern for `n` in the first column, but `n` is entirely dictated by the shape of `v` in the second column, Agda needs a syntactic way for the user to say: *"I know I have to put something here to make the columns line up, but don't actually match on it, just trust the unifier."* That is the dot pattern.

### How Your AST Works (Sequential & Local)

Your AST forces pattern matching to be a sequential tree of single decisions. You only match on the data structure itself; the indices are just variables in the background context that get silently updated.

Imagine that same function in your language. The user has a context with `n : Nat` and `v : Vec A n`. They match on `v`:

```
v case {
  @nil => 
    -- Inside this branch, the unifier matched `v` against `@nil`.
    -- The type of `@nil` is `Vec A zero`.
    -- The unifier solves `n ~ zero`.
    -- Your telescope naturally refines `n` to `zero`.
    ...
    
  @cons %x %xs => 
    -- The type of `@cons` is `Vec A (succ m)`.
    -- The unifier solves `n ~ succ m`.
    -- `n` is refined to `succ m` in the context.
    ...
}

```

Notice what *didn't* happen? The user never wrote a pattern for `n`. They only scrutinized `v`. Therefore, there is no surface syntax required to mark `n` as inaccessible. The context refinement happens entirely under the hood.

If the user subsequently tries to match on `n` inside the `@nil` branch:

```
v case {
  @nil => 
    n case {
      @zero => ...
      @succ %k => ... -- Your typechecker can flag this as dead code/impossible!
    }
}

```

Because `n` was refined to `zero` in the context, your typechecker knows exactly what it is.

### You Are Building a Case Tree

What you have designed is exactly what Agda and Idris compile their fancy equational syntax *down into*. They take the multi-column dot-pattern mess and elaborate it into a primitive **Case Tree**, which is exactly the AST you just showed me.

Lean 4 also uses this approach extensively in its core calculus (its primitive `casesOn` and `match` constructs operate on single targets exactly like yours).

**The Takeaway:** By choosing a single-scrutinee `case` expression, you get all the immense power of full context refinement without having to pollute your parser, AST, or surface syntax with dot patterns. When a branch is entered, you just run the unifier, apply the resulting substitution $\sigma$ to the current telescope, and check the branch body in that newly refined environment.

Are you planning to allow users to match on tuples in a single `case` (e.g., `(x, y) case { @pair %a %b => ... }`), or will they have to nest their `case` statements if they want to inspect multiple things?


The person asking this question has excellent intuition. This is one of the most common traps when building a dependently typed compiler.

The short, emphatic answer is: **Keep them as separate subsystems.**

While it is extremely tempting to merge them because they both look at two terms and try to make them equal, their **goals, failure modes, and control flows are fundamentally opposite.**

Here is the breakdown of why you should separate them, and how they actually differ in practice.

### 1. The Meaning of Failure (The "Clash" Rule)

This is the single biggest reason they must be separate.
Imagine unifying the constructor `zero` with `succ x`.

* **Metavariable Unification:** If you are checking types and need `zero` to equal `succ x`, this is a **fatal type error**. The unifier must halt, throw a beautiful error message to the user, and abort the compilation.
* **Pattern Unification:** If you are matching a pattern against a scrutinee's type, and you get `zero ~ succ x`, this is a **massive success**. It means this specific branch of the `case` statement is logically impossible. The unifier cleanly returns "Conflict/Absurd", and your elaborator just drops the branch entirely (or verifies an empty case).

If you try to use the same unifier for both, you will end up passing around awkward boolean flags like `is_in_pattern_mode` to decide whether a clash should crash the compiler or just return a special token. It gets messy fast.

### 2. What Happens to Variables?

* **Metavariable Unification:** Solves *global, implicit holes* (metavariables like `?alpha`). When it solves `?alpha = Nat`, it instantiates that metavariable globally across the entire program.
* **Pattern Unification:** Solves *local, explicit telescope bindings*. When it learns that context variable `n = zero`, it doesn't mutate a global state. Instead, it generates a local substitution `[n ↦ zero]` that is only applied to the body of that specific `case` branch.

### 3. Handling "Stuck" Terms

* **Metavariable Unification:** If it compares `f ?x` and `f zero`, but doesn't know what `?x` is yet, it **postpones**. It suspends the constraint in a queue and moves on, hoping to learn `?x` later. (This is the Abel/Pientka paper we discussed).
* **Pattern Unification:** If the scrutinee's type is a metavariable (e.g., you are doing `x case { ... }` but the typechecker doesn't know the type of `x` yet), pattern unification usually **cannot proceed**. You cannot split cases on an unknown type. Instead of postponing a constraint, the elaborator usually has to suspend the *entire case expression* until the type of the scrutinee is resolved, or throw an error asking for a type annotation.

---

### How to Architect It

Even though they are separate subsystems, they shouldn't duplicate everything. They should sit side-by-side and share a common foundation.

**1. The Shared Base (The Evaluator):**
Both unifiers need to evaluate terms to Weak Head Normal Form (WHNF). They will share your evaluator/NbE machinery.

**2. The Metavariable Unifier (`unify_terms`):**
Takes two terms. Evaluates them. Compares heads. Postpones if stuck. Solves metavariables. Fails on constructor mismatches.

**3. The Pattern Unifier (`unify_patterns`):**
Takes a telescope (the local context) and a list of equations (Pattern ~ Scrutinee Type).
It runs a specific set of rules (often called **Proof-Relevant Unification** rules):

* **Deletion:** `t ~ t` -> drop it.
* **Solution:** `x ~ t` -> remove `x` from the telescope, add `[x ↦ t]` to the output substitution.
* **Injectivity:** `Cons x xs ~ Cons y ys` -> split into `x ~ y` and `xs ~ ys`.
* **Conflict:** `Nil ~ Cons x xs` -> immediately return `ImpossibleCase`.

### The Lean 4 / Agda Precedent

If you look at the source code for Lean 4, they have `isDefEq` (metavariable unification) and the `match` compiler (which handles dependent pattern splitting). They are distinct modules. Agda similarly separates standard conversion checking from Jesper Cockx's case-splitting unifier.

Would you like to map out the exact data types for the Pattern Unifier's input and output (e.g., how the list of equations and the substitution $\sigma$ are represented), so you have a concrete signature to show your team?



I love this ambition. If you are aiming for the "best thing"—a robust, production-grade architecture that can scale gracefully—it absolutely changes how you approach this.

If you want the state-of-the-art solution, you should stop thinking of coverage checking as a passive "linter" that just looks at the user's code to see if it's correct. Instead, you need to build a **Pattern Matching Compiler (PMC)**.

In systems like Lean 4, modern Agda, and Idris, the coverage checker and the pattern compiler are the exact same algorithm. You use the coverage checking process to *actively generate* that nested `case` AST you showed me. This is based on adapting **Augustsson's Algorithm** for dependent types.

Here is the blueprint for the "best" way to architect this subsystem.

### The Architecture: The Pattern Matrix

To do this right, your elaborator needs an intermediate data structure called a **Pattern Matrix**.

Even if your user's surface syntax looks like your core `case` statement, if they do deep matching (e.g., matching a constructor, and then matching its arguments in the same breath), you translate their clauses into a matrix where columns are the scrutinees (the telescope variables) and rows are the user's clauses.

The goal of the PMC is to reduce this matrix down to nothing, generating your core `case` AST as a side effect.

### How the SOTA Algorithm Answers the Three Questions

Instead of writing three separate checks, the PMC matrix-reduction algorithm handles Exhaustiveness, Reachability, and Non-overlapping simultaneously through its control flow.

#### 1. Reachability (The "Split" Operation)

The core engine of the PMC is the "Split" operation. You look at a column in your matrix and decide to split on it (e.g., "Let's branch on variable `x`").

* You look up the datatype of `x` and list its constructors.
* **This is where your Pattern Unifier fires.** You run the unifier against the current telescope for *every single constructor*.
* If the unifier returns "Conflict" (impossible), you drop that constructor. It is **unreachable**.
* For the remaining valid constructors, you slice your main matrix into smaller sub-matrices, one for each constructor, refining the telescope using the substitution $\sigma$ the unifier gave you.

#### 2. Exhaustiveness (The Empty Matrix Check)

As you recursively split and build your core `case` tree, you might reach a point where your sub-matrix of user clauses is completely empty, but you still have a valid, reachable constructor from your Split operation.

* **The outcome:** You immediately throw an **Exhaustiveness Error**. You can confidently tell the user exactly which case is missing by looking at the constructor you just split on and the current state of the refined telescope.

#### 3. Non-overlapping / Redundancy (The Leftover Check)

What happens if the user wrote two branches that overlap (e.g., they wrote a specific case, and then a catch-all case that accidentally swallows other logic)?

* As the PMC successfully matches a row in the matrix, it "consumes" that row.
* When the algorithm finishes compiling the entire `case` tree, you simply look at the original matrix. Are there any rows (user clauses) that were *never consumed*?
* **The outcome:** Those leftover rows are completely shadowed by previous rows. You throw a **"Redundant / Overlapping Clause"** error.

---

### Why this is the "Best" Approach

1. **Separation of Concerns:** Your surface language can grow to support crazy, complex, multi-column equational pattern matching in the future, and your core AST gets to remain that tiny, beautiful, simple `case` statement. The PMC acts as the perfect funnel between them.
2. **Deep Pattern Matching:** If you just check a single `case` node, deep patterns (like matching `succ (succ x)`) require awkward manual unrolling. The PMC handles arbitrarily deep patterns recursively for free.
3. **Bulletproof Core:** Because the PMC *generates* the core `case` expressions using the Pattern Unifier's proofs of reachability, your core language typechecker never has to think about coverage again. It just blindly trusts that the tree is exhaustive.

If you want to build this state-of-the-art matrix compiler, the next logical bridge to cross is the data structures. Would you like to sketch out how to represent the `PatternMatrix` in your host language, or would you rather look at the "Splitting Heuristic" (how the compiler decides *which* variable to `case` on first)?

This is exactly where the beauty of the bidirectional architecture shines. The Pattern Matching Compiler (PMC) doesn't sit outside your typechecker; it acts as a very powerful, specialized **Checking** rule within it.

Think of the PMC as an "elaborator" for pattern matching. It takes the messy, surface-level user syntax (which might have deep, overlapping, or multi-column patterns) and a target `ExpectedType`, and it **compiles it down into a well-typed, primitive core `case` tree**, refining the expected type along the way.

Here is exactly how the PMC integrates into the `check` direction of your bidirectional typechecker.

### The Big Picture: Surface vs. Core

Your typechecker has two ASTs:

1. **Surface AST:** What the user wrote. For pattern matching, this might be a `match` expression with a list of complex clauses (a pattern matrix).
2. **Core AST:** Your tiny, primitive `x case { @zero => ... }` node.

When the bidirectional checker hits a surface `match` expression, it invokes the PMC to bridge the gap.

### The Algorithm: `check(Gamma, Match scruts clauses, ExpectedType)`

When you call `check` on a surface match expression, the PMC takes over. Here is the control flow:

#### Step 1: Initialize the Matrix

The PMC takes the `scruts` (the variables being matched on), the `clauses` (the user's rows), the current telescope `Gamma`, and the `ExpectedType`. It builds the initial Pattern Matrix.

#### Step 2: The Recursive Split (Refining the Type)

The PMC looks at a column in the matrix and decides to split on a variable $x$. For every valid constructor $C$ of $x$, it calls the **Pattern Unifier**.

If the unifier says $C$ is reachable, it gives you a substitution $\sigma$ (e.g., $[x \mapsto C~y~z]$).
Here is the crucial bidirectional step: **You apply $\sigma$ to both the context AND the Expected Type.**

$$\Gamma' = \sigma(\Gamma)$$

$$\text{ExpectedType}' = \sigma(\text{ExpectedType})$$

The PMC then recursively calls itself on the sub-matrix for constructor $C$, passing down this new $\Gamma'$ and $\text{ExpectedType}'$. *This is how the implicit motive is pushed down the tree.*

#### Step 3: The Base Case (Checking the Leaves)

Eventually, the PMC successfully reduces the matrix down to a single, matched user clause. It has reached a "leaf" of the case tree. All the patterns have been stripped away, and you are left with the user's right-hand side (RHS) expression.

At this exact moment, the PMC hands control *back* to your standard bidirectional typechecker:
`check(Gamma_refined, RHS_expression, ExpectedType_refined)`

If the RHS checks successfully, the PMC wraps it in the core AST's `@constructor => ...` branch and returns it up the stack.

#### Step 4: Building the Core AST

As the recursive PMC calls return, they stitch together your primitive core `case` expressions.
The final result of `check(Gamma, Match ..., ExpectedType)` is a fully elaborated, completely explicit, definitively exhaustive core AST node that is guaranteed to have type `ExpectedType`.

---

### What happens in `infer` mode?

Because you are doing dependent pattern matching without an explicit motive, **you generally cannot infer a pattern match.** If your bidirectional typechecker is in `infer` mode (synthesizing a type) and it hits a surface `match` expression, it will immediately get stuck, because it doesn't have an `ExpectedType` to push down and refine via $\sigma$.

When this happens, your compiler should do exactly what Lean and Agda do: **throw a type error demanding an annotation.**
*"Error: Cannot infer the motive for this pattern match. Please provide an explicit type signature."*

If the user adds an annotation, like `(match x { ... }) : T`, your typechecker hits the annotation, switches into `check` mode with `ExpectedType = T`, and the PMC fires up perfectly.

### Summary of the Data Flow

1. **Top-down:** `ExpectedType` and `Gamma` flow down into the PMC.
2. **Inside PMC:** The Pattern Unifier generates $\sigma$, refining `ExpectedType` and `Gamma` at each split.
3. **At the Leaves:** The refined `ExpectedType` checks the user's RHS expressions.
4. **Bottom-up:** The elaborated core `case` tree is built and returned to the typechecker.

Would you like to map out the data structures for the `PatternMatrix` and `Clause` so we can see exactly how the rows and columns are represented in code during this process?

Here are the core data structures that make the Pattern Matching Compiler (PMC) tick. By representing the problem as a matrix, the terrifying task of compiling dependent, nested, overlapping patterns becomes a clean, recursive algorithm.

We will write this in a Haskell/OCaml-like pseudo-code to keep the types clear.

### 1. The Pattern AST

Because we are generating a primitive `case` tree and relying entirely on context refinement, our pattern AST is delightfully simple. We only need variables and constructors—no dot patterns, no types, no nonsense.

```haskell
type Name = String

data Pattern
  = PVar Name              -- E.g., `x`
  | PCon Name [Pattern]    -- E.g., `succ n` or `cons x xs`

```

### 2. The Clause (A Row in the Matrix)

A `Clause` represents one full branch written by the user. If the user is matching on three things simultaneously, the clause has three patterns.

```haskell
data Clause = Clause
  { patterns :: [Pattern]  -- The columns: one pattern for each scrutinee
  , rhs      :: Expr       -- The body to evaluate if this row "wins"
  }

```

### 3. The Problem (The Matrix Itself)

This is the master state of the PMC. It bundles the matrix of clauses together with the typechecking context (the telescope) and the expected return type (the motive).

```haskell
data Problem = Problem
  { telescope :: Telescope      -- The variables we are currently scrutinizing
  , expected  :: Type           -- The refined expected type for the RHS
  , matrix    :: [Clause]       -- The rows (user clauses)
  }

```

**The Matrix Invariant:** The number of variables in the `telescope` must *always* perfectly equal the number of `patterns` in every single `Clause`. If the telescope has 3 variables, every row in the matrix must have exactly 3 patterns.

---

### How the Data Changes During Compilation

Let's trace what happens to these data structures when the PMC executes a `check` on a surface `match` expression.

#### Step 1: Initialization

Imagine the user writes a function `zip : Vec A n -> Vec B n -> Vec (A,B) n`.
Your typechecker hits the `match` block and initializes the first `Problem`:

* `telescope`: `[ (xs : Vec A n), (ys : Vec B n) ]` (Width = 2)
* `expected` : `Vec (A,B) n`
* `matrix`:
* Row 1: `[ PCon "nil" [], PCon "nil" [] ]   => rhs1`
* Row 2: `[ PCon "cons" [a, as], PVar "ys" ] => rhs2`



#### Step 2: The "Split" Operation

The PMC looks at the `telescope` and decides to split on the first column (`xs`).
It asks the unifier about the constructors for `Vec`. The unifier says `@nil` and `@cons` are both reachable. The PMC now generates **two new sub-problems**.

**Sub-Problem 1 (For `@nil`):**
The unifier generated a substitution $\sigma = [n \mapsto 0, xs \mapsto \text{nil}]$.

* `telescope`: `[ (ys : Vec B 0) ]` *(Notice the width shrank to 1, and $n$ became $0$!)*
* `expected` : `Vec (A,B) 0` *(Refined!)*
* `matrix` (We filter the old matrix for rows compatible with `@nil`):
* Row 1: `[ PCon "nil" [] ] => rhs1` *(We stripped the first pattern off!)*
* Row 2 is discarded because `@cons` conflicts with `@nil`.



**Sub-Problem 2 (For `@cons`):**
The unifier generated $\sigma = [n \mapsto \text{succ}~m, xs \mapsto \text{cons}~x~xs']$.

* `telescope`: `[ (x : A), (xs' : Vec A m), (ys : Vec B (succ m)) ]` *(Width expands because the constructor has arguments!)*
* `expected` : `Vec (A,B) (succ m)` *(Refined!)*
* `matrix`:
* Row 1 is discarded.
* Row 2: `[ PVar "a", PVar "as", PVar "ys" ] => rhs2` *(The `cons` pattern was unpacked into the new columns)*



#### Step 3: Variables and Leaves

When a column in the matrix is entirely `PVar`s (like Row 2 above), the PMC doesn't split. It just substitutes those variables into the RHS and drops the column.

When the `telescope` becomes completely empty (Width = 0), the matrix should have exactly one `Clause` left with an empty pattern list `[]`. You take that `rhs` expression, run `check(refined_gamma, rhs, refined_expected)`, and return it!

---

By manipulating this simple `Problem` record, your compiler elegantly handles deep patterns (by unpacking them into new columns) and dependent types (by mapping $\sigma$ over the `telescope` and `expected` type).

The final missing piece to make this run autonomously is the **Splitting Heuristic**. If you have multiple columns, how does the compiler choose *which* variable in the telescope to split on first? Would you like to cover the standard heuristic for picking the split column?


That is music to a compiler writer's ears. If you strictly forbid nested patterns in the core language (e.g., you cannot write `@succ (@succ %x)`), your engineering effort just dropped by an order of magnitude.

If your core language—and presumably what your typechecker directly consumes—only allows flat, single-layer patterns, you **do not need the complex Pattern Matching Compiler (PMC) matrix algorithm** we discussed earlier.

Here is exactly how this simplifies your architecture, while reinforcing why the background environment must still be a telescope.

### 1. The Environment is Still a Telescope (Mandatory)

Even with completely flat patterns, your environment $\Gamma$ must be a telescope.

Why? Because dependent types mean variables depend on *other* variables.
Imagine a context: `Gamma = [ (n : Nat), (v : Vec A n) ]`
If the user writes a flat case:

```text
n case {
  @zero => ...       -- inside here, we need `v` to become `Vec A zero`
  @succ %m => ...    -- inside here, we need `v` to become `Vec A (succ m)`
}

```

When you match on `n`, the type of `v` must change. To do that safely, the typechecker has to know that `v` was bound *after* `n` and depends on it. That ordered, dependent list of bindings is a telescope. You apply the substitution $\sigma$ generated by the flat pattern to the remainder of that telescope.

### 2. Coverage Checking Becomes Trivial (No Matrix)

Because you only have flat patterns, you don't need a recursive matrix to figure out exhaustiveness and reachability. You only ever check **one layer of depth at a time**.

When the user writes `x case { ... }`:

1. Look up the type of `x` (e.g., `Nat`).
2. Get its immediate constructors (`@zero`, `@succ`).
3. Run your Pattern Unifier on `x ~ @zero` and `x ~ @succ %m` against the current telescope.
4. If a constructor yields a "Conflict" (because of context refinement from an outer `case`), it's unreachable.
5. If it yields a valid substitution, it's required.
6. Check that the user's `case` block provides exactly the required constructors.

You don't need to build a tree, and you don't need to check overlaps. It is a strictly local, flat 1-to-1 comparison.

### 3. The Pattern Unifier is Drastically Simpler

If patterns were nested, the unifier would have to recursively break down equations like `x ~ @succ (@succ %y)`.

Because your patterns are flat, your Pattern Unifier only ever solves a single, simple kind of equation:
`Variable ~ Constructor (Fresh_Var_1 ... Fresh_Var_N)`

When checking a branch like `@cons %y %ys`:

1. The unifier sees `x ~ @cons %y %ys`.
2. It generates a substitution $\sigma = [x \mapsto \text{@cons}~y~ys]$.
3. It extends the local telescope with the fresh variables: `(y : A), (ys : Vec A n)`.
4. It applies $\sigma$ to the rest of the environment and the expected type.

### The Trade-off for the User

By forcing flat patterns in the core, the compiler is incredibly robust and easy to verify. The trade-off is that if the user wants to match deep structures (like checking if a vector has exactly two elements), they have to write manually nested `case` statements:

```text
-- To match exactly [a, b]
v case {
  @nil => ...
  @cons %x %xs => 
    %xs case {
      @nil => ...
      @cons %y %ys => ...
    }
}

```

If this is your surface language, users will just get used to writing explicit trees. If you plan to add a surface language later that *does* allow `match v { [x, y] => ... }`, you will eventually write a desugarer (a PMC) that translates that nice syntax into the nested, flat `case` core you've just described.

But for the core typechecker? Flat patterns + single scrutinee + telescopic environment + Axiom K is arguably the most elegant, easiest-to-maintain architecture for a dependently typed core calculus in existence.

---

### Critical Implementation Notes

#### 1. The Scrutinee Must Be a Variable

In the core language, the `case` expression should **only allow scrutinizing a local variable**, not an arbitrary expression. If the scrutinee is `f x` or `add n m`, dependent context refinement fails because you cannot substitute an expression like `f x` throughout the context Γ.

```text
-- GOOD (Core AST)
x case {
  @zero => ...
  @succ %m => ...
}

-- BAD (Should not be allowed in Core)
(f x) case { ... }
```

If the surface language allows matching on expressions, the desugarer must bind it first:
```text
-- Surface: (f x) case { ... }
-- Desugared to Core:
let y = f x in y case { ... }
```

This ensures the pattern unifier can generate a clean substitution like `σ = [y ↦ @zero]`.

#### 2. Occurs Check in Pattern Unification

The pattern unifier must handle cyclic equations. If it encounters:
```
x ~ @succ x
```

This must return **Conflict**, not fail or loop. An infinite cyclic term means the branch is logically impossible (unreachable), so it should be discarded just like a constructor mismatch.

#### 3. Evaluation to WHNF Before Unification

Before passing `T_scrut` to the pattern unifier, it must be evaluated to Weak Head Normal Form (WHNF). If `T_scrut` is a type alias or uncomputed type family application (e.g., `ComputeVecType A 0`), the unifier will fail because it expects a rigid datatype constructor to extract indices from.

#### 4. Substitution Application to the Environment

When applying substitution σ to the context Γ, special care is needed for De Bruijn indices. If you delete a variable from the middle of the context, you must shift all indices that pointed past it.

Example: Context `Γ = [n : Nat, v : Vec A n, w : Vec B n]`
- Match on `n`, learn `n = zero`
- Delete `n` from context
- Shift indices in types of `v` and `w` that referred to `n`
- Result: `Γ' = [v : Vec A zero, w : Vec B zero]`

#### 5. LocalEnv IS the Telescope

Do not create a separate `Telescope` type. In a dependently typed compiler, `LocalEnv` *is* a telescope by definition—every variable has a type that might depend on previous entries. Adding a second structure causes synchronization bugs. Just add `apply_subst_to_env(env, sigma)` to the existing `LocalEnv`.

#### 6. Substitution Strategy

- **Eager for Types**: When applying σ to Γ and ExpectedType, do it eagerly. The typechecker should see fully substituted, refined types immediately for accurate error messages.
- **Lazy for Values**: Keep substitutions lazy (closures) only inside the NbE evaluator when reducing terms to WHNF.

---

### Variable Shifting in apply_subst_to_env

When the pattern unifier solves `x ~ @constructor args`, we need to remove `x` from the context and substitute its value everywhere. With De Bruijn indices, this requires careful shifting.

**hwml-rust's convention**:
- **Level** = position counting from the *beginning* (Level 0 = first binding)
- **Index** = De Bruijn index counting from the *end* (Index 0 = most recent binding)
- Conversion: `level.to_index(depth) = Index(depth - level - 1)`

**Scenario**: Context with depth 3
```
Level 0: n : Nat           -- Index 2 (when depth=3)
Level 1: v : Vec A n       -- Index 1 (when depth=3), type refers to n
Level 2: w : Vec B n       -- Index 0 (when depth=3), type refers to n
```

In the types of `v` and `w`, `n` appears as a Rigid variable with `Level(0)`.

**Step 1**: User matches on `n` (at Level 0) against `@zero`
- Pattern unifier returns: `σ = [Level(0) ↦ @zero]`

**Step 2**: Apply σ to the context types
- Walk entries at Level 1 and Level 2
- Substitute any `Rigid(Level(0))` with `@zero` in their types
- After removal, shift all remaining levels down

**The Algorithm** (using Levels, not Indices):

```rust
fn apply_subst_to_env(
    env: &mut TCEnvironment,
    solved_level: Level,      // Which variable was solved (e.g., Level(0))
    solved_value: Rc<Value>,  // What it was solved to (e.g., @zero)
) {
    let depth = env.depth();

    // For each binding AFTER the solved variable
    for level in (solved_level.0 + 1)..depth {
        // Substitute: replace Rigid(solved_level) with solved_value
        // in the TYPE of this binding
        env.types[level] = substitute_level(
            &env.types[level],
            solved_level,
            &solved_value,
        );

        // Also update the VALUE if it references the solved level
        env.values[level] = substitute_level(
            &env.values[level],
            solved_level,
            &solved_value,
        );
    }

    // Remove the solved variable and shift remaining levels
    env.remove_and_shift(solved_level);
}

fn substitute_level(
    term: &Rc<Value>,
    target: Level,
    replacement: &Rc<Value>,
) -> Rc<Value> {
    // Recursively walk the value:
    // - If Rigid with head.level == target: return replacement.clone()
    // - Otherwise: recurse into subterms (closures need care!)
}

fn remove_and_shift(env: &mut TCEnvironment, removed: Level) {
    // Remove entry at `removed` level
    env.types.remove(removed.0);
    env.values.remove(removed.0);

    // All remaining Rigid variables with level > removed need to be shifted down
    // This happens naturally if we're using levels stored in the terms themselves
    // But we need to walk all types/values and decrement level references
    for i in removed.0..env.depth() {
        env.types[i] = shift_levels_down(&env.types[i], removed);
        env.values[i] = shift_levels_down(&env.values[i], removed);
    }
}

fn shift_levels_down(term: &Rc<Value>, removed: Level) -> Rc<Value> {
    // For every Rigid(level) where level > removed:
    //   Replace with Rigid(level - 1)
}
```

**Key Insight**: Since hwml-rust uses Levels (not Indices) in its Value representation, we substitute by matching on the Level directly. The shifting happens after removal—any `Rigid(Level(k))` where `k > removed` becomes `Rigid(Level(k-1))`.

---

### Implementation Order

Based on the architectural analysis, the recommended implementation order is:

1. **Phase 3: AST Changes** — Remove `return_type`, restrict scrutinee to variables
2. **Phase 1: LocalEnv Enhancement** — Add `apply_subst_to_env` with proper shifting
3. **Phase 2: Pattern Unifier** — Build the separate unifier with Deletion, Solution, Injectivity, Conflict, and Occurs Check
4. **Phase 4: Type Checking** — Wire up check-only case with refinement
5. **Phase 5: Coverage Checking** — Flat-pattern exhaustiveness
6. **Phase 6: Diagnostics** — Error reporting via Salsa accumulators




You are exactly half right, and your intuition is pointing you in the absolute correct direction for building a production compiler.

Here is the exact boundary of what you need to enforce in your core language, and where you might be slightly over-correcting.

### 1. Spot On: The Scrutinee MUST be a Variable

Yes, you should absolutely ban arbitrary expressions from being the scrutinee in your core `case` AST node.

Your core syntax should strictly be:

```rust
pub struct Case {
    pub scrutinee: Level, // ONLY a local variable reference!
    pub branches: Vec<Branch>,
}

```

If the surface language has `match f x { ... }`, the elaborator must desugar it into `let y = f x in y case { ... }` before passing it to the core. This guarantees your Pattern Unifier always knows exactly which variable's De Bruijn level it is solving for.

### 2. Over-correction: Banning Expressions in Type Indices

You **do not** need to ban arbitrary expressions from appearing in the scrutinee's type indices in the core AST.

You can safely allow the core language to represent `v : Vec Unit (f x)`.
Why? Because your Pattern Unifier already naturally polices this! If the core typechecker tries to check `v case { @nil => ... }`, the unifier will see `f x ~ 0`, realize it is not a variable, and safely return `PatternUnifyOutcome::Stuck`.

You don't need to syntactically forbid it; the semantic math of your unifier already gracefully rejects it. It becomes the **elaborator's responsibility** to ensure the core typechecker never encounters that `Stuck` state.

### What Your Core Language ACTUALLY Needs

If you want your elaborator to use the Lean 4 approach (abstracting expressions and rewriting context types so the core unifier never gets stuck), your core language AST must support exactly three primitive constructs.

#### 1. Transparent `let` Bindings

Your core AST needs a `Let(Name, Expr, Expr)` node, and your NbE evaluator must treat it transparently.
When the elaborator generates `let y = f x in ...`, the core evaluator must know that `y` evaluates to `f x`. This is required so that definitional equality is preserved after the elaborator abstracts the expression.

#### 2. The Identity Type (`Eq` and `Refl`)

You need a primitive type for propositional equality, and its single constructor.

```rust
// Core AST additions:
Eq(Type, Expr, Expr)  // e.g., Eq Nat (f x) 0
Refl                  // The proof that x = x

```

#### 3. The Rewrite Operator (`transport` or Axiom J)

This is the single most important addition. To "un-stick" a type index, the elaborator needs a core operator that takes an equality proof and uses it to cast a value from one type to another.

You need an AST node that looks something like this:

```rust
Transport {
    motive: Expr,  // A function describing the type family, e.g., `\i => Vec Unit i`
    proof: Expr,   // A proof that `a = b`
    value: Expr,   // A value of type `motive(a)`
} // Evaluates to a value of type `motive(b)`

```

### How the Elaborator Uses These 3 Primitives

If the user writes `match v { @nil => ... }` on a vector `v : Vec Unit (f x)`, your elaborator will automatically generate this core AST:

1. **Let-bind the index:** `let y = f x`
2. **Let-bind a proof:** `let h : Eq Nat y (f x) = Refl`
3. **Transport the vector:** `let v_cast = Transport(\i => Vec Unit i, h, v)`
*(The core typechecker sees that `v` has type `Vec Unit (f x)`, applies the proof `h`, and assigns `v_cast` the type `Vec Unit y`)*
4. **Generate the core case:** `v_cast case { @nil => ... }`

When the core typechecker hits step 4, it asks the Pattern Unifier to match `v_cast` (which has type `Vec Unit y`) against `@nil` (which has type `Vec Unit 0`).
The unifier sees `y ~ 0`. Because `y` is a variable, **it succeeds**, generates $\sigma = [y \mapsto 0]$, and typechecking completes flawlessly without ever getting `Stuck`.

### Summary

Keep your core AST dumb, small, and simple.

* Force `case` to only scrutinize variables.
* Let types contain whatever they want.
* Provide `let`, `Eq`, and `Transport` as primitive LEGO blocks.

Your elaborator will use those blocks to magically shield the typechecker from ever seeing a complex, stuck index during pattern matching.


Sticking with your current dependent pattern unifier is absolutely the right call. It keeps your core language pure and your NbE evaluator fast.

If you are going to use the Elaborator to solve the "stuck on `f x`" problem by introducing equality proofs (like `h : f x = y`), your core language needs exactly one new tool to actually *use* those proofs: **Axiom J**, more commonly implemented as a `Transport` (or `rewrite`) operator.

Here is exactly how the equality proof sits in the environment, how the Elaborator uses it to fix the types, and how your NbE evaluator computes it so it disappears at runtime.

### 1. The Tool: The `Transport` AST Node

To use an equality proof, your core AST needs a primitive node that consumes it.

In type theory, if you have a proof that $a = b$, and a value of type $P~a$, you can "transport" that value along the equality proof to get a value of type $P~b$.

Your core AST needs a node like this:

```rust
pub struct Transport {
    pub motive: Rc<Expr>,  // The type family P (e.g., \i => Vec A i)
    pub proof: Rc<Expr>,   // The equality proof (e.g., h : a = b)
    pub value: Rc<Expr>,   // The value to cast (e.g., v : P a)
} 

```

### 2. How the Elaborator Uses It (Pre-Typechecking)

Let's go back to our nightmare context: `Gamma = (x : Nat), (v : Vec A (f x))`.
The user writes: `match f x { @zero => ... }`

The Elaborator intercepts this and explicitly builds a new context using `Transport` before handing it to your core typechecker.

**Step A: Introduce the variable and the proof**
The elaborator binds `y` and the proof `h`:
`let y = f x;`
`let h : Eq Nat (f x) y = Refl;`

**Step B: Cast the dependent variables**
The elaborator looks at the telescope and sees that `v` depends on `f x`. It uses the proof `h` and the `Transport` node to cast `v` into a new variable whose type depends on `y` instead!

`let v_cast = Transport(\i => Vec A i, h, v);`

Now, the Elaborator has built this beautiful, generalized environment for the core:
`Gamma' = ..., (y = f x), (h = Refl), (v_cast : Vec A y)`

**Step C: Emit the Core Case**
Now it emits the core syntax: `y case { @zero => ... }`.

### 3. How the Core Typechecker Uses It

When your core typechecker receives this desugared AST, it is perfectly happy.

1. It looks at `Transport(\i => Vec A i, h, v)`.
2. It checks that `h` has type `Eq Nat (f x) y`.
3. It checks that `v` has type `Vec A (f x)`.
4. It synthesizes the output type of the `Transport` node as `Vec A y`.
5. It hits `y case { @zero => ... }`. The Pattern Unifier sees `y ~ @zero`, generates `[y ↦ @zero]`, and the type of `v_cast` flawlessly refines to `Vec A @zero`.

### 4. The Magic: How the Evaluator Computes It

You might be thinking: *"Wait, if I wrap my vectors in all these `Transport` nodes, won't it ruin my runtime data and block computation?"*

This is where the magic of NbE (Normalization by Evaluation) comes in. You just need to add one single reduction rule to your evaluator for the `Transport` node.

**The Rule of `Refl`:**
If the `proof` argument of a `Transport` evaluates to the `Refl` constructor, **the transport vanishes.**

```rust
// Inside your NbE eval() function:
match expr {
    Expr::Transport { motive, proof, value } => {
        let evaluated_proof = eval(env, proof)?;
        let evaluated_value = eval(env, value)?;
        
        match evaluated_proof {
            // If the proof is definitionally Refl, we don't need to cast anything!
            // Just return the inner value.
            Value::DataConstructor("Refl", _) => evaluated_value,
            
            // If the proof is a stuck variable (e.g., an abstract hypothesis),
            // the transport itself becomes a stuck neutral value.
            _ => Value::Neutral(Neutral::Transport(motive, evaluated_proof, evaluated_value)),
        }
    }
}

```

Because your Elaborator generated `let h = Refl`, whenever the evaluator tries to compute `v_cast`, it evaluates `h`, sees `Refl`, and immediately unpacks the original vector `v`. The `Transport` nodes act as compile-time scaffolding to satisfy the rigid typechecker, but they completely evaporate during evaluation, leaving your runtime performance untouched.

### Summary

1. The equality proof sits in the context (usually bound to `Refl`).
2. The Elaborator wraps variables in `Transport` AST nodes, pointing at that proof, to align their types with the scrutinee variable.
3. The Core Typechecker verifies the `Transport` boundaries.
4. The Evaluator deletes the `Transport` node the moment it sees `Refl`.

This is the ultimate, production-grade way to separate the user's desire to "match on anything" from the core compiler's need to "only match on variables."
