# Backtracking-Free Mixfix Operator Parsing (Danielsson & Norell)

**Created:** 2026-05-06
**Type:** Deep Dive Analysis
**Paper:** "Parsing Mixfix Operators" (IFL 2008)
**Authors:** Nils Anders Danielsson, Ulf Norell
**Confidence:** 0.95

---

## Executive Summary

Danielsson & Norell's approach achieves **efficient mixfix parsing with limited backtracking** through:

1. **Non-recursive grammar** (neither left nor right recursive)
2. **Precedence DAG** (directed acyclic graph) instead of total order
3. **Memoising parser combinators** (polynomial complexity despite backtracking)
4. **Type-driven correctness** (precedence-correct expressions by construction in Agda)

**Key Innovation:** The grammar structure ensures backtracking only happens at operator choice points (which are finite and local), not during recursive descent.

---

## 1. The Backtracking Problem in Mixfix Parsing

### 1.1 Why Mixfix Needs Backtracking (Naively)

**Example:**
```
if_then_else_  :  Bool → A → A → A
_+_            :  Nat → Nat → Nat
```

Parsing: `if x then y + z else w`

**Problem:** When we see `y`, we don't know if:
- It's the `then` argument (parse stops at `+`)
- We should continue to `y + z` (binds tighter than `if`)

Traditional approaches:
- **Full backtracking:** Try every possibility (exponential!)
- **Precedence numbers:** Pre-assign total order (not modular)
- **Operator grammar:** Complex, hard to extend

### 1.2 Sources of Backtracking

1. **Operator ambiguity:** Multiple operators with same precedence
2. **Associativity:** `a + b + c` → `(a + b) + c` vs `a + (b + c)`
3. **Mixfix boundaries:** Where does `if_then_else_` end?
4. **Closed operators:** Distinguishing `[x]` from `[x,y]`

---

## 2. The Non-Recursive Grammar

### 2.1 Grammar Structure (From Agda Code)

**Key insight:** Grammar is parameterized by **precedence level**, and each level only calls to **higher** precedence levels.

```agda
mutual
  -- Top-level: any precedence from the graph
  expr : ∞ (Parser (Expr g))
  expr = ♯ precs g

  -- Parse operators at precedences ps
  precs : (ps : List Precedence) → Parser (Expr ps)
  precs []       = fail
  precs (p ∷ ps) = (λ e → here refl ∙ proj₂ e) <$> prec p
                 ∣ weakenE                     <$> precs ps

  -- Parse ONE precedence level p
  prec : (p : Precedence) → Parser (∃ (ExprIn p))
  prec (precedence ops sucs) =
      ⟪_⟫    <$>       [ closed   ]    -- closed operators
    ∣ _⟨_⟩_  <$>  p↑ ⊛ [ infx non ] ⊛ p↑  -- non-assoc infix
    ∣ appʳ   <$>       preRight +   ⊛ p↑  -- prefix/right-assoc
    ∣ appˡ   <$>  p↑ ⊛ postLeft +         -- postfix/left-assoc
    ∣ fail
    where
    p↑ = precs sucs  -- ONLY call to HIGHER precedences!
```

**Why no left/right recursion:**
- `p↑` (higher precedences) is structurally smaller than current level
- Never calls back to same or lower precedence
- Terminates because DAG has no cycles

### 2.2 Precedence DAG

**Structure:**
```agda
data Precedence : Set where
  precedence : (ops : (fix : Fixity) → List (∃ (Operator fix)))
               (sucs : List Precedence) →
               Precedence
```

Each precedence level stores:
- `ops`: Operators at this level (grouped by fixity)
- `sucs`: **Successor** levels (bind tighter)

**Example DAG:**
```
      [low precedence]
            +, -
           /    \
          /      \
    [medium]    [medium]
       *          /
        \        /
         \      /
      [high precedence]
            ^
```

**Key property:** DAG → topological sort → no cycles → termination

---

## 3. Where Backtracking DOES Occur (And Why It's Bounded)

### 3.1 Operator Choice Backtracking

In the `prec` function, we have **4 branches** with `∣` (choice combinator):

```agda
prec p =
    ⟪_⟫    <$> [ closed   ]    -- Branch 1
  ∣ _⟨_⟩_  <$> ...             -- Branch 2
  ∣ appʳ   <$> ...             -- Branch 3
  ∣ appˡ   <$> ...             -- Branch 4
  ∣ fail
```

**Backtracking happens here** when:
- Branch 1 fails → try Branch 2
- Branch 2 fails → try Branch 3
- etc.

**But:** This is **bounded** because:
- Only 4 branches (constant)
- Each branch determined by **first token** (operator name part)
- No nested backtracking in recursion!

### 3.2 Multiple Operators at Same Precedence

```agda
inner : ∀ {fix} (ops : List (∃ (Operator fix))) →
        Parser (Inner ops)


### 6.3 Stratified Grammar

**Key technique:** Stratify by precedence level.

```
expr       ::= precs_all
precs_low  ::= prec_low | precs_med
precs_med  ::= prec_med | precs_high
precs_high ::= prec_high | atoms
```

**Property:** Each level only calls to **strictly higher** levels.
- No mutual recursion at same level
- No left recursion (calls go "up" the DAG)
- No right recursion (same reason)

**Result:** Structurally decreasing recursion → guaranteed termination.

---

## 7. Practical Implementation Strategies

### 7.1 When to Use Memoised Backtracking

**Use when:**
- You need modular precedence (DAG not total order)
- Mixfix operators are important (not just binary infix)
- Correctness > raw speed
- You have a library with good memoisation (e.g., parser-combinators in Haskell/Agda)

**Performance characteristics:**
- **Space:** O(n × P) where P = number of parsers
- **Time:** O(n³) worst case, often O(n²) in practice
- **Parse table size:** Can be large for complex grammars

### 7.2 When to Use Pratt Parsing

**Use when:**
- Precedence is total order (or you're willing to make it so)
- Primarily binary infix operators
- Speed is critical (O(n) matters)
- Simple implementation preferred

**Limitations:**
- Harder to extend to mixfix (ternary `?:`, etc.)
- Precedence is global, not modular
- Harder to verify correctness formally

### 7.3 Hybrid Approach: Pratt + Precedence DAG

**Idea:** Use Pratt's algorithm, but:
1. At ambiguous points (operators with no precedence relation), **suspend**
2. Create choice points
3. Use limited backtracking or constraint solving

**Example:**
```rust
fn pratt_parse_expr(min_bp: i32) -> Expr {
    let mut left = parse_prefix();
    loop {
        let next_op = peek_operator();
        match compare_precedence(next_op, min_bp) {
            Less => break,              // Stop
            Greater => {                // Continue
                consume();
                let right = pratt_parse_expr(next_op.bp);
                left = BinOp(next_op, left, right);
            }
            Ambiguous => {              // CHOICE POINT
                // Option 1: Emit suspended constraint
                // Option 2: Try both, pick first success
                // Option 3: Report error
            }
        }
    }
    left
}
```

**Advantage:** O(n) in common case, only backtrack when truly ambiguous.

---

## 8. Backtracking-Free Alternatives

### 8.1 Operator Precedence Parser (Shunting Yard)

**Algorithm:** Convert infix to postfix, then evaluate.

**Steps:**
1. Scan left to right
2. Maintain operator stack
3. Compare precedences to decide push vs reduce
4. Build AST from postfix

**Complexity:** O(n), no backtracking.

**Limitation:** Harder to extend to mixfix, requires precedence numbers.

### 8.2 Precedence Climbing

**Algorithm:** Similar to Pratt, but more explicit.

```python
def parse_expr(min_prec):
    left = parse_atom()
    while peek_binop() and peek_binop().prec >= min_prec:
        op = consume_binop()
        right_min_prec = op.prec + (1 if op.left_assoc else 0)
        right = parse_expr(right_min_prec)
        left = BinOp(op, left, right)
    return left
```

**Complexity:** O(n), deterministic.

**Key:** Precedence climbing = Pratt simplified (no `nud`/`led` distinction).

### 8.3 Packrat Parsing

**Algorithm:** Memoisation + PEG (Parsing Expression Grammar).

**PEG properties:**
- Ordered choice (first match wins, no backtracking)
- But memoises everything → O(n) time, O(n²) space

**Difference from Danielsson-Norell:**
- PEG: Ordered choice (deterministic, no ambiguity)
- D-N: Backtracking choice (explores all alternatives, picks unique parse)

---

## 9. Key Takeaways for HWML

### 9.1 What to Adopt

1. **Precedence DAG:** Much more modular than total order
   - Different modules can define operators without coordination
   - Only specify ordering where it matters

2. **Stratified grammar:** Non-recursive by construction
   - Easier to verify termination
   - Natural fit for precedence-based parsing

3. **Memoisation:** If using parser combinators
   - Makes backtracking practical
   - Parser-combinator libraries often provide this

### 9.2 What to Avoid

1. **Arbitrary mixfix:** Too complex for most languages
   - Consider restricting to prefix/infix/postfix
   - Or limit to specific known patterns (`if_then_else`, ternary `?:`)

2. **Pure backtracking:** Without memoisation
   - Can be exponential
   - Only works for very small grammars

### 9.3 Recommended Approach for HWML

**Phase 1: Simple Pratt Parser**
- Binary infix operators with precedence numbers
- O(n), deterministic, easy to implement
- Good enough for MVP

**Phase 2: Add Precedence DAG**
- Replace precedence numbers with partial order
- Keep Pratt's algorithm but handle ambiguity explicitly
- Emit constraints for ambiguous cases

**Phase 3: Limited Mixfix**
- Support specific patterns (ternary, subscript, etc.)
- Use precedence DAG to integrate them
- Possibly use memoised parser combinators for this part

**Phase 4: Full Mixfix (If Needed)**
- Implement Danielsson-Norell grammar
- Use their Agda formalization as reference
- Memoising parser combinators required

---

## 10. Code Examples

### 10.1 Precedence DAG in Rust

```rust
use std::collections::HashMap;

/// Precedence is a partial order
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct PrecedenceLevel(usize);

/// Operator at a precedence level
struct Operator {
    name: String,
    prec: PrecedenceLevel,
    fixity: Fixity,
}

/// Precedence graph: maps level to operators and successors
struct PrecedenceDAG {
    /// Operators at each level (grouped by fixity)
    ops: HashMap<PrecedenceLevel, Vec<Operator>>,

    /// Edges: sucs[p] = levels that bind tighter than p
    sucs: HashMap<PrecedenceLevel, Vec<PrecedenceLevel>>,
}

impl PrecedenceDAG {
    /// Check if p1 < p2 (p2 binds tighter)
    fn precedes(&self, p1: PrecedenceLevel, p2: PrecedenceLevel) -> Option<bool> {
        // BFS from p1 to see if we can reach p2
        // Return None if no path exists (ambiguous)
        self.has_path(p1, p2)
    }

    fn has_path(&self, from: PrecedenceLevel, to: PrecedenceLevel) -> Option<bool> {
        if from == to { return Some(false); }

        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(from);

        while let Some(current) = queue.pop_front() {
            if current == to { return Some(true); }
            if !visited.insert(current) { continue; }

            if let Some(succs) = self.sucs.get(&current) {
                queue.extend(succs.iter().copied());
            }
        }

        None  // No path found → ambiguous
    }
}
```

### 10.2 Pratt Parser with Ambiguity Handling

```rust
enum PrecOrder { Less, Greater, Equal, Ambiguous }

fn parse_expr(min_bp: i32, dag: &PrecedenceDAG) -> Result<Expr, ParseError> {
    let mut left = parse_prefix()?;

    loop {
        let Some(next_op) = peek_operator() else { break };

        match compare_prec(next_op.prec, min_bp, dag) {
            PrecOrder::Less | PrecOrder::Equal => break,

            PrecOrder::Greater => {
                consume();
                let right_bp = next_op.bp + if next_op.left_assoc { 1 } else { 0 };
                let right = parse_expr(right_bp, dag)?;
                left = Expr::BinOp(next_op, Box::new(left), Box::new(right));
            }

            PrecOrder::Ambiguous => {
                // Option 1: Error
                return Err(ParseError::AmbiguousPrecedence(next_op, left));

                // Option 2: Suspend (emit constraint)
                // left = Expr::Suspended(next_op, left, ...);
                // break;
            }
        }
    }

    Ok(left)
}
```

---

## 11. Further Reading

### 11.1 Danielsson's Papers

1. **"Parsing Mixfix Operators"** (IFL 2008) - The main paper
2. **"Total Parser Combinators"** (ICFP 2010) - Memoisation details
3. **"Structurally Recursive Descent Parsing"** (2008) - Ruling out left recursion with types

### 11.2 Pratt Parsing

1. Vaughan Pratt: **"Top Down Operator Precedence"** (1973) - Original paper
2. Bob Nystrom: **"Pratt Parsers: Expression Parsing Made Easy"** (blog post)
3. Matklad: **"Simple but Powerful Pratt Parsing"** (blog post)

### 11.3 Related Techniques

1. **Precedence Climbing:** Martin Richards (1979)
2. **Operator Precedence Parsing:** Floyd (1963)
3. **Packrat Parsing:** Ford (2002)

---

## 12. Summary

**Danielsson-Norell achieve efficient mixfix parsing through:**

✅ **Non-recursive grammar** stratified by precedence
✅ **Precedence DAG** for modularity
✅ **Bounded backtracking** (only at operator choices)
✅ **Memoisation** (makes backtracking polynomial)
✅ **Type-driven correctness** (Agda proof)

**Backtracking is NOT eliminated**, but is **controlled and bounded**:
- Happens at operator choice points
- Memoisation prevents exponential blowup
- Result: O(n³) worst case, often O(n²) in practice

**For HWML:** Start with Pratt (no backtracking), extend to DAG, add mixfix later if needed.
```

**Backtracking:** If first operator doesn't match, try next in list.

**Bounded by:** Number of operators at this precedence/fixity (typically small).

---

## 4. Memoisation Makes Backtracking Polynomial

### 4.1 The Key Insight

From Danielsson's **"Total Parser Combinators"** paper:

**Without memoisation:** Backtracking can explore same input position exponentially many times.

**With memoisation:** Each parser is called **at most once** per input position.

**Result:** `O(n³)` or `O(n²)` complexity (depends on grammar), where `n` = input length.

### 4.2 How It Works

**Parser combinator library caches:**
- For each `(parser, position)` pair
- The result (success/failure + remainder)

**Example:**
```
Input: a + b * c

Position 2 (at 'b'):
  prec(high) called → memoized result: success, parsed '*'

Later, different branch reaches position 2:
  prec(high) called → return cached result (no re-parse!)
```

**Implementation:** Hash table or trie mapping `(Parser, Position) → Result`.

---

## 5. Comparison with Pratt Parsing

### 5.1 Pratt Parser = No Backtracking!

**Pratt's key idea:**
- **Single pass**, **deterministic**
- Each operator has **binding power** (precedence number)
- At each step, decide based on **current** vs **next** binding power

**Pratt algorithm:**
```
parse_expr(min_bp):
  left = parse_prefix()  // No choice, deterministic
  while next_op.bp >= min_bp:
    op = consume()
    right = parse_expr(op.bp + (if left_assoc then 1 else 0))
    left = make_binop(op, left, right)
  return left
```

**No backtracking:** Decision made immediately based on precedence comparison.

### 5.2 Danielsson-Norell vs Pratt

| Feature | Danielsson-Norell | Pratt |
|---------|------------------|-------|
| **Precedence** | DAG (partial order) | Numbers (total order) |
| **Associativity** | Part of grammar | Binding power adjustment |
| **Mixfix** | Full support (arbitrary parts) | Requires extension |
| **Backtracking** | Yes, but memoised | No |
| **Modularity** | Can compose DAGs | Must renumber precedences |
| **Complexity** | O(n³) worst case | O(n) deterministic |
| **Correctness** | Type-checked (Agda) | Informal |

**Trade-off:** Pratt is faster, Danielsson-Norell is more expressive and modular.

---

## 6. Avoiding Backtracking: Design Principles

### 6.1 Make Operator Boundaries Explicit

**Problem:** When does `if_then_else_` end?

**Solution:** Use **keywords** that are reserved tokens.
- `if`, `then`, `else` cannot be identifiers
- Parser knows when they appear → no ambiguity

**In Agda:**
```agda
nameParts : Operator fix n → Vec (Maybe NamePart) n
```
- `Just "if"` → must match exactly
- `Nothing` → hole (expression)

### 6.2 Precedence DAG Construction

**Principle:** Build DAG incrementally, only add edges when needed.

**Example:**
```agda
-- Module 1
_+_ : prec 10
_*_ : prec 20
_^_ : prec 30

-- Module 2 (imports Module 1)
_/_ : prec 20  -- Same as *, no ordering between them

-- DAG:
--   30 (^)
--   /  \
--  /    \
-- 20a(*) 20b(/)
--  \    /
--   10 (+)
```

**No backtracking:** Each precedence level is separate node.

**Potential ambiguity:** `a * b / c` is **ambiguous** (no edge between `*` and `/`).
- Parser could reject OR
- Require parentheses OR
- Use left-to-right tie-breaker

