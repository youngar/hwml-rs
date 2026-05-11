# Pattern Parsing: Agda-Style Mixfix Operator Resolution

**Date:** 2026-05-11  
**Status:** 🚨 CRITICAL REVISION - Changes Pattern AST Design  
**Supersedes:** Previous Pattern disambiguation strategy  
**Related:**
- [[TOP-DOWN-PARSER-MIGRATION]] - Base parser plan
- [[PATTERN-VS-EXPRESSION-DISAMBIGUATION]] - Research (needs update)
- [[AGDA-PATTERN-DESTRUCTURING-RESEARCH]] - Agda's actual approach

---

## 🚨 Critical Insight

**HWML uses Agda-style mixfix operators.** This means we **CANNOT** determine operator structure during parsing because:

1. **Operator parts are distributed:** `if_then_else_` has parts: `if`, `then`, `else`
2. **Need scope information:** Can't tell if `if` is an operator part or variable without looking up declarations
3. **Need fixity information:** Can't determine precedence/associativity without seeing the operator declaration
4. **Need type information:** Multiple valid parsings may exist; types disambiguate

**Example that breaks naive parsing:**
```rust
// Source:
fun (if x then y else z : Bool) => ...

// Is this:
// 1. Mixfix constructor pattern: if_then_else_(x, y, z)
// 2. Application: if(x, then, y, else, z)
// 3. Variable: if, followed by other variables?
// Parser cannot tell without scope/fixity/type info!
```

---

## What Agda Actually Does

**From Agda source code analysis:**

### Phase 1: Parser - Flat Application Sequences
```haskell
-- Agda parses: if x then y else z
-- As: App [Ident "if", Ident "x", Ident "then", Ident "y", Ident "else", Ident "z"]

-- No operator structure! Just a flat list of names.
```

### Phase 2: Scope Checker - Operator Resolution
```haskell
-- Scope checker:
-- 1. Resolves all names (variables vs constructors vs operator parts)
-- 2. Finds all mixfix operators in scope
-- 3. Reparses the flat sequence using precedence climbing
-- 4. Builds precedence graph
-- 5. Produces structured operator applications

-- Output: if_then_else_(x, y, z)  -- Now knows it's an operator!
```

### Phase 3: Type Checker - Disambiguation
```haskell
-- If multiple parsings exist (ambiguous precedence):
-- - Use type information to pick the correct one
-- - Report error if still ambiguous
```

---

## Revised Pattern AST for HWML

### Surface Syntax (Parser Output)

**Key change:** No `Infix` or `App` constructors - just flat sequences!

```rust
/// Surface pattern - unparsed, no operator structure
#[derive(Clone, Eq, PartialEq, Debug, Hash)]
pub enum Pattern {
    /// Single identifier (variable or nullary constructor or operator part)
    Ident(Id),
    
    /// Flat application sequence - NOT YET PARSED INTO OPERATORS
    /// Parser just collects adjacent atoms into a flat list
    /// Example: "if x then y else z" → AppSeq([if, x, then, y, else, z])
    /// Scope checker will reparse this using fixity information
    AppSeq {
        loc: Range<usize>,
        elements: Vec<Pattern>,  // Flat list - no structure yet!
    },
    
    /// As-pattern: name @ pattern
    /// Special syntax, parsed eagerly (@ is never an operator part)
    As {
        loc: Range<usize>,
        name: Id,
        pattern: Box<Pattern>,
    },
    
    /// Parenthesized pattern
    /// Forces grouping, parsed eagerly
    Paren {
        loc: Range<usize>,
        pattern: Box<Pattern>,
    },
    
    /// Wildcard
    Underscore {
        loc: Range<usize>,
    },
    
    /// Numeric literal (for pattern matching on constants)
    Num {
        loc: Range<usize>,
        value: i64,
    },
    
    /// String literal
    Str {
        loc: Range<usize>,
        value: String,
    },
    
    /// Error pattern with provenance
    Error {
        loc: Range<usize>,
        provenance: ParseProvenance,
    },
}

/// Binder with unparsed pattern
pub struct Binder {
    pub loc: Range<usize>,
    pub pattern: Pattern,  // Unparsed! Just a flat sequence.
}
```

**Critical:** Parser does NOT try to determine:
- Which identifiers are operators
- Operator precedence
- Operator associativity
- Constructor vs variable

**Parser ONLY does:**
- Collect adjacent atoms into `AppSeq`
- Handle special syntax (`@`, `_`, parentheses, literals)
- Preserve source location

---

## Core Syntax (After Scope Checking)

**After scope checker reparses with fixity info:**

```rust
/// Core pattern - operator structure resolved, constructors identified
pub enum Pattern {
    /// Variable binding
    Var(Id),
    
    /// Constructor application (after operator resolution)
    Constructor {
        name: QualifiedName,  // Fully resolved constructor
        args: Vec<Pattern>,
    },
    
    /// Mixfix operator application (special case of Constructor)
    /// Example: if_then_else_(cond, then_branch, else_branch)
    MixfixOp {
        name: QualifiedName,
        parts: Vec<Id>,      // ["if", "then", "else"]
        args: Vec<Pattern>,  // [cond, then_branch, else_branch]
    },
    
    /// Wildcard
    Wildcard,
    
    /// Literal
    Literal(Literal),
    
    /// As-pattern
    As {
        name: Id,
        pattern: Box<Pattern>,
    },
    
    /// Ambiguous pattern (multiple valid parsings)
    /// Elaborator will use types to disambiguate
    Ambiguous {
        candidates: Vec<Pattern>,
        reason: AmbiguityReason,
    },
}
```

---

## Three-Phase Flow (Revised)

### Phase 1: Parser → Flat Sequences

**Input:**
```rust
fun (if x then y else z : Bool) => ...
```

**Parser output:**
```rust
Binder {
    loc: 0..23,
    pattern: Pattern::AppSeq {
        loc: 5..23,
        elements: vec![
            Pattern::Ident(Id { value: "if", loc: 5..7 }),
            Pattern::Ident(Id { value: "x", loc: 8..9 }),
            Pattern::Ident(Id { value: "then", loc: 10..14 }),
            Pattern::Ident(Id { value: "y", loc: 15..16 }),
            Pattern::Ident(Id { value: "else", loc: 17..21 }),
            Pattern::Ident(Id { value: "z", loc: 22..23 }),
        ]
    }
}
```

**Key:** No operator structure! Just a flat list.

---

### Phase 2: Scope Checker → Operator Resolution

**Scope checker algorithm:**

```rust
impl ScopeChecker {
    fn resolve_pattern(&self, pat: &surface::Pattern) -> Result<core::Pattern> {
        match pat {
            surface::Pattern::AppSeq { elements, loc } => {
                // Step 1: Resolve all identifiers to Names
                let names: Vec<ResolvedName> = elements.iter()
                    .map(|e| self.resolve_name(e))
                    .collect::<Result<_>>()?;
                
                // Step 2: Find all mixfix operators that could apply
                let operators = self.find_applicable_operators(&names);
                
                // Step 3: Build precedence graph
                let prec_graph = PrecedenceGraph::build(&operators)?;
                
                // Step 4: Reparse using precedence climbing
                let parsings = self.precedence_climb(&names, &prec_graph)?;
                
                // Step 5: Handle result
                match parsings.len() {
                    0 => {
                        // No operators match - treat as simple application
                        self.resolve_simple_application(names)
                    }
                    1 => {
                        // Unique parsing - use it
                        Ok(parsings.into_iter().next().unwrap())
                    }
                    _ => {
                        // Multiple parsings - ambiguous!
                        // Pass to elaborator for type-directed disambiguation
                        Ok(core::Pattern::Ambiguous {
                            candidates: parsings,
                            reason: AmbiguityReason::OperatorPrecedence,
                        })
                    }
                }
            }
            
            surface::Pattern::Ident(id) => {
                // Single identifier - is it a constructor or variable?
                match self.lookup(id) {
                    Some(Entry::Constructor(ctor)) => {
                        Ok(core::Pattern::Constructor {
                            name: ctor.qualified_name,
                            args: vec![],
                        })
                    }
                    _ => {
                        Ok(core::Pattern::Var(id.clone()))
                    }
                }
            }
            
            // ... other cases
        }
    }
}
```

---

### Phase 3: Elaborator → Type-Directed Disambiguation

```rust
impl Elaborator {
    fn elab_pattern(&mut self, pat: &core::Pattern, expected_ty: &Type) -> Result<elab::Pattern> {
        match pat {
            core::Pattern::Ambiguous { candidates, reason } => {
                // Try each candidate, see which type-checks
                let mut valid = vec![];
                
                for candidate in candidates {
                    if let Ok(elab) = self.try_elab_pattern(candidate, expected_ty) {
                        valid.push(elab);
                    }
                }
                
                match valid.len() {
                    0 => Err(Error::NoValidParsing { 
                        candidates: candidates.clone(),
                        expected_ty: expected_ty.clone(),
                    }),
                    1 => Ok(valid.into_iter().next().unwrap()),
                    _ => Err(Error::AmbiguousPattern {
                        valid_parsings: valid,
                        help: "Add parentheses to disambiguate",
                    }),
                }
            }
            
            core::Pattern::Constructor { name, args } => {
                // Validate constructor is from expected type
                let ctor_ty = self.lookup_constructor(name)?;
                self.check_constructor_type(name, expected_ty)?;
                
                // Elaborate arguments
                let elab_args = self.elab_pattern_args(args, &ctor_ty)?;
                
                Ok(elab::Pattern::Constructor {
                    name: name.clone(),
                    args: elab_args,
                })
            }
            
            // ... other cases
        }
    }
}
```

---

## Impact on Implementation Timeline

### Changes to Original Plan

**Phase 4 (Bindings): 1.5 days → 1 day** ⬇️ -0.5 day
- **Simpler parser:** Just collect flat sequences, no precedence climbing
- **No operator parsing:** Parser doesn't try to determine structure
- **Result:** Easier to implement!

**New Phase: Scope Checker Operator Resolution: +2 days** ⬆️ +2 days
- Implement `find_applicable_operators()`
- Implement precedence graph building
- Implement precedence climbing with fixity info
- Handle ambiguous parsings (SPPF)
- **Location:** After parser complete, before elaborator

**Phase 8 (Match): 1.5 days → 1 day** ⬇️ -0.5 day
- Pattern grammar already implemented (flat sequences)
- Match just uses existing pattern parser

**Net change:** +1 day (21 days → 22 days)

---

## Updated Timeline

**New Total:** 22 days (4 weeks + 2 days)

**Breakdown:**
- **Week 1:** Foundation + Statements + Expressions (5 days)
- **Week 2:** Bindings (simpler!) + Inductive + Namespace + Error Recovery (5 days)
- **Week 3:** Match + Scope Checker (operator resolution) + Migration (6 days) ← +1 day here
- **Week 4:** Testing + Polish + Documentation (5 days)
- **+1 day:** Scope checker operator resolution

---

## Examples

### Example 1: Simple Constructor Pattern

**Input:**
```rust
fun (Cons x xs : List Nat) => ...
```

**Phase 1 (Parser):**
```rust
Pattern::AppSeq([Ident("Cons"), Ident("x"), Ident("xs")])
```

**Phase 2 (Scope Checker):**
```rust
// Lookup "Cons" → Constructor
// Result:
Pattern::Constructor {
    name: "Cons",
    args: [Pattern::Var("x"), Pattern::Var("xs")]
}
```

**Phase 3 (Elaborator):**
```rust
// Type-check against List Nat
// Validate Cons is constructor of List
// Success!
```

### Example 2: Mixfix Operator Pattern

**Input:**
```rust
inductive IfThenElse : Type where
  | if_then_else_ : Bool -> Nat -> Nat -> IfThenElse

fun (if true then 42 else 0 : IfThenElse) => ...
```

**Phase 1 (Parser):**
```rust
Pattern::AppSeq([
    Ident("if"), Ident("true"),
    Ident("then"), Ident("42"),
    Ident("else"), Ident("0")
])
```

**Phase 2 (Scope Checker):**
```rust
// Find operators in scope: if_then_else_
// Parts: ["if", "then", "else"]
// Match against sequence: ✅
// Result:
Pattern::MixfixOp {
    name: "if_then_else_",
    parts: ["if", "then", "else"],
    args: [Ident("true"), Ident("42"), Ident("0")]
}
```

**Phase 3 (Elaborator):**
```rust
// Type-check arguments:
// - true : Bool ✅
// - 42 : Nat ✅
// - 0 : Nat ✅
// Constructor type matches: ✅
```

---

## Next Steps

1. ✅ Update Pattern AST (remove Infix, add AppSeq)
2. ✅ Simplify parser (just collect sequences)
3. 🔄 Design scope checker operator resolution algorithm
4. 🔄 Implement precedence graph building
5. 🔄 Implement SPPF for ambiguous parsings
6. 🔄 Update elaborator to handle ambiguity

---

**Status:** 🚨 Critical revision in progress  
**Timeline:** 22 days (was 21 days, +1 day for scope checker)  
**Confidence:** 9.5/10 (correct approach, slightly more complex)  
**Key Achievement:** Parser is simpler! Complexity moves to scope checker where we have the information we need.
