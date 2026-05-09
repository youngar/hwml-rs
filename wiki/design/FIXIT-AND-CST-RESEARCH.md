# Fixits and CST Research

## Executive Summary

**CRITICAL: Fixits don't modify the CST!** They generate **text edits** that the LSP client applies to source files. The CST stays immutable.

**Recommendation:** Implement a **lossless Concrete Syntax Tree (CST) with trivia tokens** following the Roslyn/Swift model. This enables:
- **High-quality fixits** with preserved formatting
- **Better LSP features** (semantic highlighting, precise navigation)
- **Automated refactoring** (codemods)
- **Future-proof architecture** for IDE tooling

**See also:** `wiki/design/FIXITS-WITH-IMMUTABLE-CST.md` for detailed implementation strategy.

---

## 1. What Are Fixits?

Fixits (also called "code actions" or "quick fixes") are automated code transformations suggested by the compiler/IDE to fix errors or improve code.

### Examples:
```rust
// Error: Type mismatch
expected: Nat
found:    Bool

// Fixit offered:
1. Add explicit type conversion: nat_of_bool(value)
2. Change variable type to Bool
```

### LSP Protocol:
```json
{
  "title": "Add explicit type conversion",
  "kind": "quickfix",
  "edit": {
    "changes": {
      "file:///foo.hwml": [
        {
          "range": { "start": {"line": 5, "character": 10}, "end": {"line": 5, "character": 15} },
          "newText": "nat_of_bool(value)"
        }
      ]
    }
  }
}
```

---

## 2. Why CST with Trivia Tokens?

### AST (Abstract Syntax Tree) - What We Have Now
- **Loses formatting** - no whitespace, comments, parentheses
- **Hard to generate code** - can't preserve user's style
- **Fixits are ugly** - generated code doesn't match surrounding code

### CST (Concrete Syntax Tree) - Industry Best Practice
- **Preserves everything** - whitespace, comments, exact token positions
- **Lossless roundtripping** - `parse(print(tree)) == tree`
- **Format-preserving edits** - fixits look like human-written code
- **Better IDE features** - semantic highlighting, precise navigation

---

## 3. Industry Approaches

### A. Roslyn/Swift Model (RECOMMENDED)

**How it works:**
- Each token has `leading_trivia` and `trailing_trivia`
- Trivia = whitespace, comments, preprocessor directives
- Tree structure: `Token { leading: Vec<Trivia>, kind: TokenKind, trailing: Vec<Trivia> }`

**Example:**
```
// This is a comment
def foo := 42

Tokens:
  CommentToken { leading: [], kind: Comment("// This is a comment"), trailing: [Newline] }
  DefToken { leading: [], kind: Def, trailing: [Space] }
  IdentToken { leading: [], kind: Ident("foo"), trailing: [Space] }
  ColonEqualToken { leading: [], kind: ColonEqual, trailing: [Space] }
  NumberToken { leading: [], kind: Number(42), trailing: [Newline] }
```

**Advantages:**
- ✅ Simple data structure
- ✅ Efficient traversal (trivia attached to next token)
- ✅ Used by production compilers (Swift, Roslyn, rust-analyzer RFC)
- ✅ Easy to implement fixits (replace nodes, keep trivia)

**References:**
- Swift: https://github.com/swiftlang/swift-syntax/blob/main/Sources/SwiftSyntax/Trivia.swift
- Roslyn: https://learn.microsoft.com/en-us/dotnet/csharp/roslyn-sdk/work-with-syntax
- rust-analyzer RFC: https://github.com/rust-lang/rust-analyzer/issues/6584

### B. LibCST Model (Python)

**How it works:**
- Every node has `leading_lines`, `trailing_whitespace`, `whitespace_before_colon`, etc.
- Explicit trivia fields on nodes
- "Looks like AST, acts like CST"

**Advantages:**
- ✅ Very precise control over formatting
- ✅ Great for Python-specific patterns (indentation-based syntax)

**Disadvantages:**
- ❌ More complex data structures
- ❌ Language-specific (harder to generalize)

**Reference:** https://github.com/Instagram/LibCST

### C. Tree-sitter Model (External Parser)

**How it works:**
- Separate error-tolerant parser library
- Generates CST with all trivia
- Often used for syntax highlighting

**Disadvantages:**
- ❌ Reimplements the language parser (out of sync)
- ❌ Slower than native parser
- ❌ LSP still needs access to real parser for semantic analysis

---

## 4. Implementing Fixits Without CST (Current Approach)

We can still implement basic fixits using byte offsets and string manipulation:

### Approach 1: Range-Based Edits (What LSP Uses)
```rust
pub struct Fix {
    pub range: Range<usize>,  // Byte offsets
    pub replacement: String,
}

// Example: Replace "x" with "nat_of_bool(x)"
Fix {
    range: 42..43,
    replacement: "nat_of_bool(x)".to_string(),
}
```

**Limitations:**
- ❌ Can't preserve user's whitespace style
- ❌ Can't handle multi-line edits nicely
- ❌ Hard to compose multiple fixes

### Approach 2: AST-Based Suggestions (Text-Only)


1. **Extend `Fix` type in `hwml-diagnostic`**
   ```rust
   pub enum Fix {
       Replace { range: Span, new_text: String },
       Insert { at: Position, text: String },
       Delete { range: Span },
   }
   ```

2. **Add fixit generation to error conversion**
   ```rust
   // In elab_error_to_diagnostic()
   match error {
       TypeMismatch { expected, actual, .. } => {
           let mut suggestions = vec![];

           // Fixit: Add type annotation
           if can_infer_annotation(expected) {
               suggestions.push(Suggestion {
                   message: format!("Add type annotation: {}", format_type(expected)),
                   fixes: vec![Fix::Insert {
                       at: function_start,
                       text: format!(": {}", format_type(expected))
                   }],
               });
           }

           Diagnostic { ..., suggestions }
       }
   }
   ```

3. **LSP integration**
   ```rust
   // Convert Fix -> lsp_types::CodeAction
   pub fn fix_to_code_action(fix: &Fix, uri: &Uri) -> CodeAction {
       let edit = match fix {
           Fix::Replace { range, new_text } => {
               WorkspaceEdit { ... }
           }
           ...
       };

       CodeAction {
           title: suggestion.message.clone(),
           kind: Some(CodeActionKind::QUICKFIX),
           edit: Some(edit),
           ...
       }
   }
   ```

### Future: CST Migration

When we implement CST with trivia:

1. **Parser changes:**
   ```rust
   pub struct Token {
       leading_trivia: Vec<Trivia>,
       kind: TokenKind,
       trailing_trivia: Vec<Trivia>,
   }

   pub enum Trivia {
       Whitespace(String),
       LineComment(String),
       BlockComment(String),
       Newline,
   }
   ```

2. **Roundtrip property:**
   ```rust
   assert_eq!(
       print(parse(source)),
       source
   );
   ```

3. **Fixit generation becomes tree transformation:**
   ```rust
   // Replace node while preserving trivia
   fn replace_preserving_trivia(old: &SyntaxNode, new: SyntaxNode) -> SyntaxNode {
       let leading_match = old.leading_trivia() == new.leading_trivia();
       let trailing_match = old.trailing_trivia() == new.trailing_trivia();

       let mut result = new;
       if !leading_match {
           result = result.with_leading_trivia(old.leading_trivia().clone());
       }
       if !trailing_match {
           result = result.with_trailing_trivia(old.trailing_trivia().clone());
       }
       result
   }
   ```

---

## 7. Examples from Other Compilers

### Swift FixIt (with CST)
```swift
// Error: Cannot convert value of type 'String' to expected type 'Int'
let x: Int = "42"

// FixIt: Replace '"42"' with 'Int("42")'
// The fix preserves all formatting and just wraps the expression
```

### Rust rust-analyzer (transitioning to CST)
```rust
// Error: mismatched types: expected `u32`, found `i32`
let x: u32 = 42i32;

// Code action: Change type to i32
// Code action: Add type conversion: 42i32 as u32
```

### Python LibCST (automated refactoring)
```python
# Convert old-style to new-style class
class Foo:
    pass

# Transformed to:
class Foo(object):
    pass
# All formatting, comments, whitespace preserved
```

---

## 8. References

### Papers & Talks
- "Roslyn: The Journey to a Compiler Platform" (Microsoft, 2014)
- "Swift Syntax: A Concrete Syntax Tree for Swift" (Apple, 2019)
- "rust-analyzer: Incremental IDE-First Compiler" (Aleksey Kladov, 2020)

### Implementations
- Swift: https://github.com/swiftlang/swift-syntax
- Roslyn: https://github.com/dotnet/roslyn
- LibCST: https://github.com/Instagram/LibCST
- rust-analyzer: https://github.com/rust-lang/rust-analyzer

### LSP Specification
- Code Actions: https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_codeAction
- Workspace Edits: https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#workspaceEdit

---

## Conclusion

For HWML, we should:

1. **Now:** Implement basic fixits using byte offsets (Week 4-5)
   - Good enough for MVP
   - Provides immediate value to users
   - Foundation for future work

2. **Later:** Migrate to CST with trivia tokens (Post-MVP)
   - Industry best practice
   - Enables advanced IDE features
   - Better user experience for refactoring

The two-phase approach lets us deliver value quickly while building toward a production-quality solution.

```rust
pub struct Suggestion {
    pub message: String,
    pub fix: Option<Fix>,
}
```

**Good for:**
- ✅ Simple replacements ("change `x` to `y`")
- ✅ Insertions ("add `: Nat` annotation")
- ✅ Deletions ("remove unused variable")

**Not good for:**
- ❌ Complex refactorings (extract function, inline variable)
- ❌ Format-preserving transformations

---

## 5. Recommendation for HWML

### Phase 1: Basic Fixits (NOW - Week 4/5)
Implement fixits using the current AST + byte offsets:

```rust
pub enum Fix {
    Replace { range: Span, new_text: String },
    Insert { position: Position, text: String },
    Delete { range: Span },
}
```

**Implement for:**
- Type mismatches ("add type annotation", "convert to expected type")
- Name not in scope ("did you mean X?", "import from module Y")
- Missing patterns ("add missing match cases")

### Phase 2: CST with Trivia (FUTURE - Post-MVP)
Migrate to Roslyn-style CST when we need:
- **Automated refactoring** (extract function, inline, rename)
- **Format-preserving code generation**
- **Better IDE features** (semantic highlighting, folding regions)

---

## 6. Implementation Plan

### Week 4-5: Basic Fixits
