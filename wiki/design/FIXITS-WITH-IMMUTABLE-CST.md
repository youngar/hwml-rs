# Fixits with Immutable CST

## Executive Summary

**We don't modify the CST!** Fixits generate **text edits** (LSP `TextEdit`) that describe changes to the source file. The LSP client applies these edits. The CST remains immutable and is re-parsed after edits.

This is how **all modern LSP implementations work**: rust-analyzer, TypeScript, Swift, Clang, etc.

---

## The Key Insight: Text Edits, Not Tree Mutations

### What We DON'T Do ❌
```rust
// WRONG: Mutate the tree
fn apply_fixit(tree: &mut SyntaxNode, fix: Fix) {
    tree.children[3] = new_node; // ❌ Violates immutability!
}
```

### What We DO ✅
```rust
// CORRECT: Generate text edits
fn fixit_to_text_edit(tree: &SyntaxNode, fix: Fix) -> TextEdit {
    // Find the node to replace
    let node = tree.find_node_at(fix.span);
    
    // Return a text edit describing the change
    TextEdit {
        range: Range::new(node.start_position(), node.end_position()),
        new_text: fix.replacement_text,
    }
}
```

**The workflow:**
1. Parse source → immutable CST
2. Run diagnostics → find errors
3. Generate fixits → compute text edits from CST
4. Send edits to LSP client
5. Client applies edits → modifies source file
6. Re-parse modified source → new immutable CST

---

## Architecture: Two Representations

### 1. Immutable CST (Internal - Compiler)
```rust
// Our CST - completely immutable
pub struct SyntaxNode {
    kind: SyntaxKind,
    text_range: Range<usize>,
    children: Arc<[SyntaxNode]>, // Immutable, shared
    trivia: Arc<Trivia>,
}

// Never modified - only created during parsing
```

### 2. Text Edits (External - LSP)
```rust
// What we send to the client
pub struct TextEdit {
    range: Range<Position>,  // Where to edit
    new_text: String,        // What to insert
}

// The client applies these to the actual source file
```

---

## How rust-analyzer Does It

rust-analyzer uses the **rowan** library with red-green trees:

### Green Tree (Immutable Data)
```rust
pub struct GreenNode {
    kind: SyntaxKind,
    text_len: TextSize,
    children: ThinArc<[GreenChild]>, // Shared, immutable
}
```

### Red Tree (Views with Parent Pointers)
```rust
pub struct SyntaxNode {
    green: GreenNode,    // Immutable data
    parent: Option<Arc<SyntaxNode>>,  // Parent pointer for navigation
    offset: TextSize,    // Absolute offset in file
}
```

### The Magic: SyntaxEditor
```rust
// rust-analyzer's approach for assists (code actions)
pub struct SyntaxEditor {
    original: SyntaxNode,     // Original immutable tree
    annotations: Vec<Annotation>,  // Tracked changes
}

impl SyntaxEditor {
    // Record an edit (doesn't modify tree!)
    pub fn replace(&mut self, node: &SyntaxNode, replacement: SyntaxNode) {
        self.annotations.push(Annotation::Replace {
            original: node.clone(),
            replacement,
        });
    }
    
    // At the end: compute text edits from annotations
    pub fn finish(self) -> Vec<TextEdit> {
        self.annotations.iter().map(|ann| match ann {
            Annotation::Replace { original, replacement } => {
                TextEdit {
                    range: original.text_range(),
                    new_text: replacement.to_string(),
                }
            }
        }).collect()
    }
}
```

**Key insight:** The tree is never mutated. We just track *what we want to change* and then compute text edits.

---

## HWML Implementation Strategy

### Phase 1: Simple Text-Based Fixits (Now)

**No tree mutation needed!** Just compute edits from spans:

```rust
// hwml-diagnostic/src/types.rs
pub enum Fix {
    Replace { range: Span, new_text: String },
    Insert { at: Position, text: String },
    Delete { range: Span },
}

// Conversion to LSP is trivial
impl Fix {
    pub fn to_lsp_edit(&self, uri: &Uri) -> TextEdit {
        match self {
            Fix::Replace { range, new_text } => TextEdit {
                range: span_to_lsp_range(range),
                new_text: new_text.clone(),
            },
            Fix::Insert { at, text } => TextEdit {
                range: Range::new(position_to_lsp(at), position_to_lsp(at)),
                new_text: text.clone(),
            },
            Fix::Delete { range } => TextEdit {
                range: span_to_lsp_range(range),
                new_text: String::new(),
            },
        }
    }
}
```

### Example: Type Mismatch Fixit
```rust
// In elab_error_to_diagnostic()
ElabError::TypeMismatch { expected, actual, span, .. } => {
    let diagnostic = Diagnostic {
        message: format!("Type mismatch: expected {}, found {}", 
            format_type(expected), format_type(actual)),
        span,
        suggestions: vec![
            Suggestion {
                message: "Add explicit type annotation".to_string(),
                fixes: vec![
                    // Find where to insert the annotation
                    Fix::Insert {
                        at: find_function_colon_position(span),
                        text: format!(": {}", format_type(expected)),
                    }
                ],
            }
        ],
        ..
    };
}
```

---

## Advanced: Tree-Guided Text Edits (Future)

When we have a full CST, we can use it to *compute better edits*, but still never mutate it:

```rust
pub struct FixitGenerator<'db> {
    tree: &'db SyntaxNode,  // Immutable reference
    source: &'db str,
}

impl<'db> FixitGenerator<'db> {
    // Use tree structure to find the right place to edit
    pub fn generate_type_annotation_fix(&self, span: Span) -> Fix {
        // Navigate the immutable tree
        let node = self.tree.find_node_at_offset(span.start.offset);
        let function = node.ancestors().find(|n| n.kind() == FUNCTION_DEF)?;
        let params = function.child(PARAM_LIST)?;
        
        // Compute where the annotation should go (after params, before body)
        let insert_pos = params.end_position();
        
        Fix::Insert {
            at: insert_pos,
            text: format!(": {}", format_type(ty)),
        }
    }
    
    // The tree guides us, but we return a text edit!
}
```

---

## Why This Works

1. **Separation of Concerns**
   - CST: Immutable, structural representation (internal)
   - Text Edits: Mutable operations on source file (external)

2. **LSP Protocol Design**
   - LSP was designed for this workflow
   - `TextEdit` is the fundamental primitive
   - Clients handle applying edits + re-parsing

3. **Performance**
   - Re-parsing is fast (incremental parsing with Salsa)
   - Sharing immutable CST nodes is cheap (Arc)
   - No need for complex tree mutation logic

4. **Correctness**
   - Immutability eliminates aliasing bugs
   - Text edits are simple to reason about
   - Testing is easy: `assert_eq!(apply_edits(source, edits), expected)`

---

## References

### rust-analyzer
- **SyntaxEditor**: https://github.com/rust-lang/rust-analyzer/pull/18032
- **Rowan library**: https://github.com/rust-analyzer/rowan
- **Red-Green trees**: https://rust-analyzer.github.io/book/contributing/syntax.html

### Swift
- **FixItApplier**: https://github.com/swiftlang/swift-syntax/pull/2467
- Applies edits to immutable syntax tree, returns String

### Clang
- **Code Tweaks**: https://github.com/llvm/llvm-project/commit/cce67a32cf822bf2a3520e256d92f4f0ba0dc6fe
- Two-stage: (1) Check availability, (2) Compute edits

---

## Conclusion

**We keep our CST immutable!** Fixits work by:
1. Analyzing the immutable CST to find errors
2. Computing text edits that would fix the errors
3. Sending edits to the LSP client
4. Client modifies source file
5. We re-parse to get new CST

This is the industry-standard approach used by all major LSP servers.
