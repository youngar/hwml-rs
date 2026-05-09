# Diagnostic & FixIt Implementation Summary

## Quick Reference

### Documents
1. **FIXITS-WITH-IMMUTABLE-CST.md** - How to implement fixits without mutating the CST ⭐ READ FIRST
2. **DATA-ORIENTED-CST-ARCHITECTURE.md** - Cache-perfect flat token arrays + error recovery 🚀 PERFORMANCE
3. **FIXIT-AND-CST-RESEARCH.md** - Industry research on fixits and CST approaches
4. **DIAGNOSTIC-IMPLEMENTATION-PLAN-REVISED.md** - 6-week diagnostic framework plan

---

## Key Principles

### 1. CST Remains Immutable ✅
```
Source File → Parse → Immutable CST → Analyze → Generate TextEdits
                                                          ↓
                         LSP Client ← Send Edits ←────────┘
                              ↓
                         Apply Edits
                              ↓
                         Modified Source → Re-parse → New CST
```

**We NEVER mutate the CST!** Fixits are text edits sent to the LSP client.

### 2. Fixits Are Text Edits
```rust
pub enum Fix {
    Replace { range: Span, new_text: String },
    Insert { at: Position, text: String },
    Delete { range: Span },
}

// Converted to LSP TextEdit
pub struct TextEdit {
    range: Range<Position>,
    new_text: String,
}
```

### 3. Industry Standard Approach
- **rust-analyzer**: Uses `SyntaxEditor` to track edits, generates `TextEdit`s
- **Swift**: `FixItApplier` applies edits to immutable tree, returns String
- **Clang**: Two-stage tweaks (check availability, compute edits)
- **TypeScript**: Code actions generate workspace edits

### 4. Data-Oriented Performance Secret 🚀
- **Pre-lex entire file** into flat `[Token]` array (8 bytes each)
- **Absolute byte offsets** prevent cascading span corruption
- **Panic Mode + Poison Nodes** for error recovery without Red/Green trees
- **Cache-line perfection**: CPU prefetcher streams tokens into L1 cache
- **Result**: 2-10x faster parsing (like Zig and V compilers)

---

## Implementation Phases

### Phase 1: Basic Fixits with AST (Week 4-5)
**Current approach - good enough for MVP**

```rust
// In hwml-db/src/diagnostics.rs
fn elab_error_to_diagnostic(error: &ElabError) -> Diagnostic {
    match error {
        ElabError::TypeMismatch { expected, actual, span, .. } => {
            Diagnostic {
                message: format!("expected {}, found {}", expected, actual),
                span,
                suggestions: vec![
                    Suggestion {
                        message: "Add type annotation".to_string(),
                        fixes: vec![
                            Fix::Insert {
                                at: find_annotation_position(span),
                                text: format!(": {}", format_type(expected)),
                            }
                        ],
                    }
                ],
                ..
            }
        }
    }
}
```

**What we can fix:**
- Type mismatches → "Add type annotation" / "Convert type"
- Name not in scope → "Did you mean X?" / "Import from module"
- Missing patterns → "Add missing match cases"

### Phase 2: CST with Trivia (Post-MVP)
**Better quality, format-preserving edits**

```rust
// With CST, we can navigate structure to find exact positions
pub struct FixitGenerator<'db> {
    tree: &'db SyntaxNode,  // Immutable
}

impl<'db> FixitGenerator<'db> {
    pub fn add_type_annotation(&self, ty: &Ty) -> Fix {
        let node = self.tree.find_function_at(span);
        let insert_pos = node.find_child(PARAM_LIST)
            .map(|p| p.end_position())
            .unwrap();
        
        Fix::Insert {
            at: insert_pos,
            text: format!(": {}", format_type(ty)),
        }
    }
}
```

**What we gain:**
- Format-preserving edits (respects user's whitespace)
- Complex refactorings (extract function, inline variable)
- Better suggestions (analyzes structure, not just text)

---

## Example Flow

### User sees error:
```
error: Type mismatch
  expected: Nat
  found:    Bool
  at main.hwml:10:15

  Suggested fixes:
  1. Add type annotation: `: Bool`
  2. Convert to Nat: `nat_of_bool(value)`
```

### LSP Code Action:
```json
{
  "title": "Add type annotation: `: Bool`",
  "kind": "quickfix",
  "edit": {
    "changes": {
      "file:///main.hwml": [
        {
          "range": {"start": {"line": 9, "character": 20}, "end": {"line": 9, "character": 20}},
          "newText": ": Bool"
        }
      ]
    }
  }
}
```

### Client applies edit:
```diff
-def foo(x) := x + 1
+def foo(x: Bool) := x + 1
```

### Re-parse:
```
Parse → New CST → Re-analyze → Different error or success!
```

---

## Code Structure

```
hwml-diagnostic/
├── src/
│   ├── types.rs          # Fix, Suggestion, Diagnostic
│   ├── lsp.rs            # diagnostic_to_lsp(), fix_to_code_action()
│   └── ...

hwml-db/
└── src/
    └── diagnostics.rs    # elab_error_to_diagnostic()
                          # Generates Diagnostic with Fix suggestions

hwml-lsp-server/
└── src/
    └── main.rs           # Server::compile_file()
                          # Sends diagnostics with code actions to client
```

---

## Testing Strategy

```rust
#[test]
fn test_type_annotation_fixit() {
    let source = "def foo(x) := x + 1";
    let diagnostic = analyze(source);
    
    assert_eq!(diagnostic.suggestions.len(), 1);
    let fix = &diagnostic.suggestions[0].fixes[0];
    
    assert_eq!(
        apply_fix(source, fix),
        "def foo(x: Nat) := x + 1"
    );
}
```

---

## References

- **FIXITS-WITH-IMMUTABLE-CST.md** - Detailed implementation guide
- **FIXIT-AND-CST-RESEARCH.md** - Industry research and best practices
- rust-analyzer: https://github.com/rust-lang/rust-analyzer
- Swift FixItApplier: https://github.com/swiftlang/swift-syntax
- LSP Code Actions: https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_codeAction
