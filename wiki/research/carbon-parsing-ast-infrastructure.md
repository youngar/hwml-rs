# Carbon Language: Parsing and AST Infrastructure

**Project:** Carbon Language (Google/Carbon)  
**Repository:** https://github.com/carbon-language/carbon-lang  
**Date Analyzed:** 2026-05-10  
**Confidence:** 0.95  
**Type:** Technical Survey  

---

## Executive Summary

Carbon implements a **three-phase compilation pipeline** (Lex → Parse → Check) with a **postorder parse tree**, **data-oriented CST architecture**, and **separate semantic IR**. Their approach prioritizes **error recovery**, **IDE support**, and **fast incremental compilation** through immutable data structures and clear phase separation.

### Key Architectural Choices

1. **Postorder Parse Tree**: Parse tree stored in postorder (depth-first) for efficient checking traversal
2. **Immutable CST**: Parse tree never modified after construction; fixits operate on separate data
3. **Flat Token/Node Storage**: Vectorized storage with index-based references (flyweight pattern)
4. **Lexer Bracket Matching**: Lexer handles `()`, `[]`, `{}` matching with recovery tokens
5. **Simple Autoformatter**: Token-stream-based formatter (no parse tree required for basic formatting)
6. **Semantic IR Separation**: Parse tree → Semantic IR (SemIR) → LLVM IR lowering

---

## 1. Lexing Architecture

### TokenizedBuffer Structure

**File:** `toolchain/lex/tokenized_buffer.h`

```cpp
class TokenizedBuffer {
  // Flat storage of tokens (postorder)
  llvm::SmallVector<TokenInfo> tokens_;
  
  // Separate storage for:
  // - Line information (LineInfo)
  // - Comments (CommentData, tracked separately from tokens)
  // - String/numeric literal values (in shared value stores)
  
  // Index-based handles (flyweight pattern)
  struct TokenIndex : IndexBase<TokenIndex>;
  struct LineIndex : IndexBase<LineIndex>;
  struct CommentIndex : IndexBase<CommentIndex>;
};
```

**Key Design Points:**

- **Comments excluded from token stream** to avoid special-casing in parser
- **Bracket matching in lexer** (`()`, `[]`, `{}`) with automatic recovery token insertion
- **Literal parsing at lex time** (strings, numbers) stored in shared value stores
- **Zero-based byte offsets** for all positions (see ADR-014-byte-level-location-tracking)

### Token Kinds (X-Macro Pattern)

**File:** `toolchain/lex/token_kind.def`

```cpp
// X-macro for extensibility
#define CARBON_TOKEN(Name)
#include "token_kind.def"

// Examples:
CARBON_TOKEN(Identifier)
CARBON_TOKEN(IntLiteral)
CARBON_TOKEN(Semi)
CARBON_TOKEN(OpenCurlyBrace)
```

Carbon uses **X-macros extensively** (`.def` files) for code generation across tokens, parse nodes, semantic instructions, and diagnostics.

---

## 2. Parse Tree Architecture

### Postorder Storage

**File:** `toolchain/docs/parse.md`

**Core Insight:** Parse tree stored in **postorder** (children before parents) for efficient checking:

```carbon
fn foo() -> f64 { return 42; }

// Postorder storage:
[FileStart, FunctionIntroducer(fn), Name(foo),
 ParamListStart('('), ParamList(')'),
 Literal(f64), ReturnType(->),
 FunctionDefinitionStart('{'),
 ReturnStatementStart(return), Literal(42), ReturnStatement(';'),
 FunctionDefinition('}'), FileEnd]
```

**Benefits:**
- **Single-pass checking**: Process nodes as encountered in postorder
- **Minimal context tracking**: Bracketing nodes signal start of subtrees
- **Cache-friendly**: Linear memory access pattern
- **Efficient production**: Nodes naturally produced in postorder during parsing

### Tree Structure

**File:** `toolchain/parse/tree.h`

```cpp
class Tree {
  llvm::SmallVector<NodeImpl> node_impls_;  // Flat postorder storage

  // Each node: NodeKind + TokenIndex + subtree_size + has_error flag
  // 1:1 correspondence: one node per token (on valid input)
};
```

### Bracketing Nodes Pattern

Nodes have either **fixed child count** or **bracketing node**:

```carbon
var x: i32 = y + 1;

// Structure:
var      // Bracketing (VariableIntroducer)
├─ x     // Name
├─ :     // PatternBinding (2 children: x, i32)
│  ├─ x
│  └─ i32
├─ =     // Separator (0 children)
├─ +     // InfixOp (2 children: y, 1)
│  ├─ y
│  └─ 1
└─ ;     // VariableDecl (root, brackets var)
```

---

## 3. Parse Node Kinds (X-Macro)

**File:** `toolchain/parse/node_kind.def`

Carbon uses **X-macros** (`.def` files) for code generation across system:

```cpp
// Categories with specialized handling
CARBON_PARSE_NODE_KIND(FileStart)
CARBON_PARSE_NODE_KIND(InvalidParse)         // Error recovery

// Operator macros generate multiple variants
CARBON_PARSE_NODE_KIND_INFIX_OPERATOR(Plus)  // → InfixOperatorPlus
CARBON_PARSE_NODE_KIND_PREFIX_OPERATOR(Star) // → PrefixOperatorStar
```

**Error Recovery:** Always produce structurally valid tree (correct child counts), mark `has_error=true`.

---

## 4. Parser State Machine

**File:** `toolchain/parse/state.def` (~200 states)

**Pattern:** Stack-based with documented grammar examples in comments:

```cpp
// if (c) { ... }
//  ^
//   1. ParenConditionAsIf
CARBON_PARSE_STATE(IfExprIf)

// if (c) { ... }
//    ^~~
//   1. Expr
//   2. IfExprConditionFinish
CARBON_PARSE_STATE(ParenConditionAsIf)
```

**Handler Pattern** (`toolchain/parse/handle_*.cpp`):

```cpp
// Tokens consumed out-of-order, saved in state, emitted later as parents
auto HandleFunctionReturnTypeFinish(Context& context) -> void {
  auto state = context.PopState();
  // Use saved -> token as parent after expr parsed
  context.AddNode(NodeKind::ReturnType, state.token,
                  state.subtree_start, state.has_error);
}
```

This achieves **postorder emission** while parsing left-to-right.

---

## 5. Autoformatting

**File:** `toolchain/format/formatter.cpp`

**Key Insight:** Simple token-stream formatter, **no parse tree required**!

```cpp
auto Formatter::Run() -> bool {
  for (auto token : tokens_->tokens()) {
    switch (tokens_->GetKind(token)) {
      case OpenCurlyBrace:
        PrepareForSpacedContent();
        *out_ << "{";
        RequireEmptyLine();
        indent_ += 2;
        break;
      case Semi:
        PrepareForPackedContent();
        *out_ << ";";
        RequireEmptyLine();
        break;
      default:
        PrepareForSpacedContent();
        *out_ << tokens_->GetTokenText(token);
    }
  }
}
```

**Trade-offs:**
- ✅ **Blazing fast** - no parse tree construction needed
- ✅ **Works on invalid code** - only needs valid tokens
- ✅ **Simple implementation** - ~100 LOC
- ❌ **Limited formatting** - no smart wrapping, semantic-aware layout
- ❌ **Future rewrite planned** - TODOs mention need for more sophistication

**HWML Implication:** Consider two-tier formatting (fast token-based + optional semantic-based).

---

## 6. Semantic Analysis (Check Phase)

### Semantic IR (SemIR)

**File:** `toolchain/sem_ir/file.h`

**Separate from Parse Tree:**

```cpp
class SemIR::File {
  // Semantic instructions (flat storage, like parse tree)
  ValueStore<InstId, Inst> insts_;

  // Type information
  ValueStore<TypeId, TypeInfo> types_;

  // Functions, classes, interfaces, etc.
  ValueStore<FunctionId, Function> functions_;
  ValueStore<ClassId, Class> classes_;

  // Constant evaluation results
  ConstantValueStore constant_values_;
};
```

**Instruction Kinds** (`toolchain/sem_ir/inst_kind.def`, ~150 kinds):

```cpp
CARBON_SEM_IR_INST_KIND(Assign)
CARBON_SEM_IR_INST_KIND(Call)
CARBON_SEM_IR_INST_KIND(FunctionDecl)
CARBON_SEM_IR_INST_KIND(ClassType)
// ... ~150 total
```

### Check Context

**File:** `toolchain/check/context.h`

**Traversal:** Processes parse tree in postorder using stacks:

```cpp
class Context {
  NodeStack node_stack_;                // Parse tree nodes being processed
  InstBlockStack inst_block_stack_;     // SemIR instruction blocks
  ScopeStack scope_stack_;              // Name scopes
  DeclNameStack decl_name_stack_;       // Declaration name resolution

  // Processes parse tree postorder -> emits SemIR instructions
  auto ProcessNodeId(Parse::NodeId node_id) -> SemIR::InstId;
};
```

**Handler Dispatch** (`toolchain/check/handle_*.cpp`):

```cpp
// ~100 handler files, one per language feature
handle_function.cpp
handle_class.cpp
handle_var.cpp
// ... dispatched by parse node kind
```

---

## 7. Diagnostics Infrastructure

**File:** `toolchain/diagnostics/diagnostic.h`

### Diagnostic Macro System

```cpp
// Define diagnostics with formatting
CARBON_DIAGNOSTIC(InvalidCode, Error, "code is invalid");
CARBON_DIAGNOSTIC(TypeMismatch, Error,
                  "expected type {0}, found {1}", TypeId, TypeId);

// Emit with location
emitter.Emit(location, InvalidCode);
emitter.Emit(node_id, TypeMismatch, expected_ty, actual_ty);
```

**Diagnostic Registry** (`toolchain/diagnostics/kind.def`):

```cpp
// All diagnostic kinds in one place for tooling
CARBON_DIAGNOSTIC_KIND(InvalidCode)
CARBON_DIAGNOSTIC_KIND(TypeMismatch)
// ... ~400 total diagnostics
```

### Diagnostic Levels

```cpp
enum class Level {
  LocationInfo,    // "in import" context
  Note,            // Additional information
  SoftContext,     // Fallback context (discarded if better context exists)
  Context,         // High-level operation (steals diagnostic level)
  Warning,         // Likely problem
  Error            // Invalid program
};
```

**Key Pattern:** **Context-stealing**: First `Context` message becomes primary diagnostic, original becomes `Note`.

### Sorting Consumer

**File:** `toolchain/diagnostics/sorting_consumer.h`

**Problem:** Postorder checking produces diagnostics out-of-file-order.

**Solution:** Buffer and sort by `last_byte_offset` (maintains causality):

```cpp
// Balance competing needs:
// 1. Causal order (fix A before B if A causes B)
// 2. Human-understandable order (follow file flow)
// 3. Performance (zero overhead on correct code)

class SortingConsumer {
  // Sort by last_byte_offset (maintains causal order)
  // On-scope diagnostics sorted by start position when tied
  auto Flush() -> void {
    std::stable_sort(diagnostics_.begin(), diagnostics_.end(),
                     CompareByByteOffset);
  }
};
```

---

## 8. Fixits and Code Actions

**Question:** How do fixits work with immutable CST?

**Answer:** Fixits are **separate from parse tree**, stored in diagnostics:

**File:** `toolchain/diagnostics/diagnostic.h`

```cpp
struct Message {
  Kind kind;
  Level level;
  Loc loc;                          // Location in source
  llvm::StringLiteral format;       // Diagnostic message
  llvm::SmallVector<llvm::Any> format_args;  // For tooling inspection

  // Fixits are diagnostic annotations, not tree mutations
  // LSP/IDE constructs edits from diagnostic info
};
```

**Pattern:**
1. Emit diagnostic with suggested fix text in message
2. LSP layer (`toolchain/language_server/`) constructs `TextEdit` from diagnostic
3. Parse tree remains immutable

**HWML Lesson:** Fixits as diagnostic metadata, not tree operations.

---

## 9. Syntax Tree Walking Patterns

### Visitor Pattern (Not Used!)

Carbon **does NOT use visitor pattern**. Instead:

**Pattern 1: Postorder Iteration**

```cpp
for (auto node_id : parse_tree.postorder()) {
  switch (parse_tree.node_kind(node_id)) {
    case NodeKind::FunctionDefinition:
      HandleFunctionDefinition(node_id);
      break;
    case NodeKind::VarDecl:
      HandleVarDecl(node_id);
      break;
  }
}
```

**Pattern 2: Recursive Descent (Checking)**

```cpp
// Check phase processes nodes recursively
auto ProcessNodeId(Parse::NodeId node_id) -> SemIR::InstId {
  switch (parse_tree_.node_kind(node_id)) {
    case NodeKind::BinaryOperator:
      auto lhs = ProcessNodeId(GetChild(node_id, 0));
      auto rhs = ProcessNodeId(GetChild(node_id, 1));
      return EmitBinaryOp(lhs, rhs);
  }
}
```

**Why No Visitor?**
- Flat storage makes iteration trivial
- Postorder ensures children processed before parents
- Context stacks track state instead of visitor callbacks

---

## 10. Key Design Principles

### From Documentation Review

1. **Phase Separation is Sacred**
   - Lex: Only tokenize + bracket match
   - Parse: Only syntax structure, no name lookup
   - Check: All semantics (types, names, validity)

2. **Error Recovery Over Rejection**
   - Always produce structurally valid tree
   - Mark errors, continue parsing
   - Useful for IDEs/formatters on invalid code

3. **Immutability for Tools**
   - Parse tree never modified after construction
   - Enables caching, incremental compilation
   - Tools can snapshot without worrying about mutations

4. **Data-Oriented Design**
   - Flat vectorized storage (cache-friendly)
   - Index-based references (flyweight pattern)
   - Separate data by access pattern

5. **X-Macros for Extensibility**
   - Single source of truth (`.def` files)
   - Generated dispatch tables, formatters, visitors
   - Ensures consistency across tooling

---

## 11. Implications for HWML

### Direct Applicable Lessons

1. **Postorder CST Storage**
   - Adopt flat postorder storage for cache efficiency
   - Use bracketing nodes for variable-length subtrees
   - Reserve subtree_size in node representation

2. **X-Macro Infrastructure**
   - Use `.def` files for node kinds, tokens, diagnostics
   - Generate dispatch tables automatically
   - Single source of truth for tooling

3. **Lexer-Level Bracket Matching**
   - Move bracket matching to lexer with recovery
   - Simplifies parser, improves error messages

4. **Immutable CST + Separate Fixits**
   - Never mutate parse tree after construction
   - Fixits as diagnostic metadata
   - Enables safe caching/sharing

5. **Context-Stealing Diagnostics**
   - Adopt `Context` level for high-level operations
   - First context becomes primary message
   - Better diagnostic narratives

### Differences from HWML Needs

1. **Carbon has simpler syntax** (no mixfix, no significant whitespace)
   - HWML needs more complex precedence handling
   - Consider Beneš variational approach (see `benes-flow-variational-overloading.md`)

2. **Carbon doesn't have provenance tracking**
   - HWML needs elaborate→core→semantic provenance
   - See `provenance-deep-dive.md` for requirements

3. **Carbon's formatter is intentionally simple**
   - HWML may need semantic-aware formatting (e.g., align hardware assignments)
   - Consider two-tier: fast token-based + optional semantic

4. **Carbon separates Check from Lower**
   - HWML combines elaboration+typechecking
   - Check phase could be split into Elab + Check

---

## 12. Architecture Diagram

```
Source Text
    ↓
┌───────────────┐
│  Lex Phase    │  → TokenizedBuffer (flat, postorder-ish)
└───────────────┘       - Comments separate
    ↓                   - Brackets matched
┌───────────────┐       - Literals parsed
│ Parse Phase   │  → Parse Tree (flat, postorder, immutable)
└───────────────┘       - 1:1 with tokens
    ↓                   - Bracketing nodes
┌───────────────┐       - Error nodes
│ Check Phase   │  → Semantic IR (flat, instruction-based)
└───────────────┘       - Types resolved
    ↓                   - Names bound
┌───────────────┐       - Constants evaluated
│ Lower Phase   │  → LLVM IR
└───────────────┘

   Diagnostics (all phases → SortingConsumer → Console)
```

---

## 13. References

**Primary Sources:**
- `external/carbon-lang/toolchain/docs/parse.md` - Parse tree architecture
- `external/carbon-lang/toolchain/docs/lex.md` - Lexer design
- `external/carbon-lang/toolchain/docs/diagnostics.md` - Diagnostic system
- `external/carbon-lang/toolchain/parse/tree.h` - Core CST structure
- `external/carbon-lang/toolchain/lex/tokenized_buffer.h` - Token storage

**Code:**
- `external/carbon-lang/toolchain/parse/*.def` - Grammar definitions
- `external/carbon-lang/toolchain/check/handle_*.cpp` - Semantic handlers (~100 files)
- `external/carbon-lang/toolchain/format/formatter.cpp` - Simple autoformatter

**Related HWML Research:**
- [[benes-flow-variational-overloading]] - For complex precedence/overloading
- [[provenance-deep-dive]] - For source tracking through elaboration
- [[DATA-ORIENTED-CST-ARCHITECTURE]] - HWML's CST design decisions

---

**Status:** ✅ Complete technical survey
**Next Steps:**
1. Apply postorder CST design to HWML parser
2. Implement X-macro infrastructure for node kinds
3. Design fixit system compatible with immutable CST
4. Evaluate two-tier formatting strategy
