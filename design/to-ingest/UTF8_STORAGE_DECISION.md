# UTF-8 Storage Decision: Why Surface Syntax Can't Use Borrowed Slices

**Date:** 2026-05-06  
**Question:** Should surface syntax store `&'input [u8]` or `&'input str` instead of `Box<[u8]>`?

---

## TL;DR

**Answer: NO. Surface syntax MUST own the data.**

**Why:** The `Program` syntax tree **has no lifetime parameter** and **outlives** the input bytes. It can't borrow from the input.

---

## The Two Different Syntax Trees

### 1. **Surface Syntax** (`hwml-surface`) - NO LIFETIMES

```rust
// crates/hwml-surface/src/syntax.rs
pub struct Program {               // ← NO 'input lifetime!
    pub statements: Vec<Statement>,
}

pub struct Id {
    pub loc: Range<usize>,
    pub value: Box<[u8]>,          // ← MUST OWN DATA
}
```

**Cannot store:** `&'input [u8]` or `&'input str`  
**Reason:** No lifetime parameter, tree is returned from `parse()` function

### 2. **Core Syntax** (`hwml-core`) - HAS LIFETIMES

```rust
// crates/hwml-core/src/syn/syntax.rs
pub enum Syntax<'db> {             // ← HAS 'db lifetime!
    Constant(QualifiedName<'db>),  // ← Borrows from database
    Variable(Variable<'db>),
    // ...
}
```

**Can borrow:** From Salsa database via `'db` lifetime  
**Why:** Syntax is interned/managed by Salsa, always tied to database lifetime

---

## Lifetime Analysis

### Surface Parse Flow

```rust
// crates/hwml-surface/src/parsing.rs
pub fn parse(input: &[u8]) -> Option<Program> {
    //          ^^^^^^ 'input lifetime starts here
    let mut ctx = ParserContext::new(input);
    let lexer = Lexer::new(input);
    let parser = ProgramParser::new();
    let result = parser.parse(input, &mut ctx, lexer);
    match result {
        Ok(program) => Some(program),  // ← RETURNS Program (no lifetime!)
        //                 ^^^^^^^ 'input lifetime ENDS here!
        Err(err) => None,
    }
}  // ← input bytes dropped here, but Program outlives!
```

**The problem:**
```rust
// If Id stored &'input [u8]:
pub struct Id<'input> {  // Would need this!
    pub value: &'input [u8],
}

pub struct Program<'input> {  // And this!
    pub statements: Vec<Statement<'input>>,
}

// Then parse signature would be:
pub fn parse<'input>(input: &'input [u8]) -> Option<Program<'input>>
//           ^^^^^^                               ^^^^^^^^^^^^^^^^
//   Lifetime connects input to output - program borrows from input!
```

**But that breaks the design!**

The surface syntax is an **intermediate representation** that gets converted to core syntax:

```rust
// Typical usage (elaborator)
let surface_program = hwml_surface::parse(source_bytes);  // Parse once
// source_bytes can now be dropped!

// Later (maybe in a different function):
for stmt in surface_program.statements {  // ← Must still be valid!
    let core_syntax = elaborate(db, stmt);  // Convert to core
}
```

If `Program` borrowed from `source_bytes`, you'd have to keep the source alive for the entire elaboration, which is architecturally wrong.

---

## Why Core Syntax Can Use Lifetimes

Core syntax is tied to the **Salsa database**, which has a well-defined lifetime:

```rust
// Core syntax usage
pub fn elaborate<'db>(
    db: &'db dyn Database,
    surface: &SurfaceId,  // No lifetime - owned!
) -> RcSyntax<'db> {     // Borrows from 'db
    let name = QualifiedName::new(db, ...);  // Interned in db
    Syntax::constant_rc(name)  // Tied to db lifetime
}
```

**Key difference:**
- Surface: **Parse once, own the data, convert later**
- Core: **Tied to database, borrows from database, never leaves database**

---

## The Right Design: Validate at Lexer, Own in Surface, Unchecked Convert

### Current (Problematic)

```rust
// Lexer: No validation
Token::Identifier  // Can be invalid UTF-8

// Parser: Copies bytes
Id { value: Box::from(&input[l..r]) }  // Still no validation

// Elaborator: Silent masking
let text = String::from_utf8_lossy(&id.value);  // ❌ MASKS ERRORS
let word = Word::new(db, text.as_ref());
```

### Correct Design

```rust
// Lexer: VALIDATE UTF-8
impl Iterator for Lexer {
    fn next(&mut self) -> Option<(usize, Token, usize)> {
        match token {
            Ok(Token::Identifier) => {
                // ✅ VALIDATE HERE
                if std::str::from_utf8(slice).is_err() {
                    return Some((span.start, Token::Error, span.end));
                }
            }
        }
    }
}

// Parser: Own validated bytes (still as Box<[u8]>)
// INVARIANT: After successful parse, all Id.value are valid UTF-8
Id { value: Box::from(&input[l..r]) }  // ✅ Validated by lexer

// Elaborator: Unchecked conversion (SAFE!)
// SAFETY: Lexer guaranteed UTF-8 validity
let word = unsafe { Word::from_utf8_unchecked(db, &id.value) };
```

**Why keep `Box<[u8]>` instead of `Box<str>`?**

Because the LALRPOP grammar receives `input: &'input [u8]`, not `&'input str`:

```rust
// crates/hwml-surface/src/grammar.lalrpop
grammar<'input>(input: &'input [u8], ctx: &mut ParserContext);
//                     ^^^^^^^ Bytes, not str!

Id: Id = {
  <l:@L> <s:"id"> <r:@R> => {
    Id::new(l..r, Box::from(&input[l..r]))
    //                      ^^^^^^^^^^^^^ Slicing &[u8], not &str
  }
};
```

**Should we change to `Box<str>`?**

**YES!** This is actually better:
1. Lexer validates token-by-token (not the entire file upfront)
2. Parser slices and converts with `from_utf8_unchecked` (zero cost)
3. Surface syntax stores `Box<str>` (cleaner API, type-safe)
4. Elaborator uses `Box<str>` directly (no unsafe needed)

**Benefits:**
- Type safety: `Id.value` is guaranteed valid UTF-8 at compile time
- Cleaner API: Can call `.value.as_str()` instead of `from_utf8_unchecked(&.value)`
- Less unsafe: Only in parser (localized), not scattered across elaborator

---

## Comparison to Production Compilers

### rust-analyzer

rust-analyzer's **CST (Concrete Syntax Tree)** uses owned data:

```rust
// rust-analyzer/crates/syntax/src/ast.rs
pub struct SourceFile {
    syntax: SyntaxNode,  // Owns the tree
}

pub struct Name {
    text: SmolStr,  // Owned string (inline or Arc)
}
```

**No lifetimes!** The parse tree is **owned** and can outlive the input.

### GHC (Haskell)

GHC's parse tree also owns strings:

```haskell
data HsModule = HsModule {
    hsmodName :: Located ModuleName,  -- Located wraps position + value
    -- ...
}

newtype ModuleName = ModuleName FastString  -- Interned string (owned)
```

**No borrowing from input!** Strings are interned or owned.

---

## Proposed Changes

### 1. Change Surface Syntax to Use `Box<str>`

```rust
// crates/hwml-surface/src/syntax.rs
pub struct Id {
    pub loc: Range<usize>,
    pub value: Box<str>,  // ✅ CHANGE FROM Box<[u8]>
}

pub struct Num {
    pub loc: Range<usize>,
    pub value: Box<str>,  // ✅ CHANGE FROM Box<[u8]>
}
```

**Benefits:**
- Type-safe: Rust's type system guarantees UTF-8 validity
- Cleaner API: No need for `from_utf8()` conversions
- Safer: Less `unsafe` scattered across elaborator

### 2. Add Lexer Validation

```rust
// crates/hwml-surface/src/lex.rs
impl Iterator for Lexer {
    fn next(&mut self) -> Option<Self::Item> {
        match token {
            Ok(Token::Identifier) | Ok(Token::Number) => {
                // Validate UTF-8 for identifier tokens
                if std::str::from_utf8(slice).is_err() {
                    return Some((span.start, Token::Error, span.end));
                }
            }
            // ...
        }
    }
}
```

### 3. Update LALRPOP Grammar to Convert Unchecked

```rust
// crates/hwml-surface/src/grammar.lalrpop
Id: Id = {
  <l:@L> <s:"id"> <r:@R> => {
    // SAFETY: Lexer validated UTF-8 for Identifier token
    let text = unsafe { std::str::from_utf8_unchecked(&input[l..r]) };
    Id::new(l..r, text.into())
  }
};

Num: Num = {
  <l:@L> <s:"num"> <r:@R> => {
    // SAFETY: Lexer validated UTF-8 for Number token
    let text = unsafe { std::str::from_utf8_unchecked(&input[l..r]) };
    Num::new(l..r, text.into())
  }
};
```

### 4. Update Elaborator (No Unsafe Needed!)

```rust
// crates/hwml-elab/src/names.rs
pub fn bytes_to_simple_qname<'db>(
    db: &'db dyn salsa::Database,
    namespace: Option<QualifiedName<'db>>,
    segment: &str,  // ← Changed from &[u8]
) -> QualifiedName<'db> {
    let word = Word::new(db, segment);  // ← No unsafe!
    let atom = Atom::new(word);
    let name = Name::new(db, Fixity::Closed, Box::from([atom]));
    QualifiedName::new(db, namespace, name)
}

// Update all call sites:
bytes_to_simple_qname(db, namespace, &id.value)  // ← .value is now &str!
```

---

## Summary

| Question | Answer | Reason |
|----------|--------|--------|
| Can surface syntax store `&'input [u8]`? | **NO** | No lifetime parameter, outlives input |
| Can surface syntax store `&'input str`? | **NO** | No lifetime parameter, outlives input |
| Should we add lifetime to `Program<'input>`? | **NO** | Breaks separation: surface → core conversion |
| Should we store `Box<str>` instead of `Box<[u8]>`? | **YES!** | Type-safe, cleaner API, less unsafe code |
| Should we validate at lexer? | **YES** | Catches errors early with precise locations |
| Should we use unchecked conversion in parser? | **YES** | Safe because lexer validated, localized |

**Final design:**
```
Input [u8] → Lexer validates → Parser from_utf8_unchecked → Surface Box<str> → Word Box<str>
                UTF-8 ✓                    ↑ SAFE!            (type-safe!)      (no conversion!)
                                      (in LALRPOP grammar)
```

**Benefits:**
- ✅ **One** unsafe block per token type (in LALRPOP grammar)
- ✅ **Zero** unsafe in elaborator (works with `&str` directly)
- ✅ **Type system** enforces UTF-8 validity throughout pipeline
- ✅ Matches production compilers and respects the architecture
