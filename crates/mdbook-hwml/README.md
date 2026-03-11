# mdbook-hwml

A first-class mdBook preprocessor for HWML language documentation that validates code snippets and hides boilerplate during the build process.

## Features

### ✅ Build-time Validation
All `hwml` and `hwmlc` code snippets are type-checked during `mdbook build`. If any snippet fails validation, the build halts with clear error messages.

### ✅ Session State (Incremental Definitions)
By default, code snippets on the same page share context. Later snippets can reference definitions from earlier ones, allowing you to build up examples incrementally without repeating boilerplate.

Use the `,no_session` modifier to opt out and validate a snippet in isolation.

### ✅ Hidden Lines (Boilerplate Hiding)
Lines prefixed with `# ` (hash + space) are:
- **Sent to the typechecker** (so the code compiles)
- **Hidden from readers** (keeping docs clean and focused)

This is the same pattern used by Rust's `rustdoc`.

### ✅ Asserted Failures
Mark snippets with `,should_fail` to verify that invalid code produces the expected errors.

### ✅ Ignored Snippets
Mark snippets with `,ignore` to skip type-checking for future features or incomplete examples.

### 🚧 Emit Core (Incremental Lowering)
Mark `hwml` snippets with `,emit_core` to show the lowered HWMLC (core language) output in a collapsible `<details>` block. Only the current snippet's lowered output is shown, not the accumulated session history.

**Note:** This feature requires the incremental lowering API in `hwml_core` to be implemented. Currently, it will generate an error message indicating the feature is not yet available.

## Usage

### Installation

Add to your `book.toml`:

```toml
[preprocessor.hwml-validator]
command = "cargo run --manifest-path crates/mdbook-hwml/Cargo.toml --bin mdbook-hwml"
```

### Examples

#### Session State (Incremental Definitions)

```markdown
First, define a type:
\```hwmlc
prim $Nat : U0;
prim $zero : $Nat;
\```

Then use it in later snippets:
\```hwmlc
const @Zero : $Nat = $zero;
const @One : $Nat = $zero;
\```

Continue building on those definitions:
\```hwmlc
const @Two : $Nat = @Zero;
\```
```

All three snippets are type-checked together. Later snippets can reference earlier definitions.

#### No Session (Isolated Validation)

```markdown
\```hwmlc,no_session
prim $Bit : U0;
prim $zero_bit : $Bit;
const @BitZero : $Bit = $zero_bit;
\```
```

This snippet is validated in isolation, ignoring any previous definitions on the page.

#### Hidden Lines

```markdown
\```hwmlc
# prim $Nat : U0;
# prim $zero : $Nat;
const @Zero : $Nat = $zero;
const @One : $Nat = $zero;
\```
```

**Readers see:**
```hwmlc
const @Zero : $Nat = $zero;
const @One : $Nat = $zero;
```

**Typechecker sees:**
```hwmlc
prim $Nat : U0;
prim $zero : $Nat;
const @Zero : $Nat = $zero;
const @One : $Nat = $zero;
```

#### Should Fail

```markdown
\```hwmlc,should_fail
const @InvalidNoType;
\```
```

The build will **pass** only if this snippet fails type-checking.

#### Ignore

```markdown
\```hwmlc,ignore
const @FutureFeature : $NotYetImplemented = $undefined;
\```
```

This snippet is skipped during validation.

#### Emit Core (Incremental Lowering)

```markdown
\```hwml,emit_core
def x : Bit := 0
\```
```

When the incremental lowering API is implemented, this will generate:

```markdown
\```hwml
def x : Bit := 0
\```

<details>
<summary><b>Lowered HWMLC (Core)</b></summary>

\```hwmlc
const @x : $Bit = $zero;
\```
</details>
```

The lowered code is shown in a collapsible section, allowing readers to optionally see the core language representation.

## Architecture

- **`src/lib.rs`**: Core extraction and validation logic
  - `extract_snippets()`: Parses markdown and extracts code blocks
  - `separate_hidden_lines()`: Splits display code from compiler code
  - `typecheck_snippet_hwmlc()`: Validates core language snippets in isolation
  - `typecheck_snippet_hwmlc_accumulated()`: Validates snippets with accumulated session state
  - `lower_incremental()`: Lowers hwml snippets to hwmlc incrementally (stub for future implementation)
  - `process_chapter_content()`: Main preprocessor logic with session state management and emit_core support

- **`src/main.rs`**: mdBook preprocessor binary
  - Implements `Preprocessor` trait
  - Handles JSON I/O with mdBook
  - Halts build on validation failures

## Test Coverage

The preprocessor has comprehensive test coverage with 11 passing tests:

1. **`test_extract_hwml_snippet`**: Verifies hwml code block extraction
2. **`test_extract_hwmlc_snippet`**: Verifies hwmlc code block extraction
3. **`test_extract_should_fail_snippet`**: Tests should_fail modifier parsing
4. **`test_extract_multiple_snippets`**: Tests multiple code blocks in one document
5. **`test_extract_with_hidden_lines`**: Tests hidden line extraction
6. **`test_hidden_lines`**: Tests hidden line separation (`# ` prefix)
7. **`test_ignore_other_languages`**: Tests non-HWML code blocks are ignored
8. **`test_process_chapter_with_hidden_lines`**: Integration test for hidden lines
9. **`test_session_state`**: Tests session state across multiple snippets
10. **`test_no_session_modifier`**: Tests no_session modifier isolation
11. **`test_emit_core_modifier`**: Tests emit_core modifier parsing and error handling

Run tests with:
```bash
cargo test -p mdbook-hwml
```

## Error Messages

When a snippet fails validation, you'll see:

```
❌ Validation errors in chapter 'Getting Started':

Snippet failed type-checking:
  Parse error: unexpected token
  Code:
    1: const InvalidNoType;;
```

## Development

Run tests:
```bash
cargo test -p mdbook-hwml
```

Build the preprocessor:
```bash
cargo build -p mdbook-hwml
```

Build the documentation (with validation):
```bash
mdbook build docs
```

## Design Philosophy

This preprocessor follows the "executable documentation" pattern pioneered by:
- Scala's `mdoc`
- Rust's `rustdoc`
- Python's `Sphinx`

Code examples in documentation should be **guaranteed to work**, not just syntax-highlighted text.

