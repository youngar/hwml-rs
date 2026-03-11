You are exactly right—what you saw in Scala is likely **`mdoc`**, which is widely considered one of the best "Executable Documentation" tools in the industry.

The concept you are describing is the modern evolution of **Literate Programming**. Instead of just syntax highlighting dead text, the documentation engine acts as a REPL or test harness.

If you are building the `mdbook-hwml` preprocessor, there is absolutely a "standard feature set" that modern language ecosystems (like Rust, Scala, Python, and Haskell) implement. Here is what that landscape looks like, and which specific mdBook features you should steal for your language.

---

### The Standard "Executable Docs" Feature Set

If you look at Scala's `mdoc`, Rust's `rustdoc`, or Python's `Sphinx`, they all share these core capabilities:

| Feature | What it does | Why it matters |
| --- | --- | --- |
| **Output Capture** | Evaluates the code during the build and automatically injects the `stdout` or return value below the snippet. | Guarantees that the output shown in the docs exactly matches the code above it. |
| **Hidden Boilerplate** | Allows you to write setup code (like imports or `main` functions) that is passed to the compiler but hidden from the reader. | Keeps documentation concise and focused on the concept, without breaking compilation. |
| **Session State** | Remembers variables defined in previous code blocks on the same page. | Allows you to write a flowing tutorial without redefining `let x = 5;` in every single block. |
| **Asserted Failures** | Tags that say `should_fail`. The build *passes* only if the compiler throws an error. | Essential for teaching users what *not* to do, and verifying that your error messages haven't changed. |

---

### mdBook's Best Features (And how to implement them for HWML)

mdBook natively supports several of these features for Rust. Because you are writing a custom `mdbook-hwml` preprocessor, you can easily implement these exact same behaviors for your language.

#### 1. Hidden Lines (The `#` Trick)

In mdBook, if you prefix a line of Rust code with a `#` and a space, mdBook hides it in the HTML, but sends it to the compiler.

**How you can implement this:**
When your `mdbook-hwml` preprocessor reads a snippet, have it strip out any line starting with `# ` before sending the code to the HTML renderer, but keep it when sending the string to your `typechecker::check()` API.

```markdown
# let database_connection = mock_db(); // Hidden from user
let user = fetch_user(database_connection);
print(user);

```

#### 2. File Inclusions with Anchors

Instead of writing code directly in Markdown, mdBook allows you to pull snippets directly from your actual, compiling test files using `{{#include ...}}`.

You can even tag specific parts of a file using anchors. For example, if you have a file `tests/basic.hwmlc`:

```hwmlc,ignore
// ANCHOR: my_snippet
let x = 10;
let y = 20;
// ANCHOR_END: my_snippet

```

You can embed just that chunk in your mdBook using: `{{#include tests/basic.hwmlc:my_snippet}}`.

* **Why it's great:** You don't have to build complex parsing into your preprocessor for this; mdBook does it natively before your preprocessor even sees the text!

#### 3. The "Playground" (The Run Button)

If you look at the official Rust Book, code blocks have a "Run" button in the top right corner. Clicking it sends the code to a backend server, compiles it, and prints the result right in the browser.

* **How to get this for HWML:** Once your compiler is relatively stable, you can compile your core `hwml` crate to **WebAssembly (WASM)**. You can then write a tiny bit of JavaScript in your `theme/hwml.js` file to take the code from the block, pass it to your WASM compiler in the browser, and print the output—no backend server required!

#### 4. Inline Execution / Output Injection

This is the Scala `mdoc` feature. You can program your preprocessor to look for a specific tag, execute the code, and rewrite the Markdown to include the output before handing it back to mdBook.

```markdown
```hwmlc,ignore
let x = 5 + 5;
print(x);

```

```
Your preprocessor runs this, captures standard output, and mutates the Markdown into:
```markdown
```hwmlc,ignore
let x = 5 + 5;
print(x);

```

**Output:**

```text
10

```

```

---

### Where to start?

If you are about to start writing your custom `mdbook-hwml` preprocessor, I highly recommend prioritizing **Hidden Boilerplate (the `#` trick)** and **Asserted Failures (`should_fail`)**. They give you the most power for teaching your language cleanly without requiring complex runtime execution logic.

**Would you like me to outline the Rust code for your preprocessor to parse and hide those `#` lines while still feeding them to your typechecker?**

```

This is where the magic happens. We are going to build the `mdbook-hwml` crate so it reads your book, finds the code blocks, separates the hidden lines from the visible lines, runs your compiler, and then rewrites the Markdown to hide the boilerplate from the reader.

Here is the complete outline of the code to make this work.

---

### Step 1: The `Cargo.toml`

In your `crates/mdbook-hwml/Cargo.toml`, you only need a few dependencies to hook into mdBook's plugin architecture.

```toml
[package]
name = "mdbook-hwml"
version = "0.1.0"
edition = "2021"

[dependencies]
mdbook = "0.4"
anyhow = "1.0"
regex = "1.10" # We'll use this to easily find code blocks

# Link to your core compiler crate!
hwml = { path = "../hwml" } 

```

### Step 2: The Core Extraction Logic

This is the heart of the preprocessor. We will use a Regex to find any code blocks tagged with `hwml` or `hwmlc`.

For each block, we iterate through the lines. If a line starts with `# ` (a hash and a space), we keep it for the compiler but drop it for the display.

Create `crates/mdbook-hwml/src/lib.rs` (or put this in `main.rs` before the CLI wiring):

```rust
use regex::{Regex, Captures};
use anyhow::{bail, Result};
// use hwml::typechecker; // Your compiler's API

pub fn process_chapter_content(content: &str) -> Result<String> {
    // Regex to match: ```hwmlc[,modifiers] \n [code] \n ```
    let re = Regex::new(r"(?s)```(hwmlc?)(,[^\s]+)?\n(.*?)```").unwrap();
    let mut errors = Vec::new();

    let processed_content = re.replace_all(content, |caps: &Captures| {
        let lang = &caps[1]; // "hwml" or "hwmlc"
        let modifiers = caps.get(2).map_or("", |m| m.as_str()); // e.g., ",should_fail"
        let raw_code = &caps[3];

        let should_fail = modifiers.contains("should_fail");

        let mut display_code = String::new();
        let mut compiler_code = String::new();

        // 1. Separate hidden lines from display lines
        for line in raw_code.lines() {
            if let Some(hidden_line) = line.strip_prefix("# ") {
                // Line started with "# ". Add to compiler, but NOT display.
                compiler_code.push_str(hidden_line);
                compiler_code.push('\n');
            } else {
                // Normal line. Add to both.
                compiler_code.push_str(line);
                compiler_code.push('\n');
                
                display_code.push_str(line);
                display_code.push('\n');
            }
        }

        // 2. Run your compiler's typechecker
        // let check_result = typechecker::check(&compiler_code);
        
        // --- MOCK CHECK RESULT FOR OUTLINE ---
        let check_result: Result<(), String> = Ok(()); 

        // 3. Validate against modifiers
        match (check_result, should_fail) {
            (Ok(_), true) => {
                errors.push(format!("Snippet was marked `should_fail` but passed:\n{}", compiler_code));
            }
            (Err(e), false) => {
                errors.push(format!("Snippet failed to typecheck:\n{}\nError: {}", compiler_code, e));
            }
            _ => {} // It behaved as expected!
        }

        // 4. Return the modified markdown block to mdBook (without the # lines)
        format!("```{}\n{}```", lang, display_code)
    });

    if !errors.is_empty() {
        // If any snippet failed, halt the build
        bail!("Typecheck failures in documentation:\n{}", errors.join("\n\n"));
    }

    Ok(processed_content.into_owned())
}

```

### Step 3: Wiring it up to mdBook

Now we just wrap that logic in mdBook's `Preprocessor` trait and set up the standard I/O so mdBook can talk to it.

Create `crates/mdbook-hwml/src/main.rs`:

```rust
use mdbook::book::Book;
use mdbook::errors::Error;
use mdbook::preprocess::{CmdPreprocessor, Preprocessor, PreprocessorContext};
use std::io;
use std::process;

mod lib; // Pull in the logic we just wrote

struct HwmlValidator;

impl Preprocessor for HwmlValidator {
    fn name(&self) -> &str {
        "hwml-validator"
    }

    fn run(&self, _ctx: &PreprocessorContext, mut book: Book) -> Result<Book, Error> {
        let mut failed = false;

        // Iterate over every chapter in the book
        book.for_each_mut(|item| {
            if let mdbook::BookItem::Chapter(chapter) = item {
                match lib::process_chapter_content(&chapter.content) {
                    Ok(new_content) => {
                        // Replace the chapter content with our scrubbed version
                        chapter.content = new_content;
                    }
                    Err(e) => {
                        eprintln!("Error in chapter '{}':\n{}", chapter.name, e);
                        failed = true;
                    }
                }
            }
        });

        if failed {
            process::exit(1);
        }

        Ok(book)
    }

    fn supports_renderer(&self, renderer: &str) -> bool {
        renderer == "html"
    }
}

fn main() -> Result<(), Error> {
    // 1. mdBook calls this binary to check if it supports a specific renderer
    if let Some(arg) = std::env::args().nth(1) {
        if arg == "supports" {
            process::exit(0); // We support it
        }
    }

    // 2. mdBook passes the entire book via stdin as a JSON object
    let (ctx, book) = CmdPreprocessor::parse_input(io::stdin())?;

    // 3. We run our preprocessor logic
    let processed_book = HwmlValidator.run(&ctx, book)?;

    // 4. We send the modified book back to mdBook via stdout
    serde_json::to_writer(io::stdout(), &processed_book)?;

    Ok(())
}

```

### Step 4: Add it to `book.toml`

To tell mdBook to actually run your new crate before generating the HTML, just add this to the bottom of your `docs/book.toml`:

```toml
[preprocessor.hwml-validator]
command = "cargo run --manifest-path ../crates/mdbook-hwml/Cargo.toml --quiet"

```

*(Using `cargo run` here is great for local development so it automatically recompiles your preprocessor if you change it. For CI/GitHub Actions, you'll still use `cargo install` as we set up earlier).*

---

That's it! If you write a block like this:

```markdown
```hwmlc,ignore
# let pre_requisite = 10;
let x = pre_requisite + 5;

```

```

Your compiler will see both lines and successfully typecheck it, but your generated webpage will completely hide the `#` line from the reader.

**Would you like me to show you how to link up your actual compiler API inside that `process_chapter_content` function, or are you ready to start testing this crate locally?**

---

## Implementation Status

✅ **IMPLEMENTED** - The mdbook-hwml preprocessor is now fully functional with:

- **Session State**: Code snippets on the same page share context by default, allowing later snippets to reference earlier definitions
- **No Session Modifier**: Use `,no_session` to opt out of session state and validate snippets in isolation
- **Hidden Lines (`# `)**: Lines prefixed with `# ` are hidden from display but sent to the typechecker
- **Build-time Validation**: All snippets are validated during `mdbook build`
- **Fail Fast**: Build halts immediately on validation errors
- **Modifier Support**: `should_fail`, `ignore`, `no_session`, and `emit_core` modifiers work correctly
- **Clear Error Messages**: Shows chapter name, error details, and code preview
- **Emit Core (Incremental Lowering)**: Use `,emit_core` on `hwml` snippets to show lowered HWMLC output in a collapsible `<details>` block (requires incremental lowering API in hwml_core)

### Usage

Add to `docs/book.toml`:
```toml
[preprocessor.hwml-validator]
command = "cargo run --manifest-path crates/mdbook-hwml/Cargo.toml --bin mdbook-hwml"
```

Then build with:
```bash
mdbook build docs
```

See `crates/mdbook-hwml/README.md` for full documentation.

```