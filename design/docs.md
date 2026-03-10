Building this bottom-up is the most robust way to approach the problem. A bottom-up strategy means we start with the smallest, most independent piece—your compiler's internal API—and build layers on top of it until we reach the final, user-facing website.

Here is a 5-phase plan to implement a type-checked Markdown guide for your language.

---

### Phase 1: Expose a Clean Compiler API (The Foundation)

Before we touch Markdown or `mdbook`, your compiler needs to be able to accept an isolated string of code, run it through the front-end (lexer, parser, typechecker), and return a simple pass/fail result.

1. **Decouple file I/O:** Ensure your parsing and typechecking logic takes a `&str` (the source code) rather than a file path.
2. **Create a Validation Function:** In your compiler's library (`src/lib.rs`), create a dedicated entry point for testing snippets.
```rust
pub fn typecheck_snippet(source: &str) -> Result<(), Vec<String>> {
    // 1. Lex
    // 2. Parse
    // 3. Typecheck
    // Return Ok(()) if it passes, or a list of error strings if it fails.
}

```



### Phase 2: Build the Markdown Extractor (The Bridge)

Next, we need a way to pull code blocks out of raw text. We will do this as a standalone utility module inside your compiler's test directory so it can be used independently of `mdbook`.

1. Add `pulldown-cmark` to your `[dev-dependencies]` in `Cargo.toml`.
2. Create a utility function that parses Markdown and yields the snippets.
```rust
// A simple struct to hold the code and whether we expect it to fail
pub struct Snippet {
    pub code: String,
    pub should_fail: bool,
}

pub fn extract_mylang_snippets(markdown: &str) -> Vec<Snippet> {
    // Use pulldown-cmark to iterate over markdown events,
    // look for Fenced Code Blocks tagged with "mylang",
    // and check if they also have the "should_fail" modifier.
}

```



### Phase 3: The `cargo test` Integration (The Validation)

Before making a whole website, let's make sure broken documentation fails your standard CI pipeline. We will write an integration test.

1. Create `tests/doc_tests.rs`.
2. Add the `walkdir` crate to easily find all Markdown files in your future `docs/` folder.
3. Write a test that glues Phase 1 and Phase 2 together:
* Iterate through every `.md` file.
* Read the file to a string.
* Pass it to `extract_mylang_snippets`.
* For each snippet, pass `snippet.code` to `typecheck_snippet()`.
* Use `assert!` to verify that normal snippets return `Ok` and `should_fail` snippets return `Err`.



### Phase 4: Setting up mdBook and the Preprocessor (The UI)

Now that your documentation is guaranteed to be correct via `cargo test`, it's time to generate the website.

1. **Initialize the book:** Run `mdbook init docs` and outline your `SUMMARY.md`.
2. **Create the Preprocessor:** Create a new binary target in your workspace (e.g., `mdbook-mylang`).
3. **Implement the mdBook traits:** Use the `mdbook` crate (as a dependency) to read the JSON stream that `mdbook build` sends via standard input.
4. **Hook in the Extractor:** Have the preprocessor use the exact same `extract_mylang_snippets` and `typecheck_snippet` logic from Phases 1 and 2. If it finds a type error, it prints it to `stderr` and panics, halting the `mdbook build` process.

### Phase 5: Custom Syntax Highlighting (The Polish)

The final step is making sure your verified code looks great in the browser.

1. Create a `theme/` directory in your `docs/` folder.
2. Write a custom `highlight.js` grammar for your language.
3. Configure `book.toml` to include your custom `highlight.js` file so it overrides the default web assets.

---

### Where to begin?

By starting at the bottom, you never have to wrestle with the complexities of `mdbook`'s plugin system until your core snippet-extraction and typechecking logic is fully tested and proven.

**Would you like to start with Phase 1 by sketching out your compiler's validation API, or would you prefer to dive straight into Phase 2 and look at the `pulldown-cmark` Rust code for extracting snippets?**

Hosting your mdBook on GitHub is completely free and incredibly easy using **GitHub Pages** combined with **GitHub Actions**.

The modern approach doesn't even require you to commit your generated HTML to your repository. Instead, every time you push to the `main` branch, a GitHub Action will automatically build your book and deploy it to your website.

Here is the step-by-step guide to setting it up.

---

### Step 1: Create the GitHub Actions Workflow

In the root of your project repository, create a new file at this exact path:
`.github/workflows/deploy.yml`

Paste the following YAML into that file. This tells GitHub exactly how to install `mdbook`, build your site, and publish it:

```yaml
name: Deploy mdBook to GitHub Pages

on:
  # Runs on pushes targeting the default branch
  push:
    branches: ["main"]

  # Allows you to run this workflow manually from the Actions tab
  workflow_dispatch:

# Sets permissions of the GITHUB_TOKEN to allow deployment to GitHub Pages
permissions:
  contents: read
  pages: write
  id-token: write

# Allow only one concurrent deployment, skipping runs queued between the run in-progress and latest queued.
concurrency:
  group: "pages"
  cancel-in-progress: false

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Setup mdBook
        uses: peaceiris/actions-mdbook@v2
        with:
          mdbook-version: 'latest'
          
      # If you wrote a custom preprocessor (like mdbook-mylang), 
      # you would add a step here to `cargo install` it.

      - name: Build with mdBook
        run: mdbook build
        # Assuming your book is in the root directory. If it's in a `docs/` folder, 
        # change this to `mdbook build docs/`

      - name: Upload artifact
        uses: actions/upload-pages-artifact@v3
        with:
          path: ./book # Or ./docs/book if your book is in a docs/ folder

  deploy:
    environment:
      name: github-pages
      url: ${{ steps.deployment.outputs.page_url }}
    runs-on: ubuntu-latest
    needs: build
    steps:
      - name: Deploy to GitHub Pages
        id: deployment
        uses: actions/deploy-pages@v4

```

### Step 2: Push Your Code

Commit this new workflow file and push your repository up to GitHub:

```bash
git add .github/workflows/deploy.yml
git commit -m "Add GitHub Actions workflow for mdBook"
git push origin main

```

### Step 3: Configure GitHub Settings

By default, GitHub Pages is turned off. You need to tell GitHub to use the Action you just created.

1. Go to your repository on GitHub.
2. Click the **Settings** tab.
3. In the left sidebar, click **Pages** (under the "Code and automation" section).
4. Under the **Build and deployment** section, look for the "Source" dropdown.
5. Change it from "Deploy from a branch" to **"GitHub Actions"**.

### Step 4: Watch it Deploy!

Once you change that setting, GitHub will automatically pick up your workflow.

1. Click on the **Actions** tab at the top of your GitHub repository.
2. You should see your "Deploy mdBook to GitHub Pages" workflow running.
3. Once it turns green, go back to the **Pages** settings screen, and you will see a link to your live, public website!

---

**A quick tip for custom languages:** If you end up building that custom `mdbook-mylang` testing preprocessor we talked about earlier, all you have to do is add `- run: cargo install --path ./path/to/my/preprocessor` into the `build` job right before the `mdbook build` step.

**Would you like me to help you configure the `book.toml` file to add a custom GitHub icon to the top right of your generated book that links back to your repo?**


That makes total sense. In compiler design, keeping the surface syntax (what the user writes) and the core syntax (what the compiler desugars it into) in the same place is incredibly valuable. It allows readers to easily click back and forth to understand how high-level concepts map to your internal intermediate representation (IR).

The best way to do this is to keep them in a **single mdBook** rather than trying to host two separate books. Keeping them together gives you a **unified search index**—so if someone searches for "functions," they see both how to write them in the surface language and how they are represented in the core.

Here is how you execute that cleanly.

---

### 1. Organizing the `SUMMARY.md`

mdBook allows you to create un-clickable "Section Headers" to divide your book into major parts. You can use this to create a clean, separated navigation tree on the left sidebar.

Your `src/SUMMARY.md` would look something like this:

```markdown
# Book Title

[Introduction](./intro.md)

# Part I: The Surface Language
- [Getting Started](./surface/getting_started.md)
- [Variables & Types](./surface/types.md)
- [Control Flow](./surface/control_flow.md)
- [Functions](./surface/functions.md)

# Part II: The Core Language
- [Core Architecture](./core/intro.md)
- [The AST / IR](./core/ast.md)
- [Desugaring Surface to Core](./core/lowering.md)
- [Type System Formalization](./core/types.md)

# Part III: Compiler Internals
- [Lexer & Parser](./internals/frontend.md)
- [Code Generation](./internals/codegen.md)

```

### 2. The Technical Catch: Distinct Code Blocks

Because you have two different syntaxes, the custom preprocessor we talked about earlier now has a slightly more complex job. It needs to know which parser to use!

You will need to use distinct tags for your code blocks so your testing harness knows how to validate them.

**For Surface Language snippets:**

```markdown
```surface
let x = 5 + 5;

```

```

**For Core Language snippets:**
```markdown
```core
(Let "x" (Add (Int 5) (Int 5)))

```

```

When you write your `mdbook-mylang` preprocessor or `cargo test` harness, your Rust logic will simply pattern-match on the tag:
* If it sees ````surface`, it feeds the string to `surface_parser::parse()`.
* If it sees ````core`, it feeds the string to `core_parser::parse()`.

### 3. Cross-Linking for "Desugaring" Explanations
Since they are in the same book, you can seamlessly link between them. When explaining a surface feature, you can directly link to its core representation using relative paths:

```markdown
// In surface/control_flow.md
The `if/else` block is a high-level construct that is eventually 
lowered into a `Match` expression in the [Core AST](../core/ast.md).

```

### The Verdict

Hosting them together in one `mdBook` using Section Headers is definitely the way to go. It keeps deployment simple (just one GitHub Action), keeps search unified, and naturally mirrors the pipeline of your compiler.

**Would you like to start mocking up the exact `SUMMARY.md` for your specific language features, or would you rather look at how to adapt our Rust snippet-extractor to handle both