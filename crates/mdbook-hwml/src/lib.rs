#![allow(clippy::needless_borrow)]
#![allow(clippy::explicit_auto_deref)]
#![allow(clippy::iter_cloned_collect)]
#![allow(clippy::match_single_binding)]
#![allow(clippy::doc_markdown)]
#![allow(clippy::missing_errors_doc)]
#![allow(clippy::match_same_arms)]
#![allow(clippy::must_use_candidate)]

/// Utilities for extracting and validating code snippets from Markdown documentation.
///
/// This crate provides functionality to extract code blocks tagged as `hwml` or `hwmlc`
/// from Markdown files, track whether snippets should pass or fail type checking, and
/// validate snippets using the hwml_core compiler API. The `should_fail` modifier is
/// supported for negative test cases.
use pulldown_cmark::{CodeBlockKind, Event, Parser, Tag, TagEnd};

/// Represents a code snippet extracted from Markdown documentation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Snippet {
    /// The source code of the snippet (full code including hidden lines)
    pub code: String,
    /// The display code (code without hidden lines, for rendering)
    pub display_code: String,
    /// The language tag (either "hwml" or "hwmlc")
    pub language: SnippetLanguage,
    /// Whether this snippet is expected to fail type checking
    pub should_fail: bool,
    /// Whether this snippet should be ignored (not type-checked)
    pub ignore: bool,
    /// Whether this snippet should not use session state (type-check in isolation)
    pub no_session: bool,
    /// Whether to emit the lowered HWMLC code for this snippet
    pub emit_core: bool,
    /// Line number where the snippet starts in the source file (for error reporting)
    pub line_number: Option<usize>,
}

/// The language of a code snippet
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SnippetLanguage {
    /// Surface language (hwml)
    Hwml,
    /// Core language (hwmlc)
    Hwmlc,
}

impl SnippetLanguage {
    /// Parse a language tag from a string
    fn from_str(s: &str) -> Option<Self> {
        // Remove any modifiers (like "should_fail") to get the base language
        let base = s.split(',').next()?.trim();
        match base {
            "hwml" => Some(Self::Hwml),
            "hwmlc" => Some(Self::Hwmlc),
            _ => None,
        }
    }
}

impl Snippet {
    /// Create a new snippet
    pub fn new(code: String, language: SnippetLanguage, should_fail: bool) -> Self {
        let display_code = code.clone();
        Self {
            code,
            display_code,
            language,
            should_fail,
            ignore: false,
            no_session: false,
            emit_core: false,
            line_number: None,
        }
    }

    /// Create a new snippet with ignore flag
    pub fn new_with_ignore(
        code: String,
        language: SnippetLanguage,
        should_fail: bool,
        ignore: bool,
    ) -> Self {
        let display_code = code.clone();
        Self {
            code,
            display_code,
            language,
            should_fail,
            ignore,
            no_session: false,
            emit_core: false,
            line_number: None,
        }
    }

    /// Create a new snippet with a line number
    pub fn with_line_number(
        code: String,
        language: SnippetLanguage,
        should_fail: bool,
        line_number: usize,
    ) -> Self {
        let display_code = code.clone();
        Self {
            code,
            display_code,
            language,
            should_fail,
            ignore: false,
            no_session: false,
            emit_core: false,
            line_number: Some(line_number),
        }
    }
}

/// Separate hidden lines from display lines in code. Lines starting with "# " are
/// hidden from display but included in compilation, similar to how Rust's doc tests work.
pub fn separate_hidden_lines(code: &str) -> (String, String) {
    let mut display_code = String::new();
    let mut compiler_code = String::new();

    for line in code.lines() {
        if let Some(hidden_line) = line.strip_prefix("# ") {
            // This line starts with "# " so we include it in the compiler code but not the display.
            compiler_code.push_str(hidden_line);
            compiler_code.push('\n');
        } else {
            // Normal line gets included in both.
            compiler_code.push_str(line);
            compiler_code.push('\n');
            display_code.push_str(line);
            display_code.push('\n');
        }
    }

    // Remove trailing newlines if the original didn't have them.
    if !code.ends_with('\n') {
        if compiler_code.ends_with('\n') {
            compiler_code.pop();
        }
        if display_code.ends_with('\n') {
            display_code.pop();
        }
    }

    (compiler_code, display_code)
}

/// Extract all hwml and hwmlc code snippets from a Markdown string.
///
/// This function parses the Markdown and looks for fenced code blocks with
/// language tags `hwml` or `hwmlc`. It also recognizes the `should_fail`
/// and `ignore` modifiers.
///
/// # Examples
///
/// ```markdown
/// # Example
///
/// This should pass:
/// ```hwml
/// def x : Bit := 0
/// ```
///
/// This should fail:
/// ```hwml,should_fail
/// def x : Bit := "not a bit"
/// ```
///
/// This should be ignored:
/// ```hwml,ignore
/// def x : NotImplementedYet := ...
/// ```
/// ```
pub fn extract_snippets(markdown: &str) -> Vec<Snippet> {
    let parser = Parser::new(markdown);
    let mut snippets = Vec::new();
    let mut in_code_block = false;
    let mut current_language: Option<SnippetLanguage> = None;
    let mut current_should_fail = false;
    let mut current_ignore = false;
    let mut current_no_session = false;
    let mut current_emit_core = false;
    let mut current_code = String::new();

    for event in parser {
        match event {
            Event::Start(Tag::CodeBlock(CodeBlockKind::Fenced(lang))) => {
                let lang_str = lang.as_ref();

                // Check if this is a hwml or hwmlc code block
                if let Some(language) = SnippetLanguage::from_str(lang_str) {
                    in_code_block = true;
                    current_language = Some(language);
                    // Check for modifiers in the language tag.
                    current_should_fail = lang_str.contains("should_fail");
                    current_ignore = lang_str.contains("ignore");
                    current_no_session = lang_str.contains("no_session");
                    current_emit_core = lang_str.contains("emit_core");
                    current_code.clear();
                }
            }
            Event::End(TagEnd::CodeBlock) => {
                if in_code_block {
                    if let Some(language) = current_language {
                        // Separate hidden lines from display lines.
                        let (compiler_code, display_code) = separate_hidden_lines(&current_code);

                        snippets.push(Snippet {
                            code: compiler_code,
                            display_code,
                            language,
                            should_fail: current_should_fail,
                            ignore: current_ignore,
                            no_session: current_no_session,
                            emit_core: current_emit_core,
                            line_number: None,
                        });
                    }
                    in_code_block = false;
                    current_language = None;
                    current_should_fail = false;
                    current_ignore = false;
                    current_no_session = false;
                    current_emit_core = false;
                    current_code.clear();
                }
            }
            Event::Text(text) => {
                if in_code_block {
                    current_code.push_str(&text);
                }
            }
            Event::Code(_) | Event::Html(_) | Event::InlineHtml(_) => {
                // Ignore inline code and HTML
            }
            _ => {}
        }
    }

    snippets
}

/// Typecheck a hwmlc (core language) snippet using the hwml_core compiler.
///
/// This function parses and type-checks a snippet of core language code.
/// It returns `Ok(())` if the snippet is valid, or `Err` with a list of
/// error messages if it fails.
///
/// # Examples
///
/// ```
/// use mdbook_hwml::typecheck_snippet_hwmlc;
///
/// // Valid snippet
/// assert!(typecheck_snippet_hwmlc("prim $Nat : U0;").is_ok());
/// ```
pub fn typecheck_snippet_hwmlc(source: &str) -> Result<(), Vec<String>> {
    let db = hwml_core::Database::new();

    // Parse the module
    let module = match hwml_core::syn::parse_module(&db, source) {
        Ok(m) => m,
        Err(e) => return Err(vec![format!("Parse error: {:?}", e)]),
    };

    // Type-check the module
    let global_env = hwml_core::GlobalEnv::new();
    match hwml_core::check_module::check_module(&db, &module, global_env) {
        Ok(_) => Ok(()),
        Err(e) => Err(vec![format!("Type error: {:?}", e)]),
    }
}

/// Typecheck a hwml (surface language) snippet.
///
/// This function parses and type-checks a snippet of surface language code.
/// It returns `Ok(())` if the snippet is valid, or `Err` with a list of
/// error messages if it fails.
///
/// Note: This is a placeholder until surface language type checking is implemented.
///
/// # Examples
///
/// ```
/// use mdbook_hwml::typecheck_snippet_hwml;
///
/// // Valid snippet (when surface language is implemented)
/// // assert!(typecheck_snippet_hwml("def x : Bit := 0").is_ok());
/// ```
pub fn typecheck_snippet_hwml(_source: &str) -> Result<(), Vec<String>> {
    // TODO: Implement surface language parsing and elaboration
    // For now, we just return an error indicating it's not implemented
    Err(vec![
        "Surface language (hwml) type checking not yet implemented".to_string(),
    ])
}

/// Typecheck a hwmlc snippet with session state (accumulated source code).
///
/// This function accumulates source code from multiple snippets and type-checks
/// them together as a single module. This allows later snippets to reference
/// definitions from earlier ones.
///
/// # Arguments
///
/// * `accumulated_source` - The accumulated source code from all previous snippets
/// * `new_source` - The new source code to add and type-check
///
/// # Returns
///
/// Returns `Ok(())` if successful, or `Err` with error messages if it fails.
fn typecheck_snippet_hwmlc_accumulated(
    accumulated_source: &str,
    new_source: &str,
) -> Result<(), Vec<String>> {
    let db = hwml_core::Database::new();

    // Combine accumulated source with new source
    let combined_source = if accumulated_source.is_empty() {
        new_source.to_string()
    } else {
        format!("{}\n{}", accumulated_source, new_source)
    };

    // Parse the combined module
    let module = match hwml_core::syn::parse_module(&db, &combined_source) {
        Ok(m) => m,
        Err(e) => return Err(vec![format!("Parse error: {:?}", e)]),
    };

    // Type-check the module
    let global_env = hwml_core::GlobalEnv::new();
    match hwml_core::check_module::check_module(&db, &module, global_env) {
        Ok(_) => Ok(()),
        Err(e) => Err(vec![format!("Type error: {:?}", e)]),
    }
}

/// Lower a hwml snippet to hwmlc incrementally.
///
/// This function takes a session context (accumulated source from previous snippets)
/// and new source code, type-checks them together, but only returns the lowered
/// HWMLC output for the new code.
///
/// # Arguments
///
/// * `context` - The accumulated source code from all previous snippets (session context)
/// * `new_code` - The new source code to lower
///
/// # Returns
///
/// Returns `Ok(String)` with the lowered HWMLC code for the new snippet only,
/// or `Err(String)` with error messages if lowering fails.
///
/// # Note
///
/// This is a stub implementation. The actual incremental lowering will be implemented
/// in hwml_core once the elaborator is ready.
fn lower_incremental(_context: &str, _new_code: &str) -> Result<String, String> {
    // TODO: Implement incremental lowering in hwml_core
    // For now, return a placeholder error
    Err("Incremental lowering (emit_core) not yet implemented".to_string())
}

/// Process a chapter's markdown content, validating code snippets and hiding boilerplate.
///
/// This function extracts all hwml and hwmlc code snippets from the markdown and validates
/// each snippet using the appropriate typechecker. It maintains session state so that later
/// snippets can reference definitions from earlier ones. The function returns modified markdown
/// with hidden lines (those starting with "# ") removed from display. If any snippet fails
/// validation (unless marked should_fail), an error is returned. The `emit_core` modifier is
/// supported to show lowered HWMLC output incrementally.
///
/// For hwmlc snippets, this function maintains a global environment across all snippets in
/// the chapter. This allows you to write tutorials where later code blocks build on earlier
/// ones. For example, you can define a type in one snippet and use it in later snippets on
/// the same page.
///
/// The `emit_core` modifier on hwml snippets will lower the current snippet to HWMLC and
/// inject the output in a collapsible details block. Only the current snippet's lowered
/// output is shown, not the accumulated session history.
///
/// Returns an error if any code snippet fails type checking when it should not, or passes
/// type checking when it should fail.
pub fn process_chapter_content(content: &str) -> Result<String, Vec<String>> {
    use std::cell::RefCell;

    let errors = RefCell::new(Vec::new());
    // Session state: accumulated source code for hwmlc snippets (context for later snippets)
    let hwmlc_session_context = RefCell::new(String::new());

    // Use regex to find and replace code blocks
    let re = regex::Regex::new(r"(?s)```(hwmlc?)(,[^\n]*)?\n(.*?)```").unwrap();

    let processed_content = re.replace_all(content, |caps: &regex::Captures| {
        let lang = &caps[1]; // "hwml" or "hwmlc"
        let modifiers = caps.get(2).map_or("", |m| m.as_str()); // e.g., ",should_fail"
        let raw_code = &caps[3];

        let should_fail = modifiers.contains("should_fail");
        let ignore = modifiers.contains("ignore");
        let no_session = modifiers.contains("no_session");
        let emit_core = modifiers.contains("emit_core");

        // Parse language
        let language = match lang {
            "hwml" => SnippetLanguage::Hwml,
            "hwmlc" => SnippetLanguage::Hwmlc,
            _ => unreachable!(),
        };

        // Separate hidden lines from display lines
        let (compiler_code, display_code) = separate_hidden_lines(raw_code);

        // Skip validation for ignored snippets
        if !ignore {
            // Separate current snippet from session context
            let current_snippet_code = compiler_code.clone();

            // Type check the snippet (using full code including hidden lines)
            let result = match language {
                SnippetLanguage::Hwml => typecheck_snippet_hwml(&current_snippet_code),
                SnippetLanguage::Hwmlc => {
                    if no_session {
                        // Don't use session state - type-check in isolation
                        typecheck_snippet_hwmlc(&current_snippet_code)
                    } else {
                        // Use session state - validate with context
                        let session_context = hwmlc_session_context.borrow().clone();
                        match typecheck_snippet_hwmlc_accumulated(
                            &session_context,
                            &current_snippet_code,
                        ) {
                            Ok(()) => {
                                // Add this snippet to the session context for future snippets
                                let mut ctx = hwmlc_session_context.borrow_mut();
                                if !ctx.is_empty() {
                                    ctx.push('\n');
                                }
                                ctx.push_str(&current_snippet_code);
                                Ok(())
                            }
                            Err(e) => Err(e),
                        }
                    }
                }
            };

            // Validate against expectations
            match (result, should_fail) {
                (Ok(()), true) => {
                    errors.borrow_mut().push(format!(
                        "Snippet marked 'should_fail' but type-checked successfully:\n{}",
                        compiler_code
                    ));
                }
                (Err(errs), false) => {
                    let code_preview = compiler_code
                        .lines()
                        .enumerate()
                        .take(10)
                        .map(|(i, line)| format!("  {:3}: {}", i + 1, line))
                        .collect::<Vec<_>>()
                        .join("\n");
                    errors.borrow_mut().push(format!(
                        "Snippet failed type-checking:\n  {}\n  Code:\n{}",
                        errs.join("\n  "),
                        code_preview
                    ));
                }
                _ => {} // Behaved as expected
            }
        }

        // Build the output markdown
        let mut output = format!("```{}{}\n{}```", lang, modifiers, display_code);

        // If emit_core is set and this is a hwml snippet, try to lower it
        if emit_core && language == SnippetLanguage::Hwml && !ignore {
            let session_context = hwmlc_session_context.borrow().clone();
            match lower_incremental(&session_context, &compiler_code) {
                Ok(lowered_code) => {
                    // Inject the lowered code in a collapsible details block
                    output.push_str("\n\n<details>\n<summary><b>Lowered HWMLC (Core)</b></summary>\n\n```hwmlc\n");
                    output.push_str(&lowered_code);
                    output.push_str("\n```\n</details>");
                }
                Err(err) => {
                    // If lowering fails, add an error note
                    errors.borrow_mut().push(format!(
                        "Failed to lower snippet with emit_core:\n  {}\n  Code:\n{}",
                        err,
                        compiler_code
                    ));
                }
            }
        }

        output
    });

    let errors = errors.into_inner();
    if !errors.is_empty() {
        return Err(errors);
    }

    Ok(processed_content.into_owned())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_hwml_snippet() {
        let markdown = r#"
# Test

```hwml
def x : Bit := 0
```
"#;
        let snippets = extract_snippets(markdown);
        assert_eq!(snippets.len(), 1);
        assert_eq!(snippets[0].language, SnippetLanguage::Hwml);
        assert_eq!(snippets[0].code.trim(), "def x : Bit := 0");
        assert!(!snippets[0].should_fail);
    }

    #[test]
    fn test_extract_hwmlc_snippet() {
        let markdown = r#"
```hwmlc
const Zero : $Bit;
```
"#;
        let snippets = extract_snippets(markdown);
        assert_eq!(snippets.len(), 1);
        assert_eq!(snippets[0].language, SnippetLanguage::Hwmlc);
        assert_eq!(snippets[0].code.trim(), "const Zero : $Bit;");
        assert!(!snippets[0].should_fail);
    }

    #[test]
    fn test_extract_should_fail_snippet() {
        let markdown = r#"
```hwml,should_fail
def x : Bit := "not a bit"
```
"#;
        let snippets = extract_snippets(markdown);
        assert_eq!(snippets.len(), 1);
        assert_eq!(snippets[0].language, SnippetLanguage::Hwml);
        assert!(snippets[0].should_fail);
    }

    #[test]
    fn test_extract_multiple_snippets() {
        let markdown = r#"
# Documentation

Here's a hwml example:
```hwml
def x : Bit := 0
```

And here's a hwmlc example:
```hwmlc
const One : $Bit;
```

This should fail:
```hwml,should_fail
def bad : Bit := 999
```
"#;
        let snippets = extract_snippets(markdown);
        assert_eq!(snippets.len(), 3);
        assert_eq!(snippets[0].language, SnippetLanguage::Hwml);
        assert!(!snippets[0].should_fail);
        assert_eq!(snippets[1].language, SnippetLanguage::Hwmlc);
        assert!(!snippets[1].should_fail);
        assert_eq!(snippets[2].language, SnippetLanguage::Hwml);
        assert!(snippets[2].should_fail);
    }

    #[test]
    fn test_ignore_other_languages() {
        let markdown = r#"
```rust
fn main() {}
```

```hwml
def x : Bit := 0
```

```python
print("hello")
```
"#;
        let snippets = extract_snippets(markdown);
        assert_eq!(snippets.len(), 1);
        assert_eq!(snippets[0].language, SnippetLanguage::Hwml);
    }

    #[test]
    fn test_hidden_lines() {
        let code = r#"# let setup = 10;
let x = setup + 5;
# let cleanup = 20;"#;

        let (compiler_code, display_code) = separate_hidden_lines(code);

        // Compiler should see all lines
        assert_eq!(
            compiler_code,
            "let setup = 10;\nlet x = setup + 5;\nlet cleanup = 20;"
        );

        // Display should only see non-hidden lines (no trailing newline since input doesn't have one)
        assert_eq!(display_code, "let x = setup + 5;");
    }

    #[test]
    fn test_extract_with_hidden_lines() {
        let markdown = r#"
```hwmlc
# prim $Nat : U0;
# prim $zero : $Nat;
const @Zero : $Nat = $zero;
```
"#;
        let snippets = extract_snippets(markdown);
        assert_eq!(snippets.len(), 1);

        // Compiler code should include hidden lines
        assert!(snippets[0].code.contains("prim $Nat : U0;"));
        assert!(snippets[0].code.contains("prim $zero : $Nat;"));
        assert!(snippets[0].code.contains("const @Zero : $Nat = $zero;"));

        // Display code should not include hidden lines
        assert!(!snippets[0].display_code.contains("prim $Nat : U0;"));
        assert!(!snippets[0].display_code.contains("prim $zero : $Nat;"));
        assert!(snippets[0]
            .display_code
            .contains("const @Zero : $Nat = $zero;"));
    }

    #[test]
    fn test_process_chapter_with_hidden_lines() {
        let markdown = r#"# Example

```hwmlc
# prim $Nat : U0;
# prim $zero : $Nat;
const @Zero : $Nat = $zero;
```
"#;

        let result = process_chapter_content(markdown);
        assert!(result.is_ok());

        let processed = result.unwrap();
        // The processed markdown should not contain the hidden lines
        assert!(!processed.contains("prim $Nat : U0;"));
        assert!(!processed.contains("prim $zero : $Nat;"));
        assert!(processed.contains("const @Zero : $Nat = $zero;"));
    }

    #[test]
    fn test_session_state() {
        let markdown = r#"# Session State Test

First, define a type and a value:
```hwmlc
prim $Nat : U0;
prim $zero : $Nat;
```

Then use them in a later snippet:
```hwmlc
const @Zero : $Nat = $zero;
const @One : $Nat = $zero;
```

And use those constants:
```hwmlc
const @Two : $Nat = @Zero;
```
"#;

        let result = process_chapter_content(markdown);
        if let Err(ref errors) = result {
            eprintln!("Errors: {:?}", errors);
        }
        assert!(
            result.is_ok(),
            "Session state should allow later snippets to reference earlier definitions"
        );
    }

    #[test]
    fn test_emit_core_modifier() {
        // Test that emit_core modifier is parsed correctly
        let markdown = r#"
```hwml,emit_core
def x : Bit := 0
```
"#;
        let snippets = extract_snippets(markdown);
        assert_eq!(snippets.len(), 1);
        assert!(snippets[0].emit_core, "emit_core modifier should be parsed");

        // Test that emit_core generates an error (since lowering is not implemented yet)
        // The error should mention that incremental lowering is not implemented
        let result = process_chapter_content(markdown);
        assert!(
            result.is_err(),
            "emit_core should fail since lowering is not implemented"
        );
        if let Err(errors) = result {
            assert!(
                errors.iter().any(|e| e.contains("Incremental lowering")),
                "Error should mention incremental lowering not being implemented"
            );
        }
    }

    #[test]
    fn test_no_session_modifier() {
        let markdown = r#"# No Session Test

Define a type:
```hwmlc
prim $Nat : U0;
prim $zero : $Nat;
```

This should fail because it doesn't have access to the previous snippet:
```hwmlc,no_session,should_fail
const @Zero : $Nat = $zero;
```
"#;

        let result = process_chapter_content(markdown);
        assert!(
            result.is_ok(),
            "no_session modifier should isolate snippets"
        );
    }
}
