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
/// This crate provides functionality to:
/// - Extract code blocks tagged as `hwml` or `hwmlc` from Markdown files
/// - Track whether snippets should pass or fail type checking
/// - Support the `should_fail` modifier for negative test cases
/// - Validate snippets using the hwml_core compiler API
use pulldown_cmark::{CodeBlockKind, Event, Parser, Tag, TagEnd};

/// Represents a code snippet extracted from Markdown documentation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Snippet {
    /// The source code of the snippet
    pub code: String,
    /// The language tag (either "hwml" or "hwmlc")
    pub language: SnippetLanguage,
    /// Whether this snippet is expected to fail type checking
    pub should_fail: bool,
    /// Whether this snippet should be ignored (not type-checked)
    pub ignore: bool,
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
        Self {
            code,
            language,
            should_fail,
            ignore: false,
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
        Self {
            code,
            language,
            should_fail,
            ignore,
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
        Self {
            code,
            language,
            should_fail,
            ignore: false,
            line_number: Some(line_number),
        }
    }
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
    let mut current_code = String::new();

    for event in parser {
        match event {
            Event::Start(Tag::CodeBlock(CodeBlockKind::Fenced(lang))) => {
                let lang_str = lang.as_ref();

                // Check if this is a hwml or hwmlc code block
                if let Some(language) = SnippetLanguage::from_str(lang_str) {
                    in_code_block = true;
                    current_language = Some(language);
                    // Check for should_fail and ignore modifiers
                    current_should_fail = lang_str.contains("should_fail");
                    current_ignore = lang_str.contains("ignore");
                    current_code.clear();
                }
            }
            Event::End(TagEnd::CodeBlock) => {
                if in_code_block {
                    if let Some(language) = current_language {
                        snippets.push(Snippet::new_with_ignore(
                            current_code.clone(),
                            language,
                            current_should_fail,
                            current_ignore,
                        ));
                    }
                    in_code_block = false;
                    current_language = None;
                    current_should_fail = false;
                    current_ignore = false;
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
/// assert!(typecheck_snippet_hwmlc("prim $Nat : U0;;").is_ok());
/// ```
pub fn typecheck_snippet_hwmlc(source: &str) -> Result<(), Vec<String>> {
    let db = hwml_core::Database::new();

    // Parse the module
    let module = match hwml_core::syn::parse_module(&db, source) {
        Ok(m) => m,
        Err(e) => return Err(vec![format!("Parse error: {:?}", e)]),
    };

    // Type-check the module
    let global_env = hwml_core::val::GlobalEnv::new();
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
}
