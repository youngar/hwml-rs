//! Integration test that validates all code snippets in documentation files.
//!
//! This test walks through all Markdown files in the docs/ directory and validates
//! that all hwml and hwmlc code snippets type-check correctly.

use mdbook_hwml::{
    extract_snippets, typecheck_snippet_hwml, typecheck_snippet_hwmlc, SnippetLanguage,
};
use std::path::PathBuf;
use walkdir::WalkDir;

/// Test that all code snippets in documentation files are valid.
#[test]
fn test_all_documentation_snippets() {
    let workspace_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();

    let docs_dir = workspace_root.join("docs");

    // Skip test if docs directory doesn't exist yet
    if !docs_dir.exists() {
        eprintln!("Skipping test: docs/ directory does not exist yet");
        return;
    }

    let mut total_snippets = 0;
    let mut failed_snippets = 0;
    let mut errors = Vec::new();

    // Walk through all .md files in docs/
    for entry in WalkDir::new(&docs_dir)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().map_or(false, |ext| ext == "md"))
    {
        let path = entry.path();
        let relative_path = path.strip_prefix(&workspace_root).unwrap_or(path);

        let content = match std::fs::read_to_string(path) {
            Ok(c) => c,
            Err(e) => {
                errors.push(format!("Failed to read {}: {}", relative_path.display(), e));
                continue;
            }
        };

        let snippets = extract_snippets(&content);

        for snippet in snippets {
            total_snippets += 1;

            let result = match snippet.language {
                SnippetLanguage::Hwml => typecheck_snippet_hwml(&snippet.code),
                SnippetLanguage::Hwmlc => typecheck_snippet_hwmlc(&snippet.code),
            };

            // Check if the result matches expectations
            let should_fail = snippet.should_fail;
            match (result, should_fail) {
                (Ok(()), false) => {
                    // Success: snippet is valid and should be valid
                }
                (Err(_), true) => {
                    // Success: snippet is invalid and should be invalid
                }
                (Ok(()), true) => {
                    // Failure: snippet is valid but should fail
                    failed_snippets += 1;
                    let line_info = snippet
                        .line_number
                        .map(|l| format!(":{}", l))
                        .unwrap_or_default();
                    errors.push(format!(
                        "{}{} - {:?} snippet marked 'should_fail' but type-checked successfully",
                        relative_path.display(),
                        line_info,
                        snippet.language
                    ));
                }
                (Err(errs), false) => {
                    // Failure: snippet is invalid but should be valid
                    failed_snippets += 1;
                    let line_info = snippet
                        .line_number
                        .map(|l| format!(":{}", l))
                        .unwrap_or_default();
                    let code_preview = snippet
                        .code
                        .lines()
                        .enumerate()
                        .take(10)
                        .map(|(i, line)| format!("  {:3}: {}", i + 1, line))
                        .collect::<Vec<_>>()
                        .join("\n");
                    errors.push(format!(
                        "{}{} - {:?} snippet failed type-checking:\n  {}\n  Code:\n{}",
                        relative_path.display(),
                        line_info,
                        snippet.language,
                        errs.join("\n  "),
                        code_preview
                    ));
                }
            }
        }
    }

    // Print summary
    if total_snippets == 0 {
        eprintln!("Warning: No code snippets found in docs/");
    } else {
        eprintln!(
            "Validated {} code snippets ({} failed)",
            total_snippets, failed_snippets
        );
    }

    // Report errors
    if !errors.is_empty() {
        eprintln!("\nDocumentation validation errors:\n");
        for error in &errors {
            eprintln!("{}\n", error);
        }
        panic!(
            "{} out of {} documentation snippets failed validation",
            failed_snippets, total_snippets
        );
    }
}
