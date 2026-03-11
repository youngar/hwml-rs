//! Integration test that validates all code snippets in documentation files.
//!
//! This test walks through all Markdown files in the docs/ directory and validates
//! that all hwml and hwmlc code snippets type-check correctly.
//!
//! This test uses `process_chapter_content` which properly handles session state,
//! allowing later snippets to reference earlier definitions on the same page.

use mdbook_hwml::process_chapter_content;
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

    let mut total_files = 0;
    let mut failed_files = 0;
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
                failed_files += 1;
                continue;
            }
        };

        total_files += 1;

        // Process the entire chapter content (handles session state)
        if let Err(chapter_errors) = process_chapter_content(&content) {
            failed_files += 1;
            errors.push(format!(
                "{} - Validation errors:\n  {}",
                relative_path.display(),
                chapter_errors.join("\n  ")
            ));
        }
    }

    // Print summary
    if total_files == 0 {
        eprintln!("Warning: No markdown files found in docs/");
    } else {
        eprintln!(
            "Validated {} markdown files ({} failed)",
            total_files, failed_files
        );
    }

    // Report errors
    if !errors.is_empty() {
        eprintln!("\nDocumentation validation errors:\n");
        for error in &errors {
            eprintln!("{}\n", error);
        }
        panic!(
            "{} out of {} documentation files failed validation",
            failed_files, total_files
        );
    }
}
