//! mdBook preprocessor for HWML language documentation.
//!
//! This preprocessor:
//! - Validates all hwml/hwmlc code snippets during the build
//! - Hides boilerplate lines (prefixed with "# ") from display
//! - Supports `should_fail` and `ignore` modifiers
//! - Halts the build if any snippet fails validation

use anyhow::{Context, Result};
use mdbook_core::book::{Book, BookItem};
use mdbook_hwml::process_chapter_content;
use mdbook_preprocessor::{Preprocessor, PreprocessorContext};
use std::io;
use std::process;

struct HwmlPreprocessor;

impl Preprocessor for HwmlPreprocessor {
    fn name(&self) -> &str {
        "hwml-validator"
    }

    fn run(&self, _ctx: &PreprocessorContext, mut book: Book) -> Result<Book> {
        let mut has_errors = false;

        // Process each chapter in the book
        book.for_each_mut(|item| {
            if let BookItem::Chapter(chapter) = item {
                match process_chapter_content(&chapter.content) {
                    Ok(new_content) => {
                        // Replace chapter content with processed version
                        // (hidden lines removed, snippets validated)
                        chapter.content = new_content;
                    }
                    Err(errors) => {
                        eprintln!("\n❌ Validation errors in chapter '{}':", chapter.name);
                        for error in errors {
                            eprintln!("\n{}", error);
                        }
                        has_errors = true;
                    }
                }
            }
        });

        if has_errors {
            eprintln!("\n❌ mdBook build halted due to code snippet validation failures.");
            eprintln!(
                "Fix the errors above or mark failing snippets with ',should_fail' or ',ignore'."
            );
            process::exit(1);
        }

        Ok(book)
    }

    fn supports_renderer(&self, renderer: &str) -> Result<bool> {
        Ok(renderer == "html" || renderer == "markdown")
    }
}

fn main() -> Result<()> {
    // Handle the "supports" command
    if let Some(arg) = std::env::args().nth(1) {
        if arg == "supports" {
            // Check if the renderer is supported
            if let Some(renderer) = std::env::args().nth(2) {
                let preprocessor = HwmlPreprocessor;
                if preprocessor.supports_renderer(&renderer)? {
                    process::exit(0);
                } else {
                    process::exit(1);
                }
            }
        }
    }

    // Parse input from mdBook (JSON via stdin)
    let input: (PreprocessorContext, Book) =
        serde_json::from_reader(io::stdin()).context("Failed to parse mdBook input")?;

    let (ctx, book) = input;

    // Run the preprocessor
    let processed_book = HwmlPreprocessor
        .run(&ctx, book)
        .context("Preprocessor failed")?;

    // Write the processed book back to mdBook (JSON via stdout)
    serde_json::to_writer(io::stdout(), &processed_book)
        .context("Failed to write processed book")?;

    Ok(())
}
