use hwml_core::{ty::RcTy, RcValue, SourceRange};

use crate::{context::ElabFrame, meta::MetaId};

#[derive(Debug, Clone)]
pub enum ElabError<'db> {
    TypeMismatch {
        elab_backtrace: Vec<ElabFrame<'db>>,
        expected: RcTy<'db>,
        actual: RcTy<'db>,
        span: Option<SourceRange<'db>>,
    },
    NotInScope {
        elab_backtrace: Vec<ElabFrame<'db>>,
        name: String,
        span: Option<SourceRange<'db>>,
    },
    CannotInfer {
        elab_backtrace: Vec<ElabFrame<'db>>,
        span: Option<SourceRange<'db>>,
    },
    UnificationFailure {
        elab_backtrace: Vec<ElabFrame<'db>>,
        lhs: RcValue<'db>,
        rhs: RcValue<'db>,
        span: Option<SourceRange<'db>>,
    },
    OccursCheck {
        elab_backtrace: Vec<ElabFrame<'db>>,
        meta: MetaId,
        span: Option<SourceRange<'db>>,
    },
    ScopeViolation {
        elab_backtrace: Vec<ElabFrame<'db>>,
        meta: MetaId,
        span: Option<SourceRange<'db>>,
    },
    UnsolvedMeta {
        elab_backtrace: Vec<ElabFrame<'db>>,
        meta: MetaId,
        span: Option<SourceRange<'db>>,
    },
    MetaAlreadySolved {
        meta: MetaId,
        elab_backtrace: Vec<ElabFrame<'db>>,
    },
    NotImplemented {
        elab_backtrace: Vec<ElabFrame<'db>>,
        feature: String,
        span: Option<SourceRange<'db>>,
    },
}

// NOTE: Salsa accumulators are the proper way to collect diagnostics in tracked functions.
// However, `elab_library_with_sccs` cannot currently be a `#[salsa::tracked]` function
// because it takes `&mut GlobalEnv` as a parameter. Salsa tracked functions must be pure
// and cannot take mutable references.
//
// For now, we use the simpler pattern of returning `Vec<ElabError>` in `ElabProgramResult`.
// The elaboration loop is lenient: it catches errors, pushes them to the Vec, and continues
// processing the rest of the library instead of short-circuiting.
//
// Future refactoring could make elaboration a proper tracked function by having it return
// a new GlobalEnv instead of mutating an existing one. Then we could use Salsa accumulators:
//
// ```rust
// #[salsa::accumulator]
// pub struct ElabDiagnostics(pub ElabError);
//
// #[salsa::tracked]
// pub fn elab_library_tracked(db: &dyn Database, ...) -> GlobalEnv {
//     // Push errors using ElabDiagnostics::push(db, error)
//     // Retrieve using ElabDiagnostics::accumulated(db, ...)
// }
// ```

impl<'db> ElabError<'db> {
    /// Get the elaboration backtrace from this error.
    pub fn backtrace(&self) -> &[ElabFrame<'db>] {
        match self {
            ElabError::TypeMismatch { elab_backtrace, .. } => elab_backtrace,
            ElabError::NotInScope { elab_backtrace, .. } => elab_backtrace,
            ElabError::CannotInfer { elab_backtrace, .. } => elab_backtrace,
            ElabError::UnificationFailure { elab_backtrace, .. } => elab_backtrace,
            ElabError::OccursCheck { elab_backtrace, .. } => elab_backtrace,
            ElabError::ScopeViolation { elab_backtrace, .. } => elab_backtrace,
            ElabError::UnsolvedMeta { elab_backtrace, .. } => elab_backtrace,
            ElabError::MetaAlreadySolved { elab_backtrace, .. } => elab_backtrace,
            ElabError::NotImplemented { elab_backtrace, .. } => elab_backtrace,
        }
    }

    /// Get the primary span (if any) from this error.
    pub fn span(&self) -> Option<&SourceRange<'db>> {
        match self {
            ElabError::TypeMismatch { span, .. } => span.as_ref(),
            ElabError::NotInScope { span, .. } => span.as_ref(),
            ElabError::CannotInfer { span, .. } => span.as_ref(),
            ElabError::UnificationFailure { span, .. } => span.as_ref(),
            ElabError::OccursCheck { span, .. } => span.as_ref(),
            ElabError::ScopeViolation { span, .. } => span.as_ref(),
            ElabError::UnsolvedMeta { span, .. } => span.as_ref(),
            ElabError::MetaAlreadySolved { .. } => None,
            ElabError::NotImplemented { span, .. } => span.as_ref(),
        }
    }

    /// Format this error with database access for nice file names.
    ///
    /// This should be used instead of `Display` when you have access to the database.
    pub fn display<Db>(&self, db: &'db Db) -> String
    where
        Db: salsa::Database,
    {
        let mut output = String::new();

        // Write the main error message
        match self {
            ElabError::TypeMismatch {
                expected,
                actual,
                span,
                ..
            } => {
                output.push_str("Type mismatch");
                // TODO: Use proper type formatting with GlobalEnv
                // For now, use Debug format as a placeholder
                output.push_str(&format!("\n  expected: {:?}", expected));
                output.push_str(&format!("\n  found:    {:?}", actual));
                if let Some(s) = span {
                    output.push_str(&format!("\n  at {}", s.display(db)));
                }
            }
            ElabError::NotInScope { name, span, .. } => {
                output.push_str(&format!("Not in scope: '{}'", name));
                if let Some(s) = span {
                    output.push_str(&format!("\n  at {}", s.display(db)));
                }
            }
            ElabError::CannotInfer { span, .. } => {
                output.push_str("Cannot infer type");
                if let Some(s) = span {
                    output.push_str(&format!("\n  at {}", s.display(db)));
                }
            }
            ElabError::UnificationFailure { lhs, rhs, span, .. } => {
                output.push_str("Unification failure");
                // TODO: Use proper value formatting with GlobalEnv
                output.push_str(&format!("\n  lhs: {:?}", lhs));
                output.push_str(&format!("\n  rhs: {:?}", rhs));
                if let Some(s) = span {
                    output.push_str(&format!("\n  at {}", s.display(db)));
                }
            }
            ElabError::OccursCheck { meta, span, .. } => {
                output.push_str(&format!("Occurs check failed for {:?}", meta));
                if let Some(s) = span {
                    output.push_str(&format!("\n  at {}", s.display(db)));
                }
            }
            ElabError::ScopeViolation { meta, span, .. } => {
                output.push_str(&format!("Scope violation for {:?}", meta));
                if let Some(s) = span {
                    output.push_str(&format!("\n  at {}", s.display(db)));
                }
            }
            ElabError::UnsolvedMeta { meta, span, .. } => {
                output.push_str(&format!("Unsolved metavariable {:?}", meta));
                if let Some(s) = span {
                    output.push_str(&format!("\n  at {}", s.display(db)));
                }
            }
            ElabError::MetaAlreadySolved { meta, .. } => {
                output.push_str(&format!("Meta {:?} already solved", meta));
            }
            ElabError::NotImplemented { feature, span, .. } => {
                output.push_str(&format!("Not implemented: {}", feature));
                if let Some(s) = span {
                    output.push_str(&format!("\n  at {}", s.display(db)));
                }
            }
        }

        // Add elaboration backtrace
        let backtrace = self.backtrace();
        if !backtrace.is_empty() {
            output.push_str("\n\nElaboration backtrace:");
            for (i, frame) in backtrace.iter().enumerate() {
                output.push_str(&format!(
                    "\n  {}. {} ({:?})",
                    i + 1,
                    frame.description,
                    frame.kind
                ));
                output.push_str(&format!("\n     at {}", frame.location.display(db)));
            }
        }

        output
    }
}

impl<'db> std::fmt::Display for ElabError<'db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Write the main error message
        // Note: We keep messages simple because the elaboration backtrace
        // provides all the context about what was being checked and where.
        match self {
            ElabError::TypeMismatch {
                expected,
                actual,
                span,
                ..
            } => {
                writeln!(f, "Type mismatch")?;
                writeln!(f, "  expected: {:?}", expected)?;
                writeln!(f, "  found:    {:?}", actual)?;
                if let Some(s) = span {
                    writeln!(f, "  at {:?}", s)?;
                }
            }
            ElabError::NotInScope { name, span, .. } => {
                writeln!(f, "Not in scope: '{}'", name)?;
                if let Some(s) = span {
                    writeln!(f, "  at {:?}", s)?;
                }
            }
            ElabError::CannotInfer { span, .. } => {
                writeln!(f, "Cannot infer type")?;
                if let Some(s) = span {
                    writeln!(f, "  at {:?}", s)?;
                }
            }
            ElabError::UnificationFailure { lhs, rhs, span, .. } => {
                writeln!(f, "Unification failure")?;
                writeln!(f, "  lhs: {:?}", lhs)?;
                writeln!(f, "  rhs: {:?}", rhs)?;
                if let Some(s) = span {
                    writeln!(f, "  at {:?}", s)?;
                }
            }
            ElabError::OccursCheck { meta, span, .. } => {
                writeln!(f, "Occurs check failed for {:?}", meta)?;
                if let Some(s) = span {
                    writeln!(f, "  at {:?}", s)?;
                }
            }
            ElabError::ScopeViolation { meta, span, .. } => {
                writeln!(f, "Scope violation for {:?}", meta)?;
                if let Some(s) = span {
                    writeln!(f, "  at {:?}", s)?;
                }
            }
            ElabError::UnsolvedMeta { meta, span, .. } => {
                writeln!(f, "Unsolved metavariable {:?}", meta)?;
                if let Some(s) = span {
                    writeln!(f, "  at {:?}", s)?;
                }
            }
            ElabError::MetaAlreadySolved { meta, .. } => {
                writeln!(f, "Metavariable {:?} already solved", meta)?;
            }
            ElabError::NotImplemented { feature, span, .. } => {
                writeln!(f, "Not implemented: {}", feature)?;
                if let Some(s) = span {
                    writeln!(f, "  at {:?}", s)?;
                }
            }
        }

        // Write elaboration backtrace if present
        let backtrace = self.backtrace();
        if !backtrace.is_empty() {
            writeln!(f)?;
            writeln!(f, "Elaboration backtrace:")?;
            for (i, frame) in backtrace.iter().enumerate() {
                writeln!(f, "  {}. {} ({:?})", i + 1, frame.description, frame.kind)?;
                writeln!(f, "     at {:?}", frame.location)?;
            }
        }

        Ok(())
    }
}
