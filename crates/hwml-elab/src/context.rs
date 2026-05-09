//! Elaboration context for tracking source locations and backtrace.
//!
//! This module provides the infrastructure for Phase 4 elaboration backtrace.
//! The `ElabContext` tracks:
//! - The current source file being elaborated
//! - The current byte range within that file
//! - A stack of elaboration frames for backtrace

use hwml_core::{Source, SourceRange};
use std::ops::Range;

/// Elaboration context that tracks source location and backtrace.
///
/// This is stored in `Elaborator` and updated by trace guards as elaboration proceeds.
#[derive(Clone, Debug)]
pub struct ElabContext<'db> {
    /// Stack of elaboration frames for backtrace
    trace_stack: Vec<ElabFrame<'db>>,

    /// Current source file being elaborated
    /// Updated when crossing file boundaries (imports, etc.)
    current_source: Source<'db>,

    /// Current byte range within the source file
    /// Updated by trace guards
    current_byte_range: Option<Range<usize>>,
}

/// A single frame in the elaboration backtrace.
#[derive(Clone, Debug)]
pub struct ElabFrame<'db> {
    pub description: String,
    pub location: SourceRange<'db>,
    pub kind: ElabFrameKind,
}

/// The kind of elaboration operation being traced.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ElabFrameKind {
    /// Checking an expression against an expected type
    CheckingExpression,
    /// Synthesizing a type for an expression
    SynthesizingType,
    /// Switching from check mode to synth mode (the "switch rule")
    /// This happens when we need to infer a type and then check it matches
    SwitchingToSynth,
    /// Checking a definition
    CheckingDefinition { name: String },
    /// Checking a function application
    CheckingFunctionApplication,
    /// Checking a return type
    CheckingReturnType,
    /// Solving constraints
    SolvingConstraints,
    /// Checking a constructor
    CheckingConstructor { name: String },
    /// Elaborating a file
    ElaboratingFile { path: String },
}

/// RAII guard that automatically pops a trace frame when dropped.
///
/// This ensures that trace frames are cleaned up even on early returns or errors.
pub struct TraceGuard<'a, 'db> {
    context: &'a mut ElabContext<'db>,
}

impl<'a, 'db> Drop for TraceGuard<'a, 'db> {
    fn drop(&mut self) {
        self.context.trace_stack.pop();
    }
}

/// Owning RAII guard for use with scoped trace operations.
///
/// This guard stores a function pointer to pop the trace and doesn't
/// borrow the context, allowing it to be used more flexibly.
pub struct ScopedTraceGuard<F: FnOnce()> {
    cleanup: Option<F>,
}

impl<F: FnOnce()> ScopedTraceGuard<F> {
    pub fn new(cleanup: F) -> Self {
        ScopedTraceGuard {
            cleanup: Some(cleanup),
        }
    }
}

impl<F: FnOnce()> Drop for ScopedTraceGuard<F> {
    fn drop(&mut self) {
        if let Some(cleanup) = self.cleanup.take() {
            cleanup();
        }
    }
}

impl<'db> ElabContext<'db> {
    /// Create a new elaboration context for a file.
    ///
    /// # Arguments
    /// * `source` - The source file being elaborated
    pub fn new(source: Source<'db>) -> Self {
        ElabContext {
            trace_stack: Vec::new(),
            current_source: source,
            current_byte_range: None,
        }
    }

    /// Push a trace frame with a byte range.
    ///
    /// The byte range is combined with the current source to create a `SourceRange`.
    /// Returns a guard that automatically pops the frame when dropped.
    ///
    /// # Arguments
    /// * `desc` - Human-readable description of the operation
    /// * `byte_range` - Byte range within the current source file
    /// * `kind` - The kind of elaboration operation
    pub fn trace<'a>(
        &'a mut self,
        desc: impl Into<String>,
        byte_range: Range<usize>,
        kind: ElabFrameKind,
    ) -> TraceGuard<'a, 'db> {
        // Create SourceRange using current source
        let location = SourceRange::new(self.current_source, byte_range.clone());

        // Update current byte range
        self.current_byte_range = Some(byte_range);

        self.trace_stack.push(ElabFrame {
            description: desc.into(),
            location,
            kind,
        });

        TraceGuard { context: self }
    }

    /// Push a trace frame with a pre-built SourceRange.
    ///
    /// This is used when crossing file boundaries, where we need to update
    /// the current source to match the new location.
    ///
    /// # Arguments
    /// * `desc` - Human-readable description of the operation
    /// * `location` - Pre-built source range (possibly from a different file)
    /// * `kind` - The kind of elaboration operation
    pub fn trace_with_source<'a>(
        &'a mut self,
        desc: impl Into<String>,
        location: SourceRange<'db>,
        kind: ElabFrameKind,
    ) -> TraceGuard<'a, 'db> {
        // Update current source to match the new location
        self.current_source = location.source;
        self.current_byte_range = Some(location.range.clone());

        self.trace_stack.push(ElabFrame {
            description: desc.into(),
            location,
            kind,
        });

        TraceGuard { context: self }
    }

    /// Get the current source file.
    ///
    /// This is used when elaborating sub-expressions that need to inherit the parent's source.
    pub fn source(&self) -> Source<'db> {
        self.current_source
    }

    /// Get the current source location (source + byte range).
    ///
    /// Returns `None` if no byte range has been set yet.
    pub fn current_location(&self) -> Option<SourceRange<'db>> {
        self.current_byte_range.as_ref().map(|range| {
            SourceRange::new(self.current_source, range.clone())
        })
    }

    /// Get a snapshot of the current backtrace.
    ///
    /// This is used when constructing errors to capture the elaboration context.
    pub fn snapshot(&self) -> Vec<ElabFrame<'db>> {
        self.trace_stack.clone()
    }

    /// Get the current depth of the trace stack (for debugging).
    pub fn depth(&self) -> usize {
        self.trace_stack.len()
    }

    /// Push a trace frame without returning a guard.
    ///
    /// This is useful when RAII guards cause borrow checker issues.
    /// You MUST manually call `pop_trace()` when done!
    ///
    /// # Arguments
    /// * `desc` - Human-readable description of the operation
    /// * `byte_range` - Byte range within the current source file
    /// * `kind` - The kind of elaboration operation
    pub fn push_trace(
        &mut self,
        desc: impl Into<String>,
        byte_range: Range<usize>,
        kind: ElabFrameKind,
    ) {
        let location = SourceRange::new(self.current_source, byte_range.clone());
        self.current_byte_range = Some(byte_range);

        self.trace_stack.push(ElabFrame {
            description: desc.into(),
            location,
            kind,
        });
    }

    /// Pop the most recent trace frame.
    ///
    /// This should be called after `push_trace()` when the operation completes.
    pub fn pop_trace(&mut self) {
        self.trace_stack.pop();
    }

    /// Temporarily change the source file.
    ///
    /// This is used for cross-file operations like imports, where we need to
    /// elaborate code from a different file.
    ///
    /// The source is automatically restored when the closure returns.
    ///
    /// # Arguments
    /// * `source` - The new source file
    /// * `f` - Closure to run with the new source
    pub fn with_source<R>(
        &mut self,
        source: Source<'db>,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let old_source = self.current_source;
        self.current_source = source;
        let result = f(self);
        self.current_source = old_source;
        result
    }

    /// Run a closure with a trace frame, automatically popping on exit.
    ///
    /// This is the preferred way to add trace frames as it handles cleanup
    /// even on early returns or errors, and doesn't run into borrow checker
    /// issues like RAII guards.
    ///
    /// # Arguments
    /// * `desc` - Human-readable description of the operation
    /// * `byte_range` - Byte range within the current source file
    /// * `kind` - The kind of elaboration operation
    /// * `f` - Closure to run with the trace frame active
    ///
    /// # Example
    /// ```ignore
    /// elab.context.with_trace(
    ///     "checking definition 'foo'",
    ///     0..10,
    ///     ElabFrameKind::CheckingDefinition { name: "foo".into() },
    ///     |ctx| {
    ///         // Do elaboration work here
    ///         // Trace frame automatically popped at end
    ///     }
    /// )
    /// ```
    pub fn with_trace<R>(
        &mut self,
        desc: impl Into<String>,
        byte_range: Range<usize>,
        kind: ElabFrameKind,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        // Push the frame
        let location = SourceRange::new(self.current_source, byte_range.clone());
        self.current_byte_range = Some(byte_range);

        self.trace_stack.push(ElabFrame {
            description: desc.into(),
            location,
            kind,
        });

        // Run the closure
        let result = f(self);

        // Pop the frame
        self.trace_stack.pop();

        result
    }
}
