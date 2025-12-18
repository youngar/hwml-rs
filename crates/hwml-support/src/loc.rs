use std::{ops::Range, path::PathBuf};

/// A line-and-byte-offset pair.
pub struct LinePosition {
    /// The line number.
    pub line: usize,
    /// The byte-offset, from the start of the line.
    pub column: usize,
}

/// The source of a piece of code.
pub enum Source {
    Path(PathBuf),
    Temp(String),
}

impl Source {
    pub fn title(&self) -> &str {
        match self {
            Source::Path(path) => path.to_str().unwrap_or("invalid-title"),
            Source::Temp(name) => name,
        }
    }
}

pub struct SourceId(pub usize);

/// A source and a range.
pub struct SourceRange {
    pub range: Range<usize>,
    pub source: SourceId,
}

/// A value that has an associated range of source text.
pub trait HasRange {
    fn range(&self) -> Range<usize>;
}

/// A value that has an associated range of source text, and knows the ID of the source file.
pub trait HasSourceRange {
    fn source_range(&self) -> SourceRange;
}

impl<T> HasRange for T
where
    T: HasSourceRange,
{
    fn range(&self) -> Range<usize> {
        self.source_range().range
    }
}
