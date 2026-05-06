use crate::*;

pub use std::ops::Range;

/// Identifies a single source file within a library.
#[salsa::interned]
pub struct SourceFileId {
    /// Interned library name (e.g. "my-hardware").
    pub library_name: Word<'db>,
    /// Interned canonical absolute path to the file.
    pub canonical_path: Word<'db>,
}

impl<'db> SourceFileId<'db> {
    pub fn path_str<Db>(&self, db: &'db Db) -> &'db str
    where
        Db: salsa::Database,
    {
        self.canonical_path(db).text(db)
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum SourceInfo<'db> {
    /// A real source file, identified by library name + canonical path.
    File(SourceFileId<'db>),
    /// Synthetic / compiler-generated code; label is for display only.
    Synthetic(Word<'db>),
}

impl<'db> SourceInfo<'db> {
    pub fn title<Db>(&self, db: &'db Db) -> &'db str
    where
        Db: salsa::Database,
    {
        match self {
            SourceInfo::File(id) => id.path_str(db),
            SourceInfo::Synthetic(name) => name.text(db),
        }
    }
}

#[salsa::interned]
pub struct Source {
    pub info: SourceInfo<'db>,
}

impl<'db> Source<'db> {
    pub fn title<Db>(&self, db: &'db Db) -> &'db str
    where
        Db: salsa::Database,
    {
        self.info(db).title(db)
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct SourceRange<'db> {
    pub source: Source<'db>,
    pub range: Range<usize>,
}

impl<'db> SourceRange<'db> {
    pub fn new(source: Source<'db>, range: Range<usize>) -> SourceRange<'db> {
        SourceRange { source, range }
    }
}

pub trait HasSourceRange<'db> {
    fn source_range(&self) -> Option<SourceRange<'db>>;
}

impl<'db> HasSourceRange<'db> for SourceRange<'db> {
    fn source_range(&self) -> Option<SourceRange<'db>> {
        self.clone().into()
    }
}

pub struct WithSourceRange<'db, A>(pub A, pub Option<SourceRange<'db>>);

impl<'db, A> HasSourceRange<'db> for WithSourceRange<'db, A> {
    fn source_range(&self) -> Option<SourceRange<'db>> {
        self.1.clone()
    }
}

// ============================================================================
// New Location Infrastructure (Line:Column based)
// ============================================================================

/// A position in source code (1-based line and column).
/// Column is a byte offset within the line (also 1-based).
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Position {
    /// Line number (1-based). Line 1 is the first line.
    pub line: u32,
    /// Column number (1-based byte offset). Column 1 is the first character.
    pub column: u32,
}

impl Position {
    pub fn new(line: u32, column: u32) -> Self {
        Position { line, column }
    }

    /// Convert from 0-based (internal LineInfo format) to 1-based (MLIR/Location format)
    pub fn from_zero_based(line: usize, column: usize) -> Self {
        Position {
            line: (line + 1) as u32,
            column: (column + 1) as u32,
        }
    }

    /// Convert to 0-based (for LineInfo lookups)
    pub fn to_zero_based(&self) -> (usize, usize) {
        ((self.line - 1) as usize, (self.column - 1) as usize)
    }

    /// Convert to LSP Position (0-based line, 0-based UTF-16 column)
    /// Note: This returns byte-based column; LSP servers must convert to UTF-16
    pub fn to_lsp_position(&self) -> (u32, u32) {
        (self.line - 1, self.column - 1)
    }
}

/// Location data: either a file range or synthetic.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum LocationKind<'db> {
    /// A real source range with file, start line:col, and end line:col (1-based).
    /// Maps directly to MLIR's FileLineColRange.
    FileLineColRange {
        file: SourceFileId<'db>,
        start_line: u32,
        start_column: u32,
        end_line: u32,
        end_column: u32,
    },
    /// Synthetic/compiler-generated location with a descriptive label.
    /// Examples: "implicit_argument", "desugared", "metavar_?42"
    Synthetic { label: Word<'db> },
}

/// A location in source code, interned for efficiency.
/// This is the primary location type used throughout HWML.
#[salsa::interned]
pub struct Location {
    pub kind: LocationKind<'db>,
}

impl<'db> Location<'db> {
    /// Create a file-based location from line:column positions
    pub fn file_range<Db>(
        db: &'db Db,
        file: SourceFileId<'db>,
        start: Position,
        end: Position,
    ) -> Self
    where
        Db: salsa::Database,
    {
        Location::new(
            db,
            LocationKind::FileLineColRange {
                file,
                start_line: start.line,
                start_column: start.column,
                end_line: end.line,
                end_column: end.column,
            },
        )
    }

    /// Create a file-based location from line:column values
    pub fn file_range_values<Db>(
        db: &'db Db,
        file: SourceFileId<'db>,
        start_line: u32,
        start_column: u32,
        end_line: u32,
        end_column: u32,
    ) -> Self
    where
        Db: salsa::Database,
    {
        Location::new(
            db,
            LocationKind::FileLineColRange {
                file,
                start_line,
                start_column,
                end_line,
                end_column,
            },
        )
    }

    /// Create a synthetic location with a label
    pub fn synthetic<Db>(db: &'db Db, label: &str) -> Self
    where
        Db: salsa::Database,
    {
        let label_word = Word::new(db, label);
        Location::new(db, LocationKind::Synthetic { label: label_word })
    }

    /// Get the file ID if this is a file-based location
    pub fn file<Db>(&self, db: &'db Db) -> Option<SourceFileId<'db>>
    where
        Db: salsa::Database,
    {
        match self.kind(db) {
            LocationKind::FileLineColRange { file, .. } => Some(file),
            LocationKind::Synthetic { .. } => None,
        }
    }

    /// Check if this is a synthetic location
    pub fn is_synthetic<Db>(&self, db: &'db Db) -> bool
    where
        Db: salsa::Database,
    {
        matches!(self.kind(db), LocationKind::Synthetic { .. })
    }

    /// Get start position if this is a file-based location
    pub fn start_position<Db>(&self, db: &'db Db) -> Option<Position>
    where
        Db: salsa::Database,
    {
        match self.kind(db) {
            LocationKind::FileLineColRange {
                start_line,
                start_column,
                ..
            } => Some(Position::new(start_line, start_column)),
            LocationKind::Synthetic { .. } => None,
        }
    }

    /// Get end position if this is a file-based location
    pub fn end_position<Db>(&self, db: &'db Db) -> Option<Position>
    where
        Db: salsa::Database,
    {
        match self.kind(db) {
            LocationKind::FileLineColRange {
                end_line,
                end_column,
                ..
            } => Some(Position::new(end_line, end_column)),
            LocationKind::Synthetic { .. } => None,
        }
    }

    /// Create a Location from a byte range using LineInfo for conversion
    pub fn from_byte_range<Db>(
        db: &'db Db,
        file: SourceFileId<'db>,
        byte_range: Range<usize>,
        line_info: &hwml_support::LineInfo,
    ) -> Self
    where
        Db: salsa::Database,
    {
        let (start_line_0, start_col_0) = line_info.loc(byte_range.start);
        let (end_line_0, end_col_0) = line_info.loc(byte_range.end);

        let start = Position::from_zero_based(start_line_0, start_col_0);
        let end = Position::from_zero_based(end_line_0, end_col_0);

        Location::file_range(db, file, start, end)
    }
}
