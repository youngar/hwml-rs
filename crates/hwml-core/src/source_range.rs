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

    /// Format this source range for display, including the file name.
    ///
    /// Returns a string like "adder.hwml:10..50" or "synthetic:0..10"
    pub fn display<Db>(&self, db: &'db Db) -> String
    where
        Db: salsa::Database,
    {
        let full_path = self.source.title(db);

        // Extract just the file name from the path for cleaner display
        let file_name = if let Some(pos) = full_path.rfind('/') {
            &full_path[pos + 1..]
        } else if let Some(pos) = full_path.rfind('\\') {
            &full_path[pos + 1..]
        } else {
            full_path
        };

        format!("{}:{}..{}", file_name, self.range.start, self.range.end)
    }
}

impl<'db> std::fmt::Display for SourceRange<'db> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Note: We can't access db here, so we format as Debug for now.
        // For proper display with file names, use a helper function that takes db.
        write!(f, "{:?}", self)
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
