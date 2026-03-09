//! MLIR-style location tracking using Salsa interning.
//!
//! Locations are opaque Copy-able identifiers in the Core IR (just a u32) that
//! can be queried through Salsa for source file information and snippets. This
//! keeps the Core IR pure while enabling rich diagnostics.

/// A source file tracked by Salsa.
#[salsa::input]
pub struct SourceFile {
    #[return_ref]
    pub path: String,

    #[return_ref]
    pub text: String,
}

/// Location data: either a physical span or unknown/synthetic.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LocationData {
    Physical {
        file: SourceFile,
        start: u32,
        end: u32,
    },
    Unknown,
}

/// Salsa-interned location ID (Copy-able u32 wrapper).
#[salsa::interned]
pub struct Location {
    #[return_ref]
    pub data: LocationData,
}

impl Location {
    /// Sentinel for synthetic syntax (quotation, elaboration, tests).
    /// Doesn't require a database.
    pub const UNKNOWN: Location = unsafe {
        // SAFETY: Salsa guarantees LocationData::Unknown always gets ID 0.
        std::mem::transmute::<u32, Location>(0u32)
    };

    pub fn unknown(db: &dyn salsa::Database) -> Self {
        Location::new(db, LocationData::Unknown)
    }

    pub fn physical(db: &dyn salsa::Database, file: SourceFile, start: u32, end: u32) -> Self {
        Location::new(db, LocationData::Physical { file, start, end })
    }

    pub fn snippet<'db>(&self, db: &'db dyn salsa::Database) -> Option<&'db str> {
        match self.data(db) {
            LocationData::Physical { file, start, end } => {
                file.text(db).get(*start as usize..*end as usize)
            }
            LocationData::Unknown => None,
        }
    }

    pub fn display(&self, db: &dyn salsa::Database) -> String {
        match self.data(db) {
            LocationData::Physical { file, start, end } => {
                format!("{}:{}..{}", file.path(db), start, end)
            }
            LocationData::Unknown => "<unknown>".to_string(),
        }
    }
}
