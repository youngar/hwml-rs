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
///
/// This is a simple u32 ID that can be used without a database.
/// For now, we use a simple counter-based approach.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Location(u32);

impl Location {
    /// Sentinel for synthetic syntax (quotation, elaboration, tests).
    pub const UNKNOWN: Location = Location(0);

    /// Create a new location with a given ID.
    pub fn new(id: u32) -> Self {
        Location(id)
    }

    /// Get the ID of this location.
    pub fn id(&self) -> u32 {
        self.0
    }
}

impl std::fmt::Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if *self == Location::UNKNOWN {
            write!(f, "<unknown>")
        } else {
            write!(f, "loc#{}", self.0)
        }
    }
}
