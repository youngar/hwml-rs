use crate::*;
use hwml_core::*;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum Severity {
    Hint,
    Info,
    Warning,
    Error,
    Bug,
}

impl Severity {
    pub fn str(self) -> &'static str {
        match self {
            Severity::Hint => "hint",
            Severity::Info => "info",
            Severity::Warning => "warning",
            Severity::Error => "error",
            Severity::Bug => "bug",
        }
    }
}

impl std::fmt::Display for Severity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.str())
    }
}

pub type Message = String;

/// A stack (backwards list) of noted positions in user code.
pub type Trace<'db> = Vec<WithSourceRange<'db, Message>>;

pub struct Diagnostic<'db, T> {
    pub message: T,
    pub severity: Severity,
    pub explanation: WithSourceRange<'db, Message>,
    pub trace: Trace<'db>,
    pub remarks: Vec<WithSourceRange<'db, Message>>,
}
