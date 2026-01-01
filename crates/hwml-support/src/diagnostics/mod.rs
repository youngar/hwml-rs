use crate::loc::*;

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

impl std::string::ToString for Severity {
    fn to_string(&self) -> String {
        self.str().to_owned()
    }
}

pub struct Located<T>(pub T, pub Option<SourceRange>);

pub type Message = String;

/// A stack (backwards list) of noted positions in user code.
pub type Trace = Vec<Located<Message>>;

pub struct Diagnostic<T> {
    pub message: T,
    pub severity: Severity,
    pub explanation: Located<Message>,
    pub trace: Trace,
    pub remarks: Vec<Located<Message>>,
}

pub mod markup;
pub mod reporter;
