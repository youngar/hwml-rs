//! Error types for the CIRCT backend.

use thiserror::Error;

/// Result type for CIRCT backend operations.
pub type Result<T> = std::result::Result<T, Error>;

/// Errors that can occur during CIRCT compilation.
#[derive(Error, Debug)]
pub enum Error {
    /// Failed to initialize MLIR context
    #[error("Failed to initialize MLIR context: {0}")]
    ContextInitialization(String),

    /// Failed to register a dialect
    #[error("Failed to register dialect {dialect}: {reason}")]
    DialectRegistration { dialect: String, reason: String },

    /// Translation error from HWML to CIRCT
    #[error("Translation error: {0}")]
    Translation(String),

    /// Verilog export error
    #[error("Failed to export Verilog: {0}")]
    VerilogExport(String),

    /// Pass execution failed
    #[error("Pass failed: {0}")]
    PassFailed(String),

    /// Unsupported HWML feature
    #[error("Unsupported HWML feature: {0}")]
    UnsupportedFeature(String),

    /// MLIR operation error
    #[error("MLIR operation error: {0}")]
    MlirOperation(String),

    /// Translation error (legacy)
    #[error("Translation error: {0}")]
    TranslationError(String),

    /// Unsupported construct
    #[error("Unsupported construct: {0}")]
    UnsupportedConstruct(String),

    /// Generic error
    #[error("{0}")]
    Other(String),
}

impl From<String> for Error {
    fn from(s: String) -> Self {
        Error::Other(s)
    }
}

impl From<&str> for Error {
    fn from(s: &str) -> Self {
        Error::Other(s.to_string())
    }
}
