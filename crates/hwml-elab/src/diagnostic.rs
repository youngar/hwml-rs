use crate::*;

#[derive(Clone, Debug)]
pub struct Diagnostic {
    pub location: Location,
    pub message: String,
}
