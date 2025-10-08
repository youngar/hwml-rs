/// Salsa-based interned string for the hwml-core AST.
#[salsa::interned]
pub struct InternedString {
    #[return_ref]
    pub text: String,
}
