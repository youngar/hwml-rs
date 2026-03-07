use crate::syn::RcSyntax;
use std::collections::HashMap;

#[allow(dead_code)]
pub struct Global<'db> {
    #[allow(dead_code)]
    globals: HashMap<String, RcSyntax<'db>>,
}
