use crate::syn::RcSyntax;
use std::collections::HashMap;

pub struct Global<'db> {
    globals: HashMap<String, RcSyntax<'db>>,
}
