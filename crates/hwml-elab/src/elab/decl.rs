use hwml_core::{ConstantDecl, TypeConstructorDecl};

use crate::error::ElabError;

use super::Elaborator;

/// Elaborate a top-level constant definition (`def name : ty = body`).
pub fn elab_constant<'a, 'db>(
    _elab: &mut Elaborator<'a, 'db>,
    _decl: &ConstantDecl<'db>,
) -> Result<(), ElabError<'db>> {
    todo!("elab_constant: Phase 3")
}

/// Elaborate a top-level inductive type declaration.
pub fn elab_inductive<'a, 'db>(
    _elab: &mut Elaborator<'a, 'db>,
    _decl: &TypeConstructorDecl<'db>,
) -> Result<(), ElabError<'db>> {
    todo!("elab_inductive: Phase 3")
}
