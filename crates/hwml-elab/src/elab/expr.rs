use hwml_core::{RcSyntax, ty::RcTy};
use hwml_surface::Expression;

use crate::{error::ElabError, kernel::Checked};

use super::Elaborator;

/// Pull-mode: infer (term, type) for a surface expression.
pub fn synth<'a, 'db>(
    elab: &mut Elaborator<'a, 'db>,
    expr: &Expression,
) -> Result<Checked<(RcSyntax<'db>, RcTy<'db>)>, ElabError<'db>> {
    match expr {
        Expression::Universe(_u) => {
            // McBride/Sterling: fresh ?u : UniverseType; return UniverseCode(?u).
            Ok(elab.kernel.synth_universe(None))
        }
        Expression::Id(id) => {
            let name = String::from_utf8_lossy(&id.value).to_string();
            match elab.kernel.ctx.lookup(&name) {
                Some((idx, _entry)) => elab.kernel.synth_var(idx),
                None => Err(ElabError::NotInScope { name, span: None }),
            }
        }
        Expression::App(app) => {
            // First element is function, rest are arguments.
            let mut elements = app.elements.iter();
            let fun_expr = elements.next().ok_or(ElabError::CannotInfer { span: None })?;
            let mut result = synth(elab, fun_expr)?;
            for arg in elements {
                result = elab.kernel.synth_app(result, arg)?;
            }
            Ok(result)
        }
        Expression::Pi(_pi) => {
            todo!("Pi elaboration: Phase 2")
        }
        Expression::Arrow(_arrow) => {
            todo!("Arrow elaboration: Phase 2")
        }
        Expression::LetIn(_let_in) => {
            todo!("LetIn elaboration: Phase 2")
        }
        Expression::Underscore(_) => {
            todo!("Underscore (fresh meta) elaboration: Phase 2")
        }
        Expression::Paren(p) => synth(elab, &p.expr),
        _ => Err(ElabError::CannotInfer { span: None }),
    }
}

/// Push-mode: check expression against expected type.
/// Falls through to synth + expect for non-intro forms.
pub fn check<'a, 'db>(
    elab: &mut Elaborator<'a, 'db>,
    expr: &Expression,
    expected_ty: RcTy<'db>,
) -> Result<Checked<RcSyntax<'db>>, ElabError<'db>> {
    match expr {
        Expression::Fun(_fun) => {
            // Special-cased: check against Pi without emitting unnecessary meta.
            todo!("Fun check against Pi: Phase 2")
        }
        _ => {
            // Fallback: synth then expect.
            let synth_result = synth(elab, expr)?;
            Ok(elab.kernel.expect(expected_ty, synth_result))
        }
    }
}
