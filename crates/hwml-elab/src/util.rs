use crate::State;
use hwml_core::common::*;
use hwml_core::syn::basic::*;

/// Walk the term, raising all bound variables by a certain amount. This is used
/// when subsituting an argument under a binder, we need to raise the argument
/// so that free variables remain free. The amount is the number of binders we are
/// moving under.
pub fn raise(tm: RcSyntax, amount: usize) -> RcSyntax {
    fn r(tm: RcSyntax, depth: usize, amount: usize) -> RcSyntax {
        match &*tm {
            Syntax::Variable(var) if Into::<usize>::into(var.index) >= depth => {
                Syntax::variable_rc(var.index.raise(amount))
            }
            Syntax::Application(app) => {
                let fun = r(app.function.clone(), depth, amount);
                let arg = r(app.argument.clone(), depth, amount);
                Syntax::application_rc(fun, arg)
            }
            Syntax::Lambda(lam) => {
                let body = r(lam.body.clone(), depth + 1, amount);
                Syntax::lambda_rc(body)
            }
            Syntax::Pi(pi) => {
                let source = r(pi.source.clone(), depth, amount);
                let target = r(pi.target.clone(), depth + 1, amount);
                Syntax::pi_rc(source, target)
            }
            Syntax::Metavariable(_) => todo!("not sure if we should do anything here"),
            _ => tm,
        }
    }
    r(tm, 0, amount)
}

pub fn subst_metavariable(meta: Metavariable, from: Index, to: RcSyntax) -> RcSyntax {
    // Rewrite the closure to substitute the variable.
    let values = meta
        .closure
        .values
        .iter()
        .map(|term| subst(term.clone(), from, to.clone()))
        .collect();
    let closure = Closure::with_values(values);
    Syntax::metavariable_rc(meta.id, closure)
}

pub fn subst_variable(var: Variable, from: Index, to: RcSyntax) -> RcSyntax {
    if var.index == from {
        to
    } else {
        Syntax::variable_rc(var.index)
    }
}

pub fn subst(tm: RcSyntax, from: Index, to: RcSyntax) -> RcSyntax {
    match &*tm {
        Syntax::Metavariable(meta) => subst_metavariable(meta.clone(), from, to),
        Syntax::Variable(var) => subst_variable(var.clone(), from, to),
        _ => todo!(),
    }
}

/* pub fn subst_metavariable(tm: RcSyntax, from: MetavariableId, to: RcSyntax) -> RcSyntax {
    match *tm {
        Syntax::Metavariable(meta) => subst_metavariable(meta.clone(), from, to),
        Syntax::Variable(var) => subst_variable(var.clone(), from, to),
        syntax => Rc::new(syntax),
    }
}
 */

pub fn whnf(_state: &mut State, _tm: RcSyntax) -> RcSyntax {
    todo!()
}
