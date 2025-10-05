use crate::syn::*;
use elegance::{Printer, Render};
use hwml_support::pp::{print_binder, print_lhs, print_rhs, PPTerm, State, TermPrec, PP};

const NO_PREC: Option<usize> = None;
const CHECK_LHS: Option<usize> = Some(2);
const CHECK_RHS: Option<usize> = Some(2);
const PI_LHS: Option<usize> = NO_PREC;
const PI_RHS: Option<usize> = Some(3);
const LAMBDA_LHS: Option<usize> = NO_PREC;
const LAMBDA_RHS: Option<usize> = Some(3);
const APP_LHS: Option<usize> = Some(4);
const APP_RHS: Option<usize> = Some(5);
const LIFT_LHS: Option<usize> = NO_PREC;
const LIFT_RHS: Option<usize> = Some(5);
const QUOTE_LHS: Option<usize> = NO_PREC;
const QUOTE_RHS: Option<usize> = Some(5);
const HARROW_LHS: Option<usize> = Some(4);
const HARROW_RHS: Option<usize> = Some(3);
const SPLICE_LHS: Option<usize> = NO_PREC;
const SPLICE_RHS: Option<usize> = Some(5);

impl PP for Closure {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.text("[")?;
        p.cgroup(1, |p| {
            for (i, value) in self.values.iter().enumerate() {
                if i > 0 {
                    p.text(",")?;
                    p.space()?;
                }
                value.print(st, p)?;
            }
            Ok(())
        })?;
        p.text("]")?;
        Ok(())
    }
}

impl PP for Syntax {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        match self {
            Syntax::Constant(constant) => constant.print(st, p),
            Syntax::Variable(var) => var.print(st, p),
            Syntax::Check(chk) => chk.print(st, p),
            Syntax::Pi(pi) => pi.print(st, p),
            Syntax::Lambda(lam) => lam.print(st, p),
            Syntax::Application(app) => app.print(st, p),
            Syntax::Universe(uni) => uni.print(st, p),
            Syntax::Metavariable(meta) => meta.print(st, p),
            Syntax::Lift(lift) => lift.print(st, p),
            Syntax::Quote(quote) => quote.print(st, p),
            Syntax::HArrow(harrow) => harrow.print(st, p),
        }
    }
}

impl PP for Constant {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.text("@")?;
        self.name.print(st, p)
    }
}

impl PP for Variable {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        if self.index.is_bound(st.depth()) {
            p.text_owned(&format!("{}", self.index.to_level(st.depth())))
        } else {
            p.text_owned(&format!("{}", self.index.to_negative_level(st.depth())))
        }
    }
}

impl PPTerm for Check {
    const PREC: TermPrec = (CHECK_LHS, CHECK_RHS);
    fn print_content<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.igroup(0, |p| {
            print_lhs(st, p, &*self.term, CHECK_LHS)?;
            p.text(" :")?;
            p.space()?;
            print_rhs(st, p, &*self.ty, CHECK_RHS)
        })
    }
}

impl PPTerm for Pi {
    const PREC: TermPrec = (PI_LHS, PI_RHS);
    fn print_content<R: Render>(&self, mut st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.cgroup(0, |p| {
            let mut next = self;
            p.text("∀ ")?;
            p.cgroup(2, |p| {
                loop {
                    p.text("(")?;
                    p.cgroup(1, |p| {
                        print_binder(st, p)?;
                        p.text(" :")?;
                        p.space()?;
                        print_rhs(st, p, &*next.source, CHECK_RHS)
                    })?;
                    p.text(")")?;
                    st = st.inc_depth();

                    match &*next.target {
                        Syntax::Pi(pi) => next = pi,
                        _ => break,
                    }
                    p.space()?;
                }
                Ok(())
            })?;
            p.text(" →")?;
            p.space()?;
            print_rhs(st, p, &*next.target, PI_RHS)
        })
    }
}

impl PPTerm for Lambda {
    const PREC: TermPrec = (LAMBDA_LHS, LAMBDA_RHS);

    fn print_content<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.cgroup(2, |p| {
            let mut next = self;
            let mut st = st;
            p.cgroup(0, |p| {
                p.text("λ ")?;
                loop {
                    print_binder(st, p)?;
                    st = st.inc_depth();
                    match &*next.body {
                        Syntax::Lambda(lam) => next = lam,
                        _ => break,
                    }
                    p.space()?;
                }
                p.space()?;
                p.text("→")
            })?;
            p.space()?;
            print_rhs(st, p, &*next.body, LAMBDA_RHS)
        })
    }
}

impl PPTerm for Application {
    const PREC: TermPrec = (APP_LHS, APP_RHS);

    fn print_content<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.cgroup(0, |p| {
            print_lhs(st, p, &*self.function, APP_LHS)?;
            p.space()?;
            print_rhs(st, p, &*self.argument, APP_RHS)
        })
    }
}

impl PP for Universe {
    fn print<R: Render>(&self, _st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.text_owned(&format!("𝒰{}", self.level))
    }
}

impl PP for Metavariable {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.text_owned(&format!("{}", self.id))?;
        if !self.closure.is_empty() {
            self.closure.print(st, p)
        } else {
            Ok(())
        }
    }
}

impl PPTerm for Lift {
    const PREC: TermPrec = (LIFT_LHS, LIFT_RHS);

    fn print_content<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.text("^")?;
        print_rhs(st, p, &*self.tm, LIFT_RHS)
    }
}

impl PPTerm for Quote {
    const PREC: TermPrec = (QUOTE_LHS, QUOTE_RHS);

    fn print_content<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.text("'")?;
        print_rhs(st, p, &*self.tm, QUOTE_RHS)
    }
}

impl PPTerm for HArrow {
    const PREC: TermPrec = (HARROW_LHS, HARROW_RHS);

    fn print_content<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.cgroup(0, |p| {
            print_lhs(st, p, &*self.source, HARROW_LHS)?;
            p.space()?;
            p.text("→")?;
            p.space()?;
            print_rhs(st, p, &*self.target, HARROW_RHS)
        })
    }
}

impl PP for HSyntax {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        match self {
            HSyntax::HConstant(constant) => constant.print(st, p),
            HSyntax::HVariable(variable) => variable.print(st, p),
            HSyntax::HCheck(check) => check.print(st, p),
            HSyntax::HLambda(lambda) => lambda.print(st, p),
            HSyntax::HApplication(application) => application.print(st, p),
            HSyntax::Splice(splice) => splice.print(st, p),
        }
    }
}

impl PPTerm for HCheck {
    const PREC: TermPrec = Check::PREC;

    fn print_content<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.igroup(0, |p| {
            print_lhs(st, p, &*self.term, CHECK_LHS)?;
            p.text(" :")?;
            p.space()?;
            print_rhs(st, p, &*self.ty, CHECK_RHS)
        })
    }
}

impl PPTerm for HLambda {
    const PREC: TermPrec = Lambda::PREC;

    fn print_content<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.cgroup(2, |p| {
            let mut next = self;
            let mut st = st;
            p.cgroup(0, |p| {
                p.text("λ ")?;
                loop {
                    print_binder(st, p)?;
                    st = st.inc_depth();
                    match &*next.body {
                        HSyntax::HLambda(lam) => next = lam,
                        _ => break,
                    }
                    p.space()?;
                }
                p.space()?;
                p.text("→")
            })?;
            p.space()?;
            print_rhs(st, p, &*next.body, LAMBDA_RHS)
        })
    }
}

impl PPTerm for HApplication {
    const PREC: TermPrec = Application::PREC;

    fn print_content<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.cgroup(0, |p| {
            print_lhs(st, p, &*self.function, APP_LHS)?;
            p.space()?;
            print_rhs(st, p, &*self.argument, APP_RHS)
        })
    }
}

impl PPTerm for Splice {
    const PREC: TermPrec = (SPLICE_LHS, SPLICE_RHS);

    fn print_content<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.text("~")?;
        print_rhs(st, p, &*self.term, SPLICE_RHS)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{Index, UniverseLevel};
    use crate::syn::{MetavariableId, Syntax};
    use hwml_support::pp::dump_to_str;
    use insta::assert_snapshot;

    #[test]
    fn test_print_ast_to_stdout() {
        // Simple constant: @42
        assert_snapshot!(
            dump_to_str(&Syntax::constant(42)),
            @"@42"
        );

        // Universe: 𝒰@0
        assert_snapshot!(
            dump_to_str(&Syntax::universe(UniverseLevel::new(0))),
            @"𝒰0"
        );

        // Lambda: λ%0 → %0
        assert_snapshot!(
            dump_to_str(&Syntax::lambda(Syntax::variable_rc(Index(0)))),
            @"λ %0 → %0"
        );

        // Application: @42 @99
        assert_snapshot!(
            dump_to_str(&Syntax::application(
                Syntax::constant_rc(42),
                Syntax::constant_rc(99)
            )),
            @"@42 @99"
        );

        // Pi type: ∀(%0 : 𝒰0) → 𝒰1
        assert_snapshot!(
            dump_to_str(&Syntax::pi(
                Syntax::universe_rc(UniverseLevel::new(0)),
                Syntax::universe_rc(UniverseLevel::new(1))
            )),
            @"∀ (%0 : 𝒰0) → 𝒰1"
        );

        // Nested pi: ∀(%0 : 𝒰0) (%1 : %0) → %1
        assert_snapshot!(
            dump_to_str(&Syntax::pi(
                Syntax::universe_rc(UniverseLevel::new(0)),
                Syntax::pi_rc(
                    Syntax::variable_rc(Index(1)), // refers to outer pi binder
                    Syntax::variable_rc(Index(0))  // refers to inner pi binder
                )
            )),
            @"∀ (%0 : 𝒰0) (%1 : !0) → %1"
        );

        // Check: @42 : 𝒰0
        assert_snapshot!(
            dump_to_str(&Syntax::check(
                Syntax::universe_rc(UniverseLevel::new(0)),
                Syntax::constant_rc(42)
            )),
            @"@42 : 𝒰0"
        );

        // Lambda with application: λ%0 → @999 %0
        assert_snapshot!(
            dump_to_str(&Syntax::lambda(Syntax::application_rc(
                Syntax::constant_rc(999),
                Syntax::variable_rc(Index(0))
            ))),
            @"λ %0 → @999 %0"
        );

        // Nested lambda: λ%0 %1 → %1 %0
        assert_snapshot!(
            dump_to_str(&Syntax::lambda(Syntax::lambda_rc(
                Syntax::application_rc(
                    Syntax::variable_rc(Index(0)), // outer lambda param
                    Syntax::variable_rc(Index(1))  // inner lambda param
                )
            ))),
            @"λ %0 %1 → %1 %0"
        );

        // Lambda with checked nested lambda: λ%0 → (λ%1 → %1 %0 : 𝒰0)
        assert_snapshot!(
            dump_to_str(&Syntax::lambda_rc(Syntax::check_rc(
                Syntax::universe_rc(UniverseLevel::new(0)),
                Syntax::lambda_rc(Syntax::application_rc(
                    Syntax::variable_rc(Index(0)), // outer lambda param
                    Syntax::variable_rc(Index(1))  // inner lambda param
                ))
            ))),
            @"λ %0 → (λ %1 → %1 %0 : 𝒰0)"
        );

        // Simple metavariable: ?0
        assert_snapshot!(
            dump_to_str(&Syntax::metavariable(
                MetavariableId(0),
                Closure::new()
            )),
            @"?0"
        );

        // Application with two different metavariables: ?0 ?1
        // (both metavariables must be in the same expression to share GlobalState)
        assert_snapshot!(
            dump_to_str(&Syntax::application(
                Syntax::metavariable_rc(MetavariableId(0), Closure::new()),
                Syntax::metavariable_rc(MetavariableId(1), Closure::new())
            )),
            @"?0 ?1"
        );

        // Same metavariable used twice: ?0 ?0
        // (shows that the same metavariable ID gets the same name)
        assert_snapshot!(
            dump_to_str(&Syntax::application(
                Syntax::metavariable_rc(MetavariableId(0), Closure::new()),
                Syntax::metavariable_rc(MetavariableId(0), Closure::new())
            )),
            @"?0 ?0"
        );

        // Complex expression with three metavariables: (?0 ?1) ?2
        // (shows that distinct metavariables get distinct names)
        assert_snapshot!(
            dump_to_str(&Syntax::application(
                Syntax::application_rc(
                    Syntax::metavariable_rc(MetavariableId(0), Closure::new()),
                    Syntax::metavariable_rc(MetavariableId(1), Closure::new())
                ),
                Syntax::metavariable_rc(MetavariableId(2), Closure::new())
            )),
            @"?0 ?1 ?2"
        );

        // Unbound variable at depth 0: !0
        // (variable with index 0 when there are no binders)
        assert_snapshot!(
            dump_to_str(&Syntax::variable(Index(0))),
            @"!0"
        );

        // Unbound variable at depth 0: !1
        // (variable with index 1 when there are no binders)
        assert_snapshot!(
            dump_to_str(&Syntax::variable(Index(1))),
            @"!1"
        );

        // Unbound variable at depth 0: !5
        // (variable with index 5 when there are no binders)
        assert_snapshot!(
            dump_to_str(&Syntax::variable(Index(5))),
            @"!5"
        );

        // Lambda with unbound variable: λ%0 → !0
        // (the lambda binds one variable, but the body references index 1 which is unbound)
        assert_snapshot!(
            dump_to_str(&Syntax::lambda(Syntax::variable_rc(Index(1)))),
            @"λ %0 → !0"
        );

        // Lambda with unbound variable: λ%0 → !1
        // (the lambda binds one variable, but the body references index 2 which is unbound)
        assert_snapshot!(
            dump_to_str(&Syntax::lambda(Syntax::variable_rc(Index(2)))),
            @"λ %0 → !1"
        );

        // Nested lambda with mixed bound and unbound variables: λ%0 %1 → %1 !0
        // (two binders, so index 0 and 1 are bound, but index 2 is unbound)
        assert_snapshot!(
            dump_to_str(&Syntax::lambda(Syntax::lambda_rc(
                Syntax::application_rc(
                    Syntax::variable_rc(Index(0)), // bound to inner lambda
                    Syntax::variable_rc(Index(2))  // unbound (negative level 0)
                )
            ))),
            @"λ %0 %1 → %1 !0"
        );

        // Pi with unbound variable in target: ∀(%0 : 𝒰0) → !0
        // (the pi binds one variable, but the target references index 1 which is unbound)
        assert_snapshot!(
            dump_to_str(&Syntax::pi(
                Syntax::universe_rc(UniverseLevel::new(0)),
                Syntax::variable_rc(Index(1))
            )),
            @"∀ (%0 : 𝒰0) → !0"
        );
    }

    #[test]
    fn test_print_hardware_terms() {
        use crate::syn::{Constant, HApplication, HCheck, HLambda, HSyntax, Splice, Variable};
        use std::rc::Rc;

        // Simple HConstant: @42
        assert_snapshot!(
            dump_to_str(&HSyntax::HConstant(Constant::from(42))),
            @"@42"
        );

        // Simple HVariable bound: %0 (at depth 1)
        let hvar_bound = HSyntax::HVariable(Variable::new(Index(0)));
        let mut p = Printer::new(String::new(), 80);
        let st = State::new().inc_depth(); // depth 1, so index 0 is bound
        let _ = hvar_bound.print(st, &mut p);
        let result = p.finish().unwrap_or_default();
        assert_eq!(result, "%0");

        // Simple HVariable unbound: !0 (at depth 0)
        assert_snapshot!(
            dump_to_str(&HSyntax::HVariable(Variable::new(Index(0)))),
            @"!0"
        );

        // HCheck: @42 : @99
        let hcheck = HSyntax::HCheck(HCheck::new(
            Rc::new(HSyntax::HConstant(Constant::from(99))),
            Rc::new(HSyntax::HConstant(Constant::from(42))),
        ));
        assert_snapshot!(
            dump_to_str(&hcheck),
            @"@42 : @99"
        );

        // HLambda: λ%0 → %0
        let hlambda = HSyntax::HLambda(HLambda::new(Rc::new(HSyntax::HVariable(Variable::new(
            Index(0),
        )))));
        assert_snapshot!(
            dump_to_str(&hlambda),
            @"λ %0 → %0"
        );

        // HApplication: @42 @99
        let happ = HSyntax::HApplication(HApplication::new(
            Rc::new(HSyntax::HConstant(Constant::from(42))),
            Rc::new(HSyntax::HConstant(Constant::from(99))),
        ));
        assert_snapshot!(
            dump_to_str(&happ),
            @"@42 @99"
        );

        // Splice: ~@42
        let splice = HSyntax::Splice(Splice::new(Syntax::constant_rc(42)));
        assert_snapshot!(
            dump_to_str(&splice),
            @"~@42"
        );
    }

    #[test]
    fn test_print_complex_hardware_terms() {
        use crate::syn::{Constant, HApplication, HCheck, HLambda, HSyntax, Splice, Variable};
        use std::rc::Rc;

        // Nested HLambda: λ%0 %1 → %1 %0
        let nested_hlambda = HSyntax::HLambda(HLambda::new(Rc::new(HSyntax::HLambda(
            HLambda::new(Rc::new(HSyntax::HApplication(HApplication::new(
                Rc::new(HSyntax::HVariable(Variable::new(Index(0)))), // inner lambda param
                Rc::new(HSyntax::HVariable(Variable::new(Index(1)))), // outer lambda param
            )))),
        ))));
        assert_snapshot!(
            dump_to_str(&nested_hlambda),
            @"λ %0 %1 → %1 %0"
        );

        // HLambda with HCheck: λ%0 → (@42 : @99)
        let hlambda_with_check =
            HSyntax::HLambda(HLambda::new(Rc::new(HSyntax::HCheck(HCheck::new(
                Rc::new(HSyntax::HConstant(Constant::from(99))),
                Rc::new(HSyntax::HConstant(Constant::from(42))),
            )))));
        assert_snapshot!(
            dump_to_str(&hlambda_with_check),
            @"λ %0 → (@42 : @99)"
        );

        // HApplication with HLambda: (λ%0 → %0) @42
        let happ_with_lambda = HSyntax::HApplication(HApplication::new(
            Rc::new(HSyntax::HLambda(HLambda::new(Rc::new(HSyntax::HVariable(
                Variable::new(Index(0)),
            ))))),
            Rc::new(HSyntax::HConstant(Constant::from(42))),
        ));
        assert_snapshot!(
            dump_to_str(&happ_with_lambda),
            @"(λ %0 → %0) @42"
        );

        // Splice with complex term: ~λ %0 → @42 %0
        let splice_complex = HSyntax::Splice(Splice::new(Syntax::lambda_rc(
            Syntax::application_rc(Syntax::constant_rc(42), Syntax::variable_rc(Index(0))),
        )));
        assert_snapshot!(
            dump_to_str(&splice_complex),
            @"~λ %0 → @42 %0"
        );

        // HVariable unbound at different indices
        assert_snapshot!(
            dump_to_str(&HSyntax::HVariable(Variable::new(Index(5)))),
            @"!5"
        );

        // HCheck with HLambda: (λ%0 → %0) : (λ%1 → %1)
        let hcheck_lambdas = HSyntax::HCheck(HCheck::new(
            Rc::new(HSyntax::HLambda(HLambda::new(Rc::new(HSyntax::HVariable(
                Variable::new(Index(0)),
            ))))),
            Rc::new(HSyntax::HLambda(HLambda::new(Rc::new(HSyntax::HVariable(
                Variable::new(Index(0)),
            ))))),
        ));
        assert_snapshot!(
            dump_to_str(&hcheck_lambdas),
            @"λ %0 → %0 : λ %0 → %0"
        );
    }

    #[test]
    fn test_print_quote_with_hardware_terms() {
        use crate::syn::{Constant, HApplication, HLambda, HSyntax, Lift, Quote, Splice, Variable};
        use std::rc::Rc;

        // Quote with HConstant: '@42
        let quote_hconst =
            Syntax::Quote(Quote::new(Rc::new(HSyntax::HConstant(Constant::from(42)))));
        assert_snapshot!(
            dump_to_str(&quote_hconst),
            @"'@42"
        );

        // Quote with HLambda: '(λ%0 → %0)
        let quote_hlambda = Syntax::Quote(Quote::new(Rc::new(HSyntax::HLambda(HLambda::new(
            Rc::new(HSyntax::HVariable(Variable::new(Index(0)))),
        )))));
        assert_snapshot!(
            dump_to_str(&quote_hlambda),
            @"'λ %0 → %0"
        );

        // Quote with HApplication: '@42 @99
        let quote_happ = Syntax::Quote(Quote::new(Rc::new(HSyntax::HApplication(
            HApplication::new(
                Rc::new(HSyntax::HConstant(Constant::from(42))),
                Rc::new(HSyntax::HConstant(Constant::from(99))),
            ),
        ))));
        assert_snapshot!(
            dump_to_str(&quote_happ),
            @"'(@42 @99)"
        );

        // Quote with Splice: '~@42
        let quote_splice = Syntax::Quote(Quote::new(Rc::new(HSyntax::Splice(Splice::new(
            Syntax::constant_rc(42),
        )))));
        assert_snapshot!(
            dump_to_str(&quote_splice),
            @"'~@42"
        );

        // Lift with Quote: ^'@42
        let lift_quote = Syntax::Lift(Lift::new(Syntax::quote_rc(Rc::new(HSyntax::HConstant(
            Constant::from(42),
        )))));
        assert_snapshot!(
            dump_to_str(&lift_quote),
            @"^'@42"
        );
    }
}
