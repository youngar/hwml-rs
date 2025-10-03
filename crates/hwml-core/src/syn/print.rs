use crate::syn::*;
use elegance::{Io, Printer, Render};

const INDENT: isize = 2;
const COLUMNS: usize = 80;

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

pub fn dump_syntax(syntax: &Syntax) {
    let mut p = Printer::new(Io(std::io::stdout()), COLUMNS);
    let st = State::new();
    let _ = syntax.print(st, &mut p);
    let _ = p.hard_break();
    let _ = p.finish();
}

pub fn print_syntax_to_string(syntax: &Syntax) -> String {
    let mut p = Printer::new(String::new(), 80);
    let st = State::new();
    let _ = syntax.print(st, &mut p);
    p.finish().unwrap_or_default()
}

pub fn print_hsyntax_to_string(hsyntax: &HSyntax) -> String {
    let mut p = Printer::new(String::new(), 80);
    let st = State::new();
    let _ = hsyntax.print(st, &mut p);
    p.finish().unwrap_or_default()
}

#[derive(Clone, Copy)]
struct State {
    /// Ambient binder depth.
    depth: usize,
    // The parent precedence.
    precedence: (Option<usize>, Option<usize>),
}

impl State {
    fn new() -> State {
        State {
            depth: 0,
            precedence: (None, None),
        }
    }

    fn set_lhs_prec(self, prec: Option<usize>) -> State {
        State {
            precedence: (prec, self.precedence.1),
            ..self
        }
    }

    fn set_rhs_prec(self, prec: Option<usize>) -> State {
        State {
            precedence: (self.precedence.0, prec),
            ..self
        }
    }

    fn inc_depth(self) -> State {
        State {
            depth: self.depth + 1,
            ..self
        }
    }
}

trait Print {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error>;
}

fn print_left_subterm<R, A>(
    st: State,
    p: &mut Printer<R>,
    x: &A,
    lhs_prec: Option<usize>,
) -> Result<(), R::Error>
where
    R: Render,
    A: Print,
{
    x.print(st.set_rhs_prec(lhs_prec), p)
}

fn print_right_subterm<R, A>(
    st: State,
    p: &mut Printer<R>,
    x: &A,
    rhs_prec: Option<usize>,
) -> Result<(), R::Error>
where
    R: Render,
    A: Print,
{
    x.print(st.set_lhs_prec(rhs_prec), p)
}

fn print_internal_subterm<R, A>(st: State, p: &mut Printer<R>, x: &A) -> Result<(), R::Error>
where
    R: Render,
    A: Print,
{
    x.print(st.set_lhs_prec(NO_PREC).set_rhs_prec(NO_PREC), p)
}

fn with_prec<F, R>(
    st: State,
    p: &mut Printer<R>,
    lhs_prec: Option<usize>,
    rhs_prec: Option<usize>,
    f: F,
) -> Result<(), R::Error>
where
    F: FnOnce(State, &mut Printer<R>) -> Result<(), R::Error>,
    R: Render,
{
    // If the parent binds tighter, or if equal, then we need parens to ensure
    // that this subexpression would be parsed together as an atomic expression.
    let mut need_parens = false;
    if let Some(left_prec) = lhs_prec {
        if let Some(left_parent) = st.precedence.0 {
            need_parens |= left_parent >= left_prec;
        }
    }
    if let Some(right_prec) = rhs_prec {
        if let Some(right_parent) = st.precedence.1 {
            need_parens |= right_parent >= right_prec;
        }
    }
    if need_parens {
        p.igroup(INDENT, |p| {
            p.text("(")?;
            f(st.set_lhs_prec(NO_PREC).set_rhs_prec(NO_PREC), p)?;
            p.text(")")
        })
    } else {
        f(st, p)
    }
}

fn print_binder<R>(st: State, p: &mut Printer<R>) -> Result<(), R::Error>
where
    R: Render,
{
    p.text_owned(format!("%{}", st.depth))
}

impl Print for Closure {
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

impl Print for Syntax {
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

impl Print for Constant {
    fn print<R: Render>(&self, _st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.text_owned(&format!("@{}", self.name.0))
    }
}

impl Print for Variable {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        if self.index.is_bound(st.depth) {
            p.text_owned(&format!("{}", self.index.to_level(st.depth)))
        } else {
            p.text_owned(&format!("{}", self.index.to_negative_level(st.depth)))
        }
    }
}

impl Print for Check {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        with_prec(st, p, CHECK_LHS, CHECK_RHS, |st, p| {
            p.igroup(0, |p| {
                print_left_subterm(st, p, &*self.term, CHECK_LHS)?;
                p.text(" :")?;
                p.space()?;
                print_right_subterm(st, p, &*self.ty, CHECK_RHS)
            })
        })
    }
}

impl Print for Pi {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        with_prec(st, p, PI_LHS, PI_RHS, |mut st, p| {
            p.cgroup(0, |p| {
                let mut next = self;
                p.text("∀ ")?;
                p.cgroup(2, |p| {
                    loop {
                        p.text("(")?;
                        p.cgroup(INDENT, |p| {
                            print_binder(st, p)?;
                            p.text(" :")?;
                            p.space()?;
                            print_right_subterm(st, p, &*next.source, CHECK_RHS)
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
                print_right_subterm(st, p, &*next.target, PI_RHS)
            })
        })
    }
}

impl Print for Lambda {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        with_prec(st, p, LAMBDA_LHS, LAMBDA_RHS, |st, p| {
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
                print_right_subterm(st, p, &*next.body, LAMBDA_RHS)
            })
        })
    }
}

impl Print for Application {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        with_prec(st, p, APP_LHS, APP_RHS, |st, p| {
            p.cgroup(0, |p| {
                print_left_subterm(st, p, &*self.function, APP_LHS)?;
                p.space()?;
                print_right_subterm(st, p, &*self.argument, APP_RHS)
            })
        })
    }
}

impl Print for Universe {
    fn print<R: Render>(&self, _st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.text_owned(&format!("𝒰{}", self.level))
    }
}

impl Print for Metavariable {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.text_owned(&format!("{}", self.id))?;
        if !self.closure.is_empty() {
            self.closure.print(st, p)
        } else {
            Ok(())
        }
    }
}

impl Print for Lift {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        with_prec(st, p, LIFT_LHS, LIFT_RHS, |st, p| {
            p.text("^")?;
            print_right_subterm(st, p, &*self.tm, LIFT_RHS)
        })
    }
}

impl Print for Quote {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        with_prec(st, p, QUOTE_LHS, QUOTE_RHS, |st, p| {
            p.text("'")?;
            print_right_subterm(st, p, &*self.tm, QUOTE_RHS)
        })
    }
}

impl Print for HArrow {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        with_prec(st, p, HARROW_LHS, HARROW_RHS, |st, p| {
            p.cgroup(0, |p| {
                print_left_subterm(st, p, &*self.source, HARROW_LHS)?;
                p.space()?;
                p.text("→")?;
                p.space()?;
                print_right_subterm(st, p, &*self.target, HARROW_RHS)
            })
        })
    }
}

impl Print for HSyntax {
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

impl Print for HCheck {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        with_prec(st, p, CHECK_LHS, CHECK_RHS, |st, p| {
            p.igroup(0, |p| {
                print_left_subterm(st, p, &*self.term, CHECK_LHS)?;
                p.text(" :")?;
                p.space()?;
                print_right_subterm(st, p, &*self.ty, CHECK_RHS)
            })
        })
    }
}

impl Print for HLambda {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        with_prec(st, p, LAMBDA_LHS, LAMBDA_RHS, |st, p| {
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
                print_right_subterm(st, p, &*next.body, LAMBDA_RHS)
            })
        })
    }
}

impl Print for HApplication {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        with_prec(st, p, APP_LHS, APP_RHS, |st, p| {
            p.cgroup(0, |p| {
                print_left_subterm(st, p, &*self.function, APP_LHS)?;
                p.space()?;
                print_right_subterm(st, p, &*self.argument, APP_RHS)
            })
        })
    }
}

impl Print for Splice {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        with_prec(st, p, SPLICE_LHS, SPLICE_RHS, |st, p| {
            p.text("~")?;
            print_right_subterm(st, p, &*self.term, SPLICE_RHS)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{Index, UniverseLevel};
    use crate::syn::{ConstantId, MetavariableId, Syntax};
    use insta::assert_snapshot;

    #[test]
    fn test_print_ast_to_stdout() {
        // Simple constant: @42
        assert_snapshot!(
            print_syntax_to_string(&Syntax::constant(ConstantId(42))),
            @"@42"
        );

        // Universe: 𝒰@0
        assert_snapshot!(
            print_syntax_to_string(&Syntax::universe(UniverseLevel::new(0))),
            @"𝒰0"
        );

        // Lambda: λ%0 → %0
        assert_snapshot!(
            print_syntax_to_string(&Syntax::lambda(Syntax::variable_rc(Index(0)))),
            @"λ %0 → %0"
        );

        // Application: @42 @99
        assert_snapshot!(
            print_syntax_to_string(&Syntax::application(
                Syntax::constant_rc(ConstantId(42)),
                Syntax::constant_rc(ConstantId(99))
            )),
            @"@42 @99"
        );

        // Pi type: ∀(%0 : 𝒰0) → 𝒰1
        assert_snapshot!(
            print_syntax_to_string(&Syntax::pi(
                Syntax::universe_rc(UniverseLevel::new(0)),
                Syntax::universe_rc(UniverseLevel::new(1))
            )),
            @"∀ (%0 : 𝒰0) → 𝒰1"
        );

        // Nested pi: ∀(%0 : 𝒰0) (%1 : %0) → %1
        assert_snapshot!(
            print_syntax_to_string(&Syntax::pi(
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
            print_syntax_to_string(&Syntax::check(
                Syntax::universe_rc(UniverseLevel::new(0)),
                Syntax::constant_rc(ConstantId(42))
            )),
            @"@42 : 𝒰0"
        );

        // Lambda with application: λ%0 → @999 %0
        assert_snapshot!(
            print_syntax_to_string(&Syntax::lambda(Syntax::application_rc(
                Syntax::constant_rc(ConstantId(999)),
                Syntax::variable_rc(Index(0))
            ))),
            @"λ %0 → @999 %0"
        );

        // Nested lambda: λ%0 %1 → %1 %0
        assert_snapshot!(
            print_syntax_to_string(&Syntax::lambda(Syntax::lambda_rc(
                Syntax::application_rc(
                    Syntax::variable_rc(Index(0)), // outer lambda param
                    Syntax::variable_rc(Index(1))  // inner lambda param
                )
            ))),
            @"λ %0 %1 → %1 %0"
        );

        // Lambda with checked nested lambda: λ%0 → (λ%1 → %1 %0 : 𝒰0)
        assert_snapshot!(
            print_syntax_to_string(&Syntax::lambda_rc(Syntax::check_rc(
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
            print_syntax_to_string(&Syntax::metavariable(
                MetavariableId(0),
                Closure::new()
            )),
            @"?0"
        );

        // Application with two different metavariables: ?0 ?1
        // (both metavariables must be in the same expression to share GlobalState)
        assert_snapshot!(
            print_syntax_to_string(&Syntax::application(
                Syntax::metavariable_rc(MetavariableId(0), Closure::new()),
                Syntax::metavariable_rc(MetavariableId(1), Closure::new())
            )),
            @"?0 ?1"
        );

        // Same metavariable used twice: ?0 ?0
        // (shows that the same metavariable ID gets the same name)
        assert_snapshot!(
            print_syntax_to_string(&Syntax::application(
                Syntax::metavariable_rc(MetavariableId(0), Closure::new()),
                Syntax::metavariable_rc(MetavariableId(0), Closure::new())
            )),
            @"?0 ?0"
        );

        // Complex expression with three metavariables: (?0 ?1) ?2
        // (shows that distinct metavariables get distinct names)
        assert_snapshot!(
            print_syntax_to_string(&Syntax::application(
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
            print_syntax_to_string(&Syntax::variable(Index(0))),
            @"!0"
        );

        // Unbound variable at depth 0: !1
        // (variable with index 1 when there are no binders)
        assert_snapshot!(
            print_syntax_to_string(&Syntax::variable(Index(1))),
            @"!1"
        );

        // Unbound variable at depth 0: !5
        // (variable with index 5 when there are no binders)
        assert_snapshot!(
            print_syntax_to_string(&Syntax::variable(Index(5))),
            @"!5"
        );

        // Lambda with unbound variable: λ%0 → !0
        // (the lambda binds one variable, but the body references index 1 which is unbound)
        assert_snapshot!(
            print_syntax_to_string(&Syntax::lambda(Syntax::variable_rc(Index(1)))),
            @"λ %0 → !0"
        );

        // Lambda with unbound variable: λ%0 → !1
        // (the lambda binds one variable, but the body references index 2 which is unbound)
        assert_snapshot!(
            print_syntax_to_string(&Syntax::lambda(Syntax::variable_rc(Index(2)))),
            @"λ %0 → !1"
        );

        // Nested lambda with mixed bound and unbound variables: λ%0 %1 → %1 !0
        // (two binders, so index 0 and 1 are bound, but index 2 is unbound)
        assert_snapshot!(
            print_syntax_to_string(&Syntax::lambda(Syntax::lambda_rc(
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
            print_syntax_to_string(&Syntax::pi(
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
            print_hsyntax_to_string(&HSyntax::HConstant(Constant::new(ConstantId(42)))),
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
            print_hsyntax_to_string(&HSyntax::HVariable(Variable::new(Index(0)))),
            @"!0"
        );

        // HCheck: @42 : @99
        let hcheck = HSyntax::HCheck(HCheck::new(
            Rc::new(HSyntax::HConstant(Constant::new(ConstantId(99)))),
            Rc::new(HSyntax::HConstant(Constant::new(ConstantId(42)))),
        ));
        assert_snapshot!(
            print_hsyntax_to_string(&hcheck),
            @"@42 : @99"
        );

        // HLambda: λ%0 → %0
        let hlambda = HSyntax::HLambda(HLambda::new(Rc::new(HSyntax::HVariable(Variable::new(
            Index(0),
        )))));
        assert_snapshot!(
            print_hsyntax_to_string(&hlambda),
            @"λ %0 → %0"
        );

        // HApplication: @42 @99
        let happ = HSyntax::HApplication(HApplication::new(
            Rc::new(HSyntax::HConstant(Constant::new(ConstantId(42)))),
            Rc::new(HSyntax::HConstant(Constant::new(ConstantId(99)))),
        ));
        assert_snapshot!(
            print_hsyntax_to_string(&happ),
            @"@42 @99"
        );

        // Splice: ~@42
        let splice = HSyntax::Splice(Splice::new(Syntax::constant_rc(ConstantId(42))));
        assert_snapshot!(
            print_hsyntax_to_string(&splice),
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
            print_hsyntax_to_string(&nested_hlambda),
            @"λ %0 %1 → %1 %0"
        );

        // HLambda with HCheck: λ%0 → (@42 : @99)
        let hlambda_with_check =
            HSyntax::HLambda(HLambda::new(Rc::new(HSyntax::HCheck(HCheck::new(
                Rc::new(HSyntax::HConstant(Constant::new(ConstantId(99)))),
                Rc::new(HSyntax::HConstant(Constant::new(ConstantId(42)))),
            )))));
        assert_snapshot!(
            print_hsyntax_to_string(&hlambda_with_check),
            @"λ %0 → (@42 : @99)"
        );

        // HApplication with HLambda: (λ%0 → %0) @42
        let happ_with_lambda = HSyntax::HApplication(HApplication::new(
            Rc::new(HSyntax::HLambda(HLambda::new(Rc::new(HSyntax::HVariable(
                Variable::new(Index(0)),
            ))))),
            Rc::new(HSyntax::HConstant(Constant::new(ConstantId(42)))),
        ));
        assert_snapshot!(
            print_hsyntax_to_string(&happ_with_lambda),
            @"(λ %0 → %0) @42"
        );

        // Splice with complex term: ~λ %0 → @42 %0
        let splice_complex =
            HSyntax::Splice(Splice::new(Syntax::lambda_rc(Syntax::application_rc(
                Syntax::constant_rc(ConstantId(42)),
                Syntax::variable_rc(Index(0)),
            ))));
        assert_snapshot!(
            print_hsyntax_to_string(&splice_complex),
            @"~λ %0 → @42 %0"
        );

        // HVariable unbound at different indices
        assert_snapshot!(
            print_hsyntax_to_string(&HSyntax::HVariable(Variable::new(Index(5)))),
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
            print_hsyntax_to_string(&hcheck_lambdas),
            @"λ %0 → %0 : λ %0 → %0"
        );
    }

    #[test]
    fn test_print_quote_with_hardware_terms() {
        use crate::syn::{Constant, HApplication, HLambda, HSyntax, Lift, Quote, Splice, Variable};
        use std::rc::Rc;

        // Quote with HConstant: '@42
        let quote_hconst = Syntax::Quote(Quote::new(Rc::new(HSyntax::HConstant(Constant::new(
            ConstantId(42),
        )))));
        assert_snapshot!(
            print_syntax_to_string(&quote_hconst),
            @"'@42"
        );

        // Quote with HLambda: '(λ%0 → %0)
        let quote_hlambda = Syntax::Quote(Quote::new(Rc::new(HSyntax::HLambda(HLambda::new(
            Rc::new(HSyntax::HVariable(Variable::new(Index(0)))),
        )))));
        assert_snapshot!(
            print_syntax_to_string(&quote_hlambda),
            @"'λ %0 → %0"
        );

        // Quote with HApplication: '@42 @99
        let quote_happ = Syntax::Quote(Quote::new(Rc::new(HSyntax::HApplication(
            HApplication::new(
                Rc::new(HSyntax::HConstant(Constant::new(ConstantId(42)))),
                Rc::new(HSyntax::HConstant(Constant::new(ConstantId(99)))),
            ),
        ))));
        assert_snapshot!(
            print_syntax_to_string(&quote_happ),
            @"'(@42 @99)"
        );

        // Quote with Splice: '~@42
        let quote_splice = Syntax::Quote(Quote::new(Rc::new(HSyntax::Splice(Splice::new(
            Syntax::constant_rc(ConstantId(42)),
        )))));
        assert_snapshot!(
            print_syntax_to_string(&quote_splice),
            @"'~@42"
        );

        // Lift with Quote: ^'@42
        let lift_quote = Syntax::Lift(Lift::new(Syntax::quote_rc(Rc::new(HSyntax::HConstant(
            Constant::new(ConstantId(42)),
        )))));
        assert_snapshot!(
            print_syntax_to_string(&lift_quote),
            @"^'@42"
        );
    }
}
