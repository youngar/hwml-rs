use std::collections::HashMap;

use crate::syn::{
    Application, Check, Constant, Lambda, Metavariable, MetavariableId, Pi, Syntax, Universe,
    Variable,
};
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

pub fn dump_syntax(syntax: &Syntax) {
    let mut p = Printer::new(Io(std::io::stdout()), COLUMNS);
    let st = State::new();
    let mut global = GlobalState::new();
    let _ = syntax.print(&mut global, st, &mut p);
    let _ = p.hard_break();
    let _ = p.finish();
}

pub fn print_syntax_to_string(syntax: &Syntax) -> String {
    let mut p = Printer::new(String::new(), 40);
    let st = State::new();
    let mut global = GlobalState::new();
    let _ = syntax.print(&mut global, st, &mut p);
    let _ = p.hard_break();
    p.finish().unwrap_or_default()
}

struct GlobalState {
    // Mapping from metavariable ids to names.
    metavar_names: HashMap<MetavariableId, usize>,
}

impl GlobalState {
    fn new() -> GlobalState {
        GlobalState {
            metavar_names: HashMap::new(),
        }
    }
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

fn print_left_subterm<R>(
    global: &mut GlobalState,
    st: State,
    p: &mut Printer<R>,
    x: &Syntax,
    lhs_prec: Option<usize>,
) -> Result<(), R::Error>
where
    R: Render,
{
    x.print(global, st.set_rhs_prec(lhs_prec), p)
}

fn print_right_subterm<R>(
    global: &mut GlobalState,
    st: State,
    p: &mut Printer<R>,
    x: &Syntax,
    rhs_prec: Option<usize>,
) -> Result<(), R::Error>
where
    R: Render,
{
    x.print(global, st.set_lhs_prec(rhs_prec), p)
}

fn print_internal_subterm<R>(
    global: &mut GlobalState,
    st: State,
    p: &mut Printer<R>,
    x: &Syntax,
) -> Result<(), R::Error>
where
    R: Render,
{
    x.print(global, st.set_lhs_prec(NO_PREC).set_rhs_prec(NO_PREC), p)
}

fn with_prec<F, R>(
    global: &mut GlobalState,
    st: State,
    p: &mut Printer<R>,
    lhs_prec: Option<usize>,
    rhs_prec: Option<usize>,
    f: F,
) -> Result<(), R::Error>
where
    F: FnOnce(&mut GlobalState, State, &mut Printer<R>) -> Result<(), R::Error>,
    R: Render,
{
    // If the parent precedence is greater than the child precedence, we need parens.
    let mut need_parens = false;
    if let Some(left_prec) = lhs_prec {
        if let Some(left_parent) = st.precedence.0 {
            need_parens |= left_parent > left_prec;
        }
    }
    if let Some(right_prec) = rhs_prec {
        if let Some(right_parent) = st.precedence.1 {
            need_parens |= right_parent > right_prec;
        }
    }
    if need_parens {
        p.igroup(INDENT, |p| {
            p.text("(")?;
            f(global, st.set_lhs_prec(NO_PREC).set_rhs_prec(NO_PREC), p)?;
            p.text(")")
        })
    } else {
        f(global, st, p)
    }
}

fn print_binder<R>(st: State, p: &mut Printer<R>) -> Result<(), R::Error>
where
    R: Render,
{
    p.text_owned(format!("%{}", st.depth))
}

impl Syntax {
    fn print<R: Render>(
        &self,
        global: &mut GlobalState,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        match self {
            Syntax::Constant(constant) => constant.print(global, st, p),
            Syntax::Variable(var) => var.print(global, st, p),
            Syntax::Check(chk) => chk.print(global, st, p),
            Syntax::Pi(pi) => pi.print(global, st, p),
            Syntax::Lambda(lam) => lam.print(global, st, p),
            Syntax::Application(app) => app.print(global, st, p),
            Syntax::Universe(uni) => uni.print(global, st, p),
            Syntax::Metavariable(meta) => meta.print(global, st, p),
        }
    }
}

impl Constant {
    fn print<R: Render>(
        &self,
        _global: &mut GlobalState,
        _st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        p.text_owned(&format!("@{}", self.name.0))
    }
}

impl Variable {
    fn print<R: Render>(
        &self,
        _global: &mut GlobalState,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        let lvl: usize = self.index.to_level(st.depth).to_usize();
        p.text_owned(&format!("%{}", lvl))
    }
}

impl Check {
    fn print<R: Render>(
        &self,
        global: &mut GlobalState,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        with_prec(global, st, p, CHECK_LHS, CHECK_RHS, |global, st, p| {
            p.igroup(0, |p| {
                print_left_subterm(global, st, p, &*self.term, CHECK_LHS)?;
                p.text(" :")?;
                p.space()?;
                print_right_subterm(global, st, p, &*self.ty, CHECK_RHS)
            })
        })
    }
}

impl Pi {
    fn print<R: Render>(
        &self,
        global: &mut GlobalState,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        with_prec(global, st, p, PI_LHS, PI_RHS, |global, st, p| {
            p.cgroup(0, |p| {
                let mut next = self;
                let mut st = st;
                p.text("∀")?;
                loop {
                    p.text("(")?;
                    p.cgroup(INDENT, |p| {
                        print_binder(st, p)?;
                        st = st.inc_depth();
                        p.text(" :")?;
                        p.space()?;
                        print_internal_subterm(global, st, p, &*next.source)
                    })?;
                    p.text(")")?;
                    match &*next.target {
                        Syntax::Pi(pi) => next = pi,
                        _ => break,
                    }
                    p.space()?;
                }
                p.space()?;
                p.text("→")?;
                p.space()?;
                print_right_subterm(global, st, p, &*next.target, PI_RHS)
            })
        })
    }
}

impl Lambda {
    fn print<R: Render>(
        &self,
        global: &mut GlobalState,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        with_prec(global, st, p, LAMBDA_LHS, LAMBDA_RHS, |global, st, p| {
            p.cgroup(2, |p| {
                let mut next = self;
                let mut st = st;
                p.cgroup(0, |p| {
                    p.text("λ")?;
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
                print_right_subterm(global, st, p, &*next.body, LAMBDA_RHS)
            })
        })
    }
}

impl Application {
    fn print<R: Render>(
        &self,
        global: &mut GlobalState,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        with_prec(global, st, p, APP_LHS, APP_RHS, |global, st, p| {
            p.cgroup(0, |p| {
                print_left_subterm(global, st, p, &*self.function, APP_LHS)?;
                p.space()?;
                print_right_subterm(global, st, p, &*self.argument, APP_RHS)
            })
        })
    }
}

impl Universe {
    fn print<R: Render>(
        &self,
        _global: &mut GlobalState,
        _st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        p.text_owned(&format!("𝒰{}", self.level))
    }
}

impl Metavariable {
    fn print<R: Render>(
        &self,
        global: &mut GlobalState,
        _st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        let len = global.metavar_names.len();
        let name = *global.metavar_names.entry(self.id).or_insert(len);
        p.text_owned(&format!("?{}", name))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{Index, UniverseLevel};
    use crate::syn::{ConstantId, Syntax};
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
            print_syntax_to_string(&Syntax::universe(UniverseLevel(0))),
            @"𝒰0"
        );

        // Lambda: λ%0 → %0
        assert_snapshot!(
            print_syntax_to_string(&Syntax::lambda(Syntax::variable_rc(Index(0)))),
            @"λ%0 → %0"
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
                Syntax::universe_rc(UniverseLevel(0)),
                Syntax::universe_rc(UniverseLevel(1))
            )),
            @"∀(%0 : 𝒰0) → 𝒰1"
        );

        // Nested pi: ∀(%0 : 𝒰0) (%1 : %0) → %1
        assert_snapshot!(
            print_syntax_to_string(&Syntax::pi(
                Syntax::universe_rc(UniverseLevel(0)),
                Syntax::pi_rc(
                    Syntax::variable_rc(Index(1)), // refers to outer pi binder
                    Syntax::variable_rc(Index(0))  // refers to inner pi binder
                )
            )),
            @"∀(%0 : 𝒰0) (%1 : %0) → %1"
        );

        // Check: @42 : 𝒰0
        assert_snapshot!(
            print_syntax_to_string(&Syntax::check(
                Syntax::universe_rc(UniverseLevel(0)),
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
            @"λ%0 → @999 %0"
        );

        // Nested lambda: λ%0 %1 → %1 %0
        assert_snapshot!(
            print_syntax_to_string(&Syntax::lambda(Syntax::lambda_rc(
                Syntax::application_rc(
                    Syntax::variable_rc(Index(0)), // outer lambda param
                    Syntax::variable_rc(Index(1))  // inner lambda param
                )
            ))),
            @"λ%0 %1 → %1 %0"
        );

        // Lambda with checked nested lambda: λ%0 → (λ%1 → %1 %0 : 𝒰0)
        assert_snapshot!(
            print_syntax_to_string(&Syntax::lambda_rc(Syntax::check_rc(
                Syntax::universe_rc(UniverseLevel(0)),
                Syntax::lambda_rc(Syntax::application_rc(
                    Syntax::variable_rc(Index(0)), // outer lambda param
                    Syntax::variable_rc(Index(1))  // inner lambda param
                ))
            ))),
            @"λ%0 → (λ%1 → %1 %0 : 𝒰0)"
        );

        // Test metavariables
        use crate::syn::Closure;

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
    }
}
