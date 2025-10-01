use crate::syn::{
    self, Application, Check, Constant, Lambda, Metavariable, Pi, RcSyntax, Syntax, Universe,
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
    let _ = syntax.print(st, &mut p);
    let _ = p.hard_break();
    let _ = p.finish();
}

pub fn print_syntax_to_string(syntax: &Syntax) -> String {
    let mut p = Printer::new(String::new(), 40);
    let st = State::new();
    let _ = syntax.print(st, &mut p);
    let _ = p.hard_break();
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

fn print_left_subterm<R>(
    st: State,
    p: &mut Printer<R>,
    x: &Syntax,
    lhs_prec: Option<usize>,
) -> Result<(), R::Error>
where
    R: Render,
{
    x.print(st.set_rhs_prec(lhs_prec), p)
}

fn print_right_subterm<R>(
    st: State,
    p: &mut Printer<R>,
    x: &Syntax,
    rhs_prec: Option<usize>,
) -> Result<(), R::Error>
where
    R: Render,
{
    x.print(st.set_lhs_prec(rhs_prec), p)
}

fn print_internal_subterm<R>(st: State, p: &mut Printer<R>, x: &Syntax) -> Result<(), R::Error>
where
    R: Render,
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

impl Syntax {
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
        }
    }
}

impl Constant {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.text_owned(&format!("@{}", self.name.0))
    }
}

impl Variable {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        let lvl: usize = self.index.to_level(st.depth).to_usize();
        p.text_owned(&format!("%{}", lvl))
    }
}

impl Check {
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

impl Pi {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        with_prec(st, p, PI_LHS, PI_RHS, |st, p| {
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
                        print_internal_subterm(st, p, &*next.source)
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
                print_right_subterm(st, p, &*next.target, PI_RHS)
            })
        })
    }
}

impl Lambda {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        with_prec(st, p, LAMBDA_LHS, LAMBDA_RHS, |st, p| {
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
                    p.text("↦")
                })?;
                p.space()?;
                print_right_subterm(st, p, &*next.body, LAMBDA_RHS)
            })
        })
    }
}

impl Application {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        with_prec(st, p, APP_LHS, APP_RHS, |st, p| {
            p.cgroup(0, |p| {
                print_right_subterm(st, p, &*self.function, APP_RHS)?;
                p.space();
                print_left_subterm(st, p, &*self.argument, APP_LHS)
            })
        })
    }
}

impl Universe {
    fn print<R: Render>(&self, _st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.text_owned(&format!("𝒰{}", self.level))
    }
}

impl Metavariable {
    fn print<R: Render>(&self, _st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.text_owned(&format!("?helpme"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{Index, UniverseLevel};
    use crate::syn::{NameId, Syntax};
    use insta::assert_snapshot;

    #[test]
    fn test_print_ast_to_stdout() {
        // Create some example AST nodes

        // Simple constant: @42
        let constant = Syntax::constant(NameId(42));
        assert_snapshot!(print_syntax_to_string(&constant), @"@42");

        // Universe: 𝒰@0
        let universe = Syntax::universe(UniverseLevel(0));
        assert_snapshot!(print_syntax_to_string(&universe), @"𝒰0");

        let lambda_body = Syntax::variable_rc(Index(0));
        let lambda = Syntax::lambda(lambda_body);
        assert_snapshot!(print_syntax_to_string(&lambda), @"λ%0 ↦ %0");

        let app_fun = Syntax::constant_rc(NameId(42));
        let app_arg = Syntax::constant_rc(NameId(99));
        let application = Syntax::application(app_fun, app_arg);
        assert_snapshot!(print_syntax_to_string(&application), @"@42 @99");

        let pi_source = Syntax::universe_rc(UniverseLevel(0));
        let pi_target = Syntax::universe_rc(UniverseLevel(1));
        let pi = Syntax::pi(pi_source, pi_target);
        assert_snapshot!(print_syntax_to_string(&pi), @"∀(%0 : 𝒰0) → 𝒰1");

        let inner_pi_source = Syntax::variable_rc(Index(1)); // refers to outer pi binder
        let inner_pi_target = Syntax::variable_rc(Index(0)); // refers to inner pi binder
        let inner_pi = Syntax::pi_rc(inner_pi_source, inner_pi_target);
        let outer_pi_source = Syntax::universe_rc(UniverseLevel(0));
        let outer_pi = Syntax::pi(outer_pi_source, inner_pi);
        assert_snapshot!(print_syntax_to_string(&outer_pi), @"∀(%0 : 𝒰0) (%1 : %0) → %1");

        let check_term = Syntax::constant_rc(NameId(42));
        let check_type = Syntax::universe_rc(UniverseLevel(0));
        let check = Syntax::check(check_type, check_term);
        assert_snapshot!(print_syntax_to_string(&check), @"@42 : 𝒰0");

        let complex_fun = Syntax::constant_rc(NameId(999)); // @id
        let complex_arg = Syntax::variable_rc(Index(0)); // refers to lambda parameter
        let complex_app = Syntax::application_rc(complex_fun, complex_arg);
        let complex_lambda = Syntax::lambda(complex_app);
        assert_snapshot!(print_syntax_to_string(&complex_lambda), @"λ%0 ↦ @999 %0");

        let inner_fun = Syntax::variable_rc(Index(0)); // outer lambda param
        let inner_arg = Syntax::variable_rc(Index(1)); // inner lambda param
        let inner_app = Syntax::application_rc(inner_fun, inner_arg);
        let inner_lambda = Syntax::lambda_rc(inner_app);
        let outer_lambda = Syntax::lambda(inner_lambda);
        assert_snapshot!(print_syntax_to_string(&outer_lambda), @"λ%0 %1 ↦ %1 %0");

        let inner_fun = Syntax::variable_rc(Index(0)); // outer lambda param
        let inner_arg = Syntax::variable_rc(Index(1)); // inner lambda param
        let inner_app = Syntax::application_rc(inner_fun, inner_arg);
        let inner_lambda = Syntax::lambda_rc(inner_app);
        let outer_check = Syntax::check_rc(Syntax::universe_rc(UniverseLevel(0)), inner_lambda);
        let outer_lambda = Syntax::lambda_rc(outer_check);
        assert_snapshot!(print_syntax_to_string(&outer_lambda), @"λ%0 ↦ (λ%1 ↦ %1 %0 : 𝒰0)");
    }
}
