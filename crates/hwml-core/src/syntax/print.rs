use crate::syntax::{Application, Check, Lambda, Pi, RcSyntax, Syntax, Universe, Variable};
use elegance::{Io, Printer, Render};

const INDENT: isize = 2;
const COLUMNS: usize = 80;

pub fn dump_syntax(syntax: &Syntax) {
    let mut p = Printer::new(Io(std::io::stdout()), COLUMNS);
    let mut st = State::new();
    let _ = print(&mut st, &mut p, syntax);
    let _ = p.hard_break();
    let _ = p.finish();
}

struct State {
    /// Ambient binder depth.
    depth: usize,
    /// Ambient operator binding power.
    precedence: usize,
    /// True if this is the last subexpression in the tree.
    /// When a lambda is the tail expression, it can be printed without parens.
    last: bool,
}

impl State {
    fn new() -> State {
        State {
            depth: 0,
            precedence: 0,
            last: true,
        }
    }
}

trait Print {
    fn print<R>(&self, st: &mut State, p: &mut Printer<R>) -> Result<(), R::Error>
    where
        R: Render;
}

fn print<T, R>(st: &mut State, p: &mut Printer<R>, x: &T) -> Result<(), R::Error>
where
    T: Print,
    R: Render,
{
    x.print(st, p)
}

fn print_subterm<T, R>(st: &mut State, p: &mut Printer<R>, x: &T) -> Result<(), R::Error>
where
    T: Print,
    R: Render,
{
    let prev_value = st.last;
    st.last = false;
    let r = print(st, p, x);
    st.last = prev_value;
    r
}

fn print_last_subterm<T, R>(st: &mut State, p: &mut Printer<R>, x: &T) -> Result<(), R::Error>
where
    T: Print,
    R: Render,
{
    print(st, p, x)
}

fn print_binder<R>(st: &mut State, p: &mut Printer<R>) -> Result<(), R::Error>
where
    R: Render,
{
    p.text_owned(format!("%{}", st.depth))
}

fn under_binder<F, R>(st: &mut State, p: &mut Printer<R>, f: F) -> Result<(), R::Error>
where
    F: FnOnce(&mut State, &mut Printer<R>) -> Result<(), R::Error>,
    R: Render,
{
    st.depth += 1;
    let r = f(st, p);
    st.depth -= 1;
    r
}

fn print_subterm_under_binder<T, R>(
    st: &mut State,
    p: &mut Printer<R>,
    x: &T,
) -> Result<(), R::Error>
where
    T: Print,
    R: Render,
{
    under_binder(st, p, |st, p| print_subterm(st, p, x))
}

fn print_last_subterm_under_binder<T, R>(
    st: &mut State,
    p: &mut Printer<R>,
    x: &T,
) -> Result<(), R::Error>
where
    T: Print,
    R: Render,
{
    under_binder(st, p, |st, p| print_last_subterm(st, p, x))
}

/// Run the printing function f, outputing under a paren group.
fn under_group<F, R>(st: &mut State, p: &mut Printer<R>, f: F) -> Result<(), R::Error>
where
    F: FnOnce(&mut State, &mut Printer<R>) -> Result<(), R::Error>,
    R: Render,
{
    let prev_last = st.last;
    st.last = true;
    let result = p.cgroup(INDENT, |p| {
        p.text("(")?;
        f(st, p)?;
        p.text(")")
    });
    st.last = prev_last;
    result
}

fn print_under_group<T, R>(st: &mut State, p: &mut Printer<R>, x: &T) -> Result<(), R::Error>
where
    T: Print,
    R: Render,
{
    under_group(st, p, |st, p| print(st, p, x))
}

impl Print for Syntax {
    fn print<R: Render>(&self, st: &mut State, p: &mut Printer<R>) -> Result<(), R::Error> {
        match self {
            Syntax::Variable(var) => print(st, p, var),
            Syntax::Check(chk) => print(st, p, chk),
            Syntax::Pi(pi) => print(st, p, pi),
            Syntax::Lambda(lam) => print(st, p, lam),
            Syntax::Application(app) => print(st, p, app),
            Syntax::Universe(uni) => print(st, p, uni),
        }
    }
}

impl Print for Variable {
    fn print<R: Render>(&self, st: &mut State, p: &mut Printer<R>) -> Result<(), R::Error> {
        let lvl = self.index.to_level(st.depth).to_usize();
        p.text_owned(&format!("%{}", lvl))
    }
}

impl Print for Check {
    fn print<R: Render>(&self, st: &mut State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.cgroup(INDENT, |p| {
            print_subterm(st, p, &*self.term)?;
            p.space()?;
            p.text(":")?;
            p.space()?;
            print_last_subterm(st, p, &*self.ty)
        })
    }
}

impl Print for Pi {
    fn print<R: Render>(&self, st: &mut State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.cgroup(0, |p| {
            p.text("∀")?;
            print_binder(st, p)?;
            p.space()?;
            p.text(":")?;
            p.space()?;
            print_subterm(st, p, &*self.source)?;
            p.space()?;
            p.text("→")?;
            p.space()?;
            print_last_subterm_under_binder(st, p, &*self.target)
        })
    }
}

impl Lambda {
    fn print_base<R: Render>(&self, st: &mut State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.cgroup(2, |p| {
            p.cgroup(0, |p| {
                p.text("λ")?;
                print_binder(st, p)?;
                p.space()?;
                p.text("↦")
            })?;
            p.space()?;
            print_last_subterm_under_binder(st, p, &*self.body)
        })
    }
}

impl Print for Lambda {
    fn print<R: Render>(&self, st: &mut State, p: &mut Printer<R>) -> Result<(), R::Error> {
        // Lambdas continue to the end of the expression. If this lambda is the
        // final expression, it can be rendered without parens.
        if st.last {
            self.print_base(st, p)
        } else {
            p.cgroup(INDENT, |p| {
                p.text("(")?;
                self.print_base(st, p)?;
                p.text(")")
            })
        }
    }
}

impl Print for Application {
    fn print<R: Render>(&self, st: &mut State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.cgroup(0, |p| {
            print_subterm(st, p, &*self.function)?;
            p.space();
            print_last_subterm(st, p, &*self.argument)
        })
    }
}

impl Print for Universe {
    fn print<R: Render>(&self, _st: &mut State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.text_owned(&format!("𝒰@{}", self.level))
    }
}
