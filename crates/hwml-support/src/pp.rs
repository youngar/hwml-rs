use elegance::{Io, Printer, Render};

pub type Prec = Option<usize>;
pub type TermPrec = (Option<usize>, Option<usize>);

const COLUMNS: usize = 80;

pub fn lhs_prec((lhs, _): TermPrec) -> Prec {
    lhs
}

pub fn rhs_prec((_, rhs): TermPrec) -> Prec {
    rhs
}

#[derive(Clone, Copy)]
pub struct State {
    /// Ambient binder depth.
    depth: usize,
    /// The precedence of the term on the left-hand-side, if any.
    lhs_prec: Prec,
    /// The precedence of the term on the right-hand-side, if any.
    rhs_prec: Prec,
}

impl State {
    pub fn new() -> Self {
        Self {
            depth: 0,
            lhs_prec: None,
            rhs_prec: None,
        }
    }

    /// Clear the LHS and RHS precedence.
    pub fn reset_prec(&self) -> Self {
        Self {
            lhs_prec: None,
            rhs_prec: None,
            ..*self
        }
    }

    pub fn set_prec(&self, (lhs_prec, rhs_prec): TermPrec) -> Self {
        Self {
            lhs_prec,
            rhs_prec,
            ..*self
        }
    }

    pub fn set_lhs_prec(&self, lhs_prec: Prec) -> Self {
        Self { lhs_prec, ..*self }
    }

    pub fn set_rhs_prec(&self, rhs_prec: Option<usize>) -> Self {
        Self { rhs_prec, ..*self }
    }

    pub fn depth(&self) -> usize {
        self.depth
    }

    pub fn inc_depth(&self) -> Self {
        Self {
            depth: self.depth + 1,
            ..*self
        }
    }
}

pub trait PP {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error>;
}

impl<T: PP> PP for std::rc::Rc<T> {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        self.as_ref().print(st, p)
    }
}

pub trait PPTerm {
    const PREC: TermPrec;

    fn print_content<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error>;
}

impl<T: PPTerm> PP for T {
    fn print<R: Render>(&self, st: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        if parens_required(&st, T::PREC) {
            p.cgroup(1, |p| {
                p.text("(")?;
                self.print_content(st.reset_prec(), p)?;
                p.text(")")
            })
        } else {
            self.print_content(st, p)
        }
    }
}

fn check_prec(ambient: Prec, current: Prec) -> bool {
    match (ambient, current) {
        (Some(ambient), Some(current)) => ambient >= current,
        _ => false,
    }
}

fn parens_required(st: &State, (lhs_prec, rhs_prec): TermPrec) -> bool {
    check_prec(st.lhs_prec, lhs_prec) || check_prec(st.rhs_prec, rhs_prec)
}

pub fn print_lhs<R, T>(
    st: State,
    p: &mut Printer<R>,
    x: &T,
    ambient_rhs_prec: Prec,
) -> Result<(), R::Error>
where
    R: Render,
    T: PP,
{
    let st = st.set_rhs_prec(ambient_rhs_prec);
    x.print(st, p)
}

pub fn print_rhs<R, T>(
    st: State,
    p: &mut Printer<R>,
    x: &T,
    ambient_lhs_prec: Prec,
) -> Result<(), R::Error>
where
    R: Render,
    T: PP,
{
    let st = st.set_lhs_prec(ambient_lhs_prec);
    x.print(st, p)
}

pub fn print_internal<R, T>(st: State, p: &mut Printer<R>, x: &T) -> Result<(), R::Error>
where
    R: Render,
    T: PP,
{
    let st = st.reset_prec();
    x.print(st, p)
}

pub fn print_binder<R>(st: State, p: &mut Printer<R>) -> Result<(), R::Error>
where
    R: Render,
{
    p.text_owned(format!("%{}", st.depth))
}

pub fn dump<T: PP>(x: &T) {
    let mut p = Printer::new(Io(std::io::stdout()), COLUMNS);
    let st = State::new();
    let _ = x.print(st, &mut p);
    let _ = p.hard_break();
    let _ = p.finish();
}

pub fn dump_to_str<T: PP>(x: &T) -> String {
    let mut p = Printer::new(String::new(), 80);
    let st = State::new();
    let _ = x.print(st, &mut p);
    p.finish().unwrap_or_default()
}
