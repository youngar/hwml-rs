use crate::{
    declaration::{self, Declaration, Primitive},
    syn::*,
};
use elegance::{Io, Printer, Render};

const INDENT: isize = 2;
const COLUMNS: usize = 80;

type Precedence = (Option<usize>, Option<usize>);

struct Properties {
    mode: Option<Mode>,
    precedence: Precedence,
}

impl Properties {
    fn lhs_prec(&self) -> Option<usize> {
        self.precedence.0
    }

    fn rhs_prec(&self) -> Option<usize> {
        self.precedence.1
    }
}

const CHECK: Properties = Properties {
    mode: None,
    precedence: (Some(2), Some(3)),
};

const QUOTE: Properties = Properties {
    mode: None,
    precedence: (None, Some(5)),
};

const SPLICE: Properties = Properties {
    mode: None,
    precedence: (None, Some(5)),
};

const UNIVERSE: Properties = Properties {
    mode: Some(Mode::ML),
    precedence: (None, None),
};

const HARDWARE_UNIVERSE: Properties = Properties {
    mode: Some(Mode::ML),
    precedence: (None, None),
};

const LIFT: Properties = Properties {
    mode: Some(Mode::ML),
    precedence: (None, Some(5)),
};

const SLIFT: Properties = Properties {
    mode: Some(Mode::ML),
    precedence: (None, Some(5)),
};

const MLIFT: Properties = Properties {
    mode: Some(Mode::ML),
    precedence: (None, Some(5)),
};

const SIGNAL_UNIVERSE: Properties = Properties {
    mode: Some(Mode::ML),
    precedence: (None, None),
};

const MODULE_UNIVERSE: Properties = Properties {
    mode: Some(Mode::ML),
    precedence: (None, None),
};

const PI: Properties = Properties {
    mode: Some(Mode::ML),
    precedence: (None, Some(3)),
};

const LAMBDA: Properties = Properties {
    mode: Some(Mode::ML),
    precedence: (None, Some(3)),
};

const APP: Properties = Properties {
    mode: Some(Mode::ML),
    precedence: (Some(4), Some(5)),
};

const TCON_APP: Properties = Properties {
    mode: Some(Mode::ML),
    precedence: APP.precedence,
};

const DCON_APP: Properties = Properties {
    mode: Some(Mode::ML),
    precedence: APP.precedence,
};

const TCON: Properties = Properties {
    mode: Some(Mode::ML),
    precedence: (None, None),
};

const DCON: Properties = Properties {
    mode: Some(Mode::ML),
    precedence: (None, None),
};

const CASE: Properties = Properties {
    mode: Some(Mode::ML),
    precedence: (APP.precedence.0, None),
};

const HARROW: Properties = Properties {
    mode: Some(Mode::ML),
    precedence: (Some(4), Some(3)),
};

const MODULE: Properties = Properties {
    mode: Some(Mode::HW),
    precedence: LAMBDA.precedence,
};

const HAPP: Properties = Properties {
    mode: Some(Mode::HW),
    precedence: APP.precedence,
};

const BIT: Properties = Properties {
    mode: Some(Mode::ML),
    precedence: (None, None),
};

const ZERO: Properties = Properties {
    mode: Some(Mode::HW),
    precedence: (None, None),
};

const ONE: Properties = Properties {
    mode: Some(Mode::HW),
    precedence: (None, None),
};

pub fn dump_syntax<'db>(db: &'db dyn salsa::Database, syntax: &Syntax<'db>) {
    let mut p = Printer::new(Io(std::io::stdout()), COLUMNS);
    let st = State::new();
    let _ = syntax.print(db, st, &mut p);
    let _ = p.hard_break();
    let _ = p.finish();
}

pub fn print_syntax_to_string<'db>(db: &'db dyn salsa::Database, syntax: &Syntax<'db>) -> String {
    let mut p = Printer::new(String::new(), 80);
    let st = State::new();
    let _ = syntax.print(db, st, &mut p);
    p.finish().unwrap_or_default()
}

pub fn dump_module<'db>(db: &'db dyn salsa::Database, module: &crate::declaration::Module<'db>) {
    let mut p = Printer::new(Io(std::io::stdout()), COLUMNS);
    let _ = print_module(db, module, &mut p);
    let _ = p.hard_break();
    let _ = p.finish();
}

pub fn print_module_to_string<'db>(
    db: &'db dyn salsa::Database,
    module: &crate::declaration::Module<'db>,
) -> String {
    let mut p = Printer::new(String::new(), 80);
    let _ = print_module(db, module, &mut p);
    p.finish().unwrap_or_default()
}

fn print_module<'db, R: Render>(
    db: &'db dyn salsa::Database,
    module: &crate::declaration::Module<'db>,
    p: &mut Printer<R>,
) -> Result<(), R::Error> {
    let mut iter = module.declarations.iter();

    // Print the first element
    if let Some(first) = iter.next() {
        print_declaration(db, first, p)?;

        // Print remaining elements with hard break before each
        for decl in iter {
            p.hard_break()?;
            print_declaration(db, decl, p)?;
        }
    }

    Ok(())
}

fn print_declaration<'db, R: Render>(
    db: &'db dyn salsa::Database,
    decl: &crate::declaration::Declaration<'db>,
    p: &mut Printer<R>,
) -> Result<(), R::Error> {
    match decl {
        Declaration::Primitive(prim) => print_primitive(db, prim, p),
        Declaration::Constant(c) => print_constant(db, c, p),
        Declaration::TypeConstructor(tc) => print_type_constructor(db, tc, p),
    }
}

pub fn print_primitive<'db, R: Render>(
    db: &'db dyn salsa::Database,
    prim: &Primitive<'db>,
    p: &mut Printer<R>,
) -> Result<(), R::Error> {
    p.text("prim $")?;
    p.text_owned(prim.name.name(db))?;
    p.text(" : ")?;
    let st = State::new();
    prim.ty.print(db, st, p)?;
    p.text(";")?;
    Ok(())
}

pub fn print_constant<'db, R: Render>(
    db: &'db dyn salsa::Database,
    c: &declaration::Constant<'db>,
    p: &mut Printer<R>,
) -> Result<(), R::Error> {
    p.text("const @")?;
    p.text_owned(c.name.name(db))?;
    p.text(" : ")?;
    let st = State::new();
    c.ty.print(db, st, p)?;
    p.text(" = ")?;
    c.value.print(db, st, p)?;
    p.text(";")?;
    Ok(())
}

pub fn print_type_constructor<'db, R: Render>(
    db: &'db dyn salsa::Database,
    tc: &declaration::TypeConstructor<'db>,
    p: &mut Printer<R>,
) -> Result<(), R::Error> {
    p.text("tcon @")?;
    p.text_owned(tc.name.name(db))?;
    p.text(" : -> ")?;
    let st = State::new();
    tc.universe.print(db, st, p)?;
    if !tc.data_constructors.is_empty() {
        p.text(" where")?;
        p.hard_break()?;
        for dcon in &tc.data_constructors {
            p.text("    dcon @")?;
            p.text_owned(dcon.name.name(db))?;
            // Print parameters as telescope, then result type
            let mut dcon_st = st;
            for param_ty in dcon.parameters.iter() {
                p.text(" (")?;
                p.text("%")?;
                p.text_owned(format!("{}", dcon_st.depth))?;
                p.text(" : ")?;
                param_ty.print(db, dcon_st, p)?;
                p.text(")")?;
                dcon_st = dcon_st.inc_depth();
            }
            p.text(" : ")?;
            dcon.result_type.print(db, dcon_st, p)?;
            p.hard_break()?;
        }
    }
    p.text(";")?;
    Ok(())
}

pub fn print_hw_syntax_to_string<'db>(
    db: &'db dyn salsa::Database,
    syntax: &Syntax<'db>,
) -> String {
    let mut p = Printer::new(String::new(), 80);
    let st = State::with_mode(Mode::HW);
    let _ = syntax.print(db, st, &mut p);
    p.finish().unwrap_or_default()
}

#[derive(Clone, Copy)]
enum Mode {
    /// Hardware mode.
    HW,
    /// Meta-level mode.
    ML,
}

#[derive(Clone, Copy)]
struct State {
    /// The current mode (HW/ML) we are printing at.
    mode: Mode,
    /// Ambient binder depth.
    depth: usize,
    // The parent precedence.
    precedence: Precedence,
}

impl State {
    fn new() -> State {
        State {
            mode: Mode::ML,
            depth: 0,
            precedence: (None, None),
        }
    }

    fn with_mode(mode: Mode) -> State {
        State {
            mode,
            depth: 0,
            precedence: (None, None),
        }
    }

    fn set_prec(self, precedence: Precedence) -> State {
        State { precedence, ..self }
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

    fn set_mode(self, mode: Mode) -> State {
        State { mode, ..self }
    }
}

trait Print {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error>;
}

fn print_lhs_subterm<R, A>(
    db: &dyn salsa::Database,
    st: State,
    p: &mut Printer<R>,
    x: &A,
    lhs_prec: Option<usize>,
) -> Result<(), R::Error>
where
    R: Render,
    A: Print,
{
    x.print(db, st.set_rhs_prec(lhs_prec), p)
}

fn print_rhs_subterm<R, A>(
    db: &dyn salsa::Database,
    st: State,
    p: &mut Printer<R>,
    x: &A,
    rhs_prec: Option<usize>,
) -> Result<(), R::Error>
where
    R: Render,
    A: Print,
{
    x.print(db, st.set_lhs_prec(rhs_prec), p)
}

fn print_internal<F, R>(
    _db: &dyn salsa::Database,
    st: State,
    p: &mut Printer<R>,
    f: F,
) -> Result<(), R::Error>
where
    F: FnOnce(State, &mut Printer<R>) -> Result<(), R::Error>,
    R: Render,
{
    f(st.set_prec((None, None)), p)
}

fn print_internal_subterm<R, A>(
    db: &dyn salsa::Database,
    st: State,
    p: &mut Printer<R>,
    x: &A,
) -> Result<(), R::Error>
where
    R: Render,
    A: Print,
{
    x.print(db, st.set_prec((None, None)), p)
}

fn ensure_precedence<F, R>(
    st: State,
    p: &mut Printer<R>,
    (lhs_prec, rhs_prec): Precedence,
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
            f(st.set_prec((None, None)), p)?;
            p.text(")")
        })
    } else {
        f(st, p)
    }
}

pub fn quote<F, R>(st: State, p: &mut Printer<R>, f: F) -> Result<(), R::Error>
where
    F: FnOnce(State, &mut Printer<R>) -> Result<(), R::Error>,
    R: Render,
{
    ensure_precedence(st, p, QUOTE.precedence, |st, p| {
        p.text("'")?;
        let st = st.set_mode(Mode::HW);
        let st = st.set_lhs_prec(QUOTE.precedence.1);
        f(st, p)
    })
}

pub fn splice<F, R>(st: State, p: &mut Printer<R>, f: F) -> Result<(), R::Error>
where
    F: FnOnce(State, &mut Printer<R>) -> Result<(), R::Error>,
    R: Render,
{
    ensure_precedence(st, p, SPLICE.precedence, |st, p| {
        p.text("~")?;
        let st = st.set_mode(Mode::ML);
        let st = st.set_lhs_prec(SPLICE.precedence.1);
        f(st, p)
    })
}

fn ensure_mode<F, R>(
    st: State,
    p: &mut Printer<R>,
    mode: Option<Mode>,
    f: F,
) -> Result<(), R::Error>
where
    F: FnOnce(State, &mut Printer<R>) -> Result<(), R::Error>,
    R: Render,
{
    match (st.mode, mode) {
        (Mode::ML, Some(Mode::HW)) => quote(st, p, f),
        (Mode::HW, Some(Mode::ML)) => splice(st, p, f),
        _ => f(st, p),
    }
}

fn ensure<F, R>(st: State, p: &mut Printer<R>, properties: Properties, f: F) -> Result<(), R::Error>
where
    F: FnOnce(State, &mut Printer<R>) -> Result<(), R::Error>,
    R: Render,
{
    ensure_mode(st, p, properties.mode, |st, p| {
        ensure_precedence(st, p, properties.precedence, f)
    })
}

fn print_binder<R>(st: State, p: &mut Printer<R>) -> Result<(), R::Error>
where
    R: Render,
{
    p.text_owned(format!("%{}", st.depth))
}

fn print_binders<R>(st: State, p: &mut Printer<R>, n: usize) -> Result<(), R::Error>
where
    R: Render,
{
    if n == 0 {
        return Ok(());
    }
    print_binder(st, p)?;
    for _i in 0..n - 1 {
        p.space()?;
        print_binder(st, p)?;
    }
    Ok(())
}

impl<'db> Print for ConstantId<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        _st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        let name = self.name(db);
        p.text_owned(&format!("@{}", name))
    }
}

impl<'db> Print for Closure<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        p.text("[")?;
        p.cgroup(1, |p| {
            for (i, value) in self.values.iter().enumerate() {
                if i > 0 {
                    p.text(",")?;
                    p.space()?;
                }
                value.print(db, st, p)?;
            }
            Ok(())
        })?;
        p.text("]")?;
        Ok(())
    }
}

impl<'db> Print for Syntax<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        match self {
            Syntax::Universe(uni) => uni.print(db, st, p),
            Syntax::Lift(lift) => lift.print(db, st, p),

            Syntax::Pi(pi) => pi.print(db, st, p),
            Syntax::Lambda(lam) => lam.print(db, st, p),
            Syntax::Application(app) => app.print(db, st, p),

            Syntax::TypeConstructor(type_constructor) => type_constructor.print(db, st, p),
            Syntax::DataConstructor(data_constructor) => data_constructor.print(db, st, p),
            Syntax::Case(case) => case.print(db, st, p),

            Syntax::HardwareUniverse(hwu) => hwu.print(db, st, p),
            Syntax::SLift(slift) => slift.print(db, st, p),
            Syntax::MLift(mlift) => mlift.print(db, st, p),

            Syntax::SignalUniverse(sig) => sig.print(db, st, p),
            Syntax::Bit(bit) => bit.print(db, st, p),
            Syntax::Zero(zero) => zero.print(db, st, p),
            Syntax::One(one) => one.print(db, st, p),

            Syntax::ModuleUniverse(mty) => mty.print(db, st, p),
            Syntax::HArrow(harrow) => harrow.print(db, st, p),
            Syntax::Module(module) => module.print(db, st, p),
            Syntax::HApplication(app) => app.print(db, st, p),

            Syntax::Prim(prim) => prim.print(db, st, p),
            Syntax::Constant(constant) => constant.print(db, st, p),
            Syntax::Variable(var) => var.print(db, st, p),
            Syntax::Metavariable(meta) => meta.print(db, st, p),

            Syntax::Check(chk) => chk.print(db, st, p),
        }
    }
}

impl<'db> Print for Universe<'db> {
    fn print<R: Render>(
        &self,
        _db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, UNIVERSE, |_, p| {
            p.text_owned(&format!("𝒰{}", self.level))
        })
    }
}

impl<'db> Print for Lift<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, LIFT, |st, p| {
            p.text("^")?;
            print_rhs_subterm(db, st, p, &*self.ty, LIFT.rhs_prec())
        })
    }
}

impl<'db> Print for Pi<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, PI, |mut st, p| {
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
                            print_rhs_subterm(db, st, p, &*next.source, CHECK.rhs_prec())
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
                print_rhs_subterm(db, st, p, &*next.target, PI.rhs_prec())
            })
        })
    }
}

impl<'db> Print for Lambda<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, LAMBDA, |st, p| {
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
                print_rhs_subterm(db, st, p, &*next.body, LAMBDA.rhs_prec())
            })
        })
    }
}

impl<'db> Print for Application<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, APP, |st, p| {
            p.cgroup(0, |p| {
                print_lhs_subterm(db, st, p, &*self.function, APP.lhs_prec())?;
                p.space()?;
                print_rhs_subterm(db, st, p, &*self.argument, APP.rhs_prec())
            })
        })
    }
}

impl<'db> Print for TypeConstructor<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, TCON, |st, p| {
            print_constructor(db, st, p, "#", self.constructor, &self.arguments)
        })
    }
}

impl<'db> Print for DataConstructor<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, DCON_APP, |st, p| {
            print_constructor(db, st, p, "", self.constructor, &self.arguments)
        })
    }
}

fn print_constructor<'db, R: Render>(
    db: &dyn salsa::Database,
    st: State,
    p: &mut Printer<R>,
    sigil: &'static str,
    constructor: ConstantId<'db>,
    arguments: &[RcSyntax<'db>],
) -> Result<(), R::Error> {
    p.cgroup(0, |p| {
        p.text(sigil)?;
        p.text("[");
        constructor.print(db, st, p)?;
        if let Some((last, rest)) = arguments.split_last() {
            let st = st.set_lhs_prec(DCON_APP.rhs_prec());
            let ist = st.set_rhs_prec(DCON_APP.lhs_prec());
            for arg in rest {
                p.space()?;
                arg.print(db, ist, p)?;
            }
            p.space()?;
            last.print(db, st, p)?;
        }
        p.text("]");
        Ok(())
    })
}

fn print_case_branch<'db, R>(
    db: &dyn salsa::Database,
    st: State,
    p: &mut Printer<R>,
    branch: &CaseBranch<'db>,
) -> Result<(), R::Error>
where
    R: Render,
{
    branch.constructor.print(db, st, p)?;

    // Print the pattern variables and increment depth for each
    let mut st = st;
    for _i in 0..branch.arity {
        p.space()?;
        print_binder(st, p)?;
        st = st.inc_depth();
    }

    p.space()?;
    p.text("=>")?;
    p.space()?;
    print_internal_subterm(db, st, p, &*branch.body)
}

impl<'db> Print for Case<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, CASE, |st, p| {
            print_lhs_subterm(db, st, p, &*self.expr, CASE.lhs_prec())?;
            p.space()?;
            p.text("case")?;
            p.space()?;
            print_binder(st, p)?;
            p.space()?;
            p.text("→")?;
            p.space()?;
            print_internal_subterm(db, st.inc_depth(), p, &*self.motive)?;
            p.space()?;
            p.text("{")?;
            p.cgroup(0, |p| {
                p.space()?;
                if let Some((first, rest)) = self.branches.split_first() {
                    print_case_branch(db, st, p, first)?;
                    p.space()?;
                    for branch in rest {
                        p.text("|")?;
                        p.space()?;
                        print_case_branch(db, st, p, branch)?;
                        p.space()?;
                    }
                }
                Ok(())
            })?;
            p.text("}")
        })
    }
}

impl<'db> Print for CaseBranch<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        print_case_branch(db, st, p, self)
    }
}

impl<'db> Print for HardwareUniverse<'db> {
    fn print<R: Render>(
        &self,
        _db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, HARDWARE_UNIVERSE, |st, p| p.text("H"))
    }
}

impl<'db> Print for SLift<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, SLIFT, |st, p| {
            p.text("^s")?;
            print_rhs_subterm(db, st, p, &*self.ty, SLIFT.rhs_prec())
        })
    }
}

impl<'db> Print for MLift<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, MLIFT, |st, p| {
            p.text("^m")?;
            print_rhs_subterm(db, st, p, &*self.ty, MLIFT.rhs_prec())
        })
    }
}

impl<'db> Print for SignalUniverse<'db> {
    fn print<R: Render>(
        &self,
        _db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, SIGNAL_UNIVERSE, |st, p| p.text("SignalType"))
    }
}

impl<'db> Print for Bit<'db> {
    fn print<R: Render>(
        &self,
        _db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, BIT, |st, p| p.text("$Bit"))
    }
}

impl<'db> Print for Zero<'db> {
    fn print<R: Render>(
        &self,
        _db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, ZERO, |st, p| p.text("0"))
    }
}

impl<'db> Print for One<'db> {
    fn print<R: Render>(
        &self,
        _db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, ONE, |st, p| p.text("1"))
    }
}

impl<'db> Print for ModuleUniverse<'db> {
    fn print<R: Render>(
        &self,
        _db: &dyn salsa::Database,
        _st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        p.text("M")
    }
}

impl<'db> Print for HArrow<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, HARROW, |st, p| {
            p.cgroup(0, |p| {
                print_lhs_subterm(db, st, p, &*self.source, HARROW.lhs_prec())?;
                p.space()?;
                p.text("→")?;
                p.space()?;
                print_rhs_subterm(db, st, p, &*self.target, HARROW.rhs_prec())
            })
        })
    }
}

impl<'db> Print for Module<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, MODULE, |st, p| {
            p.cgroup(2, |p| {
                let mut next = self;
                let mut st = st;
                p.cgroup(0, |p| {
                    p.text("λ ")?;
                    loop {
                        print_binder(st, p)?;
                        st = st.inc_depth();
                        match &*next.body {
                            Syntax::Module(lam) => next = lam,
                            _ => break,
                        }
                        p.space()?;
                    }
                    p.space()?;
                    p.text("→")
                })?;
                p.space()?;
                print_rhs_subterm(db, st, p, &*next.body, MODULE.rhs_prec())
            })
        })
    }
}

impl<'db> Print for HApplication<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, HAPP, |st, p| {
            p.cgroup(0, |p| {
                print_lhs_subterm(db, st, p, &*self.function, HAPP.lhs_prec())?;
                p.space()?;
                print_rhs_subterm(db, st, p, &*self.argument, HAPP.rhs_prec())
            })
        })
    }
}

impl<'db> Print for Prim<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        _st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        let name = self.name.name(db);
        p.text_owned(&format!("${}", name))
    }
}

impl<'db> Print for Constant<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        self.name.print(db, st, p)
    }
}

impl<'db> Print for Variable<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        if self.index.is_bound(st.depth) {
            p.text_owned(&format!("{}", self.index.to_level(st.depth)))
        } else {
            p.text_owned(&format!("{}", self.index.to_negative_level(st.depth)))
        }
    }
}

impl<'db> Print for Metavariable<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        p.text("?[")?;
        p.text_owned(&format!("{}", self.id.0))?;
        for arg in &self.substitution {
            p.text(" ")?;
            arg.print(db, st, p)?;
        }
        p.text("]")?;
        Ok(())
    }
}

impl<'db> Print for Check<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, CHECK, |st, p| {
            p.igroup(0, |p| {
                print_lhs_subterm(db, st, p, &*self.term, CHECK.lhs_prec())?;
                p.text(" :")?;
                p.space()?;
                print_rhs_subterm(db, st, p, &*self.ty, CHECK.rhs_prec())
            })
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{Index, MetaVariableId, UniverseLevel};
    use crate::syn::{ConstantId, Syntax};
    use hwml_support::{FromWithDb, IntoWithDb};
    use insta::assert_snapshot;

    #[test]
    fn test_print_ast_to_stdout() {
        let db = crate::Database::new();

        // Simple constant: @42
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::constant_from(&db, "42")),
            @"@42"
        );

        // Universe: 𝒰@0
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::universe(UniverseLevel::new(0))),
            @"𝒰0"
        );

        // Lambda: λ%0 → %0
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::lambda(Syntax::variable_rc(Index(0)))),
            @"λ %0 → %0"
        );

        // Application: @42 @99
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::application(
                Syntax::constant_rc(ConstantId::from_with_db(&db, "42")),
                Syntax::constant_rc(ConstantId::from_with_db(&db, "99"))
            )),
            @"@42 @99"
        );

        // Pi type: ∀(%0 : 𝒰0) → 𝒰1
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::pi(
                Syntax::universe_rc(UniverseLevel::new(0)),
                Syntax::universe_rc(UniverseLevel::new(1))
            )),
            @"∀ (%0 : 𝒰0) → 𝒰1"
        );

        // Nested pi: ∀(%0 : 𝒰0) (%1 : %0) → %1
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::pi(
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
            print_syntax_to_string(&db, &Syntax::check(
                Syntax::universe_rc(UniverseLevel::new(0)),
                Syntax::constant_rc(ConstantId::from_with_db(&db, "42"))
            )),
            @"@42 : 𝒰0"
        );

        // Lambda with application: λ%0 → @999 %0
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::lambda(Syntax::application_rc(
                Syntax::constant_rc(ConstantId::from_with_db(&db, "999")),
                Syntax::variable_rc(Index(0))
            ))),
            @"λ %0 → @999 %0"
        );

        // Nested lambda: λ%0 %1 → %1 %0
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::lambda(Syntax::lambda_rc(
                Syntax::application_rc(
                    Syntax::variable_rc(Index(0)), // outer lambda param
                    Syntax::variable_rc(Index(1))  // inner lambda param
                )
            ))),
            @"λ %0 %1 → %1 %0"
        );

        // Lambda with checked nested lambda: λ%0 → (λ%1 → %1 %0 : 𝒰0)
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::lambda_rc(Syntax::check_rc(
                Syntax::universe_rc(UniverseLevel::new(0)),
                Syntax::lambda_rc(Syntax::application_rc(
                    Syntax::variable_rc(Index(0)), // outer lambda param
                    Syntax::variable_rc(Index(1))  // inner lambda param
                ))
            ))),
            @"λ %0 → (λ %1 → %1 %0 : 𝒰0)"
        );

        // Simple metavariable: ?[0]
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::metavariable(
                MetaVariableId(0),
                vec![]
            )),
            @"?[0]"
        );

        // Application with two different metavariables: ?[0] ?[1]
        // (both metavariables must be in the same expression to share GlobalState)
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::application(
                Syntax::metavariable_rc(MetaVariableId(0), vec![]),
                Syntax::metavariable_rc(MetaVariableId(1), vec![])
            )),
            @"?[0] ?[1]"
        );

        // Same metavariable used twice: ?[0] ?[0]
        // (shows that the same metavariable ID gets the same name)
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::application(
                Syntax::metavariable_rc(MetaVariableId(0), vec![]),
                Syntax::metavariable_rc(MetaVariableId(0), vec![])
            )),
            @"?[0] ?[0]"
        );

        // Data constructor with no arguments: @Nil
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::data_constructor(
                ConstantId::from_with_db(&db, "Nil"),
                vec![]
            )),
            @"[@Nil]"
        );

        // Data constructor with one lambda argument.
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::data_constructor(
                ConstantId::from_with_db(&db, "Nil"),
                vec![Syntax::lambda_rc(Syntax::variable_rc(Index(0)))]
            )),
            @"[@Nil λ %0 → %0]"
        );

        // Data constructor with multiple lambda arguments.
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::data_constructor(
                ConstantId::from_with_db(&db, "Cons"),
                vec![
                    Syntax::lambda_rc(Syntax::variable_rc(Index(0))),
                    Syntax::lambda_rc(Syntax::variable_rc(Index(0)))
                ]
            )),
            @"[@Cons (λ %0 → %0) λ %0 → %0]"
        );

        // Complex expression with three metavariables: (?[0] ?[1]) ?[2]
        // (shows that distinct metavariables get distinct names)
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::application(
                Syntax::application_rc(
                    Syntax::metavariable_rc(MetaVariableId(0), vec![]),
                    Syntax::metavariable_rc(MetaVariableId(1), vec![])
                ),
                Syntax::metavariable_rc(MetaVariableId(2), vec![])
            )),
            @"?[0] ?[1] ?[2]"
        );

        // Unbound variable at depth 0: !0
        // (variable with index 0 when there are no binders)
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::variable(Index(0))),
            @"!0"
        );

        // Unbound variable at depth 0: !1
        // (variable with index 1 when there are no binders)
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::variable(Index(1))),
            @"!1"
        );

        // Unbound variable at depth 0: !5
        // (variable with index 5 when there are no binders)
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::variable(Index(5))),
            @"!5"
        );

        // Lambda with unbound variable: λ%0 → !0
        // (the lambda binds one variable, but the body references index 1 which is unbound)
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::lambda(Syntax::variable_rc(Index(1)))),
            @"λ %0 → !0"
        );

        // Lambda with unbound variable: λ%0 → !1
        // (the lambda binds one variable, but the body references index 2 which is unbound)
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::lambda(Syntax::variable_rc(Index(2)))),
            @"λ %0 → !1"
        );

        // Nested lambda with mixed bound and unbound variables: λ%0 %1 → %1 !0
        // (two binders, so index 0 and 1 are bound, but index 2 is unbound)
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::lambda(Syntax::lambda_rc(
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
            print_syntax_to_string(&db, &Syntax::pi(
                Syntax::universe_rc(UniverseLevel::new(0)),
                Syntax::variable_rc(Index(1))
            )),
            @"∀ (%0 : 𝒰0) → !0"
        );
    }

    #[test]
    fn test_print_hardware_terms() {
        use crate::syn::{HApplication, Module, Variable};
        use crate::Database;
        use std::rc::Rc;
        let db = Database::default();

        // Simple Constant: @42
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::Constant(Constant::new(ConstantId::from_with_db(&db, "42")))),
            @"@42"
        );

        // Simple Variable bound: %0 (at depth 1)
        let hvar_bound = Syntax::Variable(Variable::new(Index(0)));
        let mut p = Printer::new(String::new(), 80);
        let st = State::new().inc_depth(); // depth 1, so index 0 is bound
        let _ = hvar_bound.print(&db, st, &mut p);
        let result = p.finish().unwrap_or_default();
        assert_eq!(result, "%0");

        // Simple Variable unbound: !0 (at depth 0)
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::Variable(Variable::new(Index(0)))),
            @"!0"
        );

        // Check: @42 : $Bit
        // Type annotation is now a meta-level Syntax (hardware type)
        let hcheck = Syntax::Check(Check::new(
            Rc::new(Syntax::Bit(Bit::new())),
            Rc::new(Syntax::Constant(Constant::new(ConstantId::from_with_db(
                &db, "42",
            )))),
        ));
        assert_snapshot!(
            print_syntax_to_string(&db, &hcheck),
            @"@42 : $Bit"
        );

        // Module: λ%0 → %0
        let Module = Syntax::Module(Module::new(Rc::new(Syntax::Variable(Variable::new(
            Index(0),
        )))));
        assert_snapshot!(
            print_syntax_to_string(&db, &Module),
            @"λ %0 → %0"
        );

        // HApplication: @42 @99
        let happ = Syntax::HApplication(HApplication::new(
            Rc::new(Syntax::Constant(Constant::new(ConstantId::from_with_db(
                &db, "42",
            )))),
            Rc::new(Syntax::Constant(Constant::new(ConstantId::from_with_db(
                &db, "99",
            )))),
        ));
        assert_snapshot!(
            print_syntax_to_string(&db, &happ),
            @"@42 @99"
        );
    }

    #[test]
    fn test_print_complex_hardware_terms() {
        use crate::syn::{HApplication, Module, Syntax, Variable};
        use crate::Database;
        use std::rc::Rc;
        let db = Database::default();

        // Nested Module: λ%0 %1 → %1 %0
        let nested_module = Syntax::Module(Module::new(Rc::new(Syntax::Module(Module::new(
            Rc::new(Syntax::HApplication(HApplication::new(
                Rc::new(Syntax::Variable(Variable::new(Index(0)))), // inner lambda param
                Rc::new(Syntax::Variable(Variable::new(Index(1)))), // outer lambda param
            ))),
        )))));
        assert_snapshot!(
            print_syntax_to_string(&db, &nested_module),
            @"λ %0 %1 → %1 %0"
        );

        // Module with Check: λ%0 → (@42 : $Bit)
        let module_with_check = Syntax::Module(Module::new(Rc::new(Syntax::Check(Check::new(
            Rc::new(Syntax::Bit(Bit::new())),
            Rc::new(Syntax::Constant(Constant::new(ConstantId::from_with_db(
                &db, "42",
            )))),
        )))));
        assert_snapshot!(
            print_syntax_to_string(&db, &module_with_check),
            @"λ %0 → (@42 : $Bit)"
        );

        // HApplication with Module: (λ%0 → %0) @42
        let happ_with_lambda = Syntax::HApplication(HApplication::new(
            Rc::new(Syntax::Module(Module::new(Rc::new(Syntax::Variable(
                Variable::new(Index(0)),
            ))))),
            Rc::new(Syntax::Constant(Constant::new(ConstantId::from_with_db(
                &db, "42",
            )))),
        ));
        assert_snapshot!(
            print_syntax_to_string(&db, &happ_with_lambda),
            @"(λ %0 → %0) @42"
        );

        // Variable unbound at different indices
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::Variable(Variable::new(Index(5)))),
            @"!5"
        );

        // Check with Module: (λ%0 → %0) : $Bit -> $Bit
        // The type annotation is a hardware type (meta-level Syntax)
        let harrow_type = Syntax::HArrow(HArrow::new(
            Rc::new(Syntax::Bit(Bit::new())),
            Rc::new(Syntax::Bit(Bit::new())),
        ));
        let hcheck_lambdas = Syntax::Check(Check::new(
            Rc::new(harrow_type),
            Rc::new(Syntax::Module(Module::new(Rc::new(Syntax::Variable(
                Variable::new(Index(0)),
            ))))),
        ));
        assert_snapshot!(
            print_syntax_to_string(&db, &hcheck_lambdas),
            @"λ %0 → %0 : $Bit → $Bit"
        );
    }

    // #[test]
    // fn test_print_quote_with_hardware_terms() {
    //     use crate::syn::{Constant, HApplication, Lift, Module, Syntax, Variable};
    //     use crate::Database;
    //     use std::rc::Rc;
    //     let db = Database::default();

    //     // Quote with Constant: '@42
    //     let quote_hconst = Syntax::Quote(Quote::new(Rc::new(Syntax::Constant(Constant::new(
    //         ConstantId::from_with_db(&db, "42"),
    //     )))));
    //     assert_snapshot!(
    //         print_syntax_to_string(&db, &quote_hconst),
    //         @"'@42"
    //     );

    //     // Quote with Module: '(λ%0 → %0)
    //     let quote_Module = Syntax::Quote(Quote::new(Rc::new(Syntax::Module(Module::new(
    //         Rc::new(Syntax::Variable(Variable::new(Index(0)))),
    //     )))));
    //     assert_snapshot!(
    //         print_syntax_to_string(&db, &quote_Module),
    //         @"'λ %0 → %0"
    //     );

    //     // Quote with HApplication: '@42 @99
    //     let quote_happ = Syntax::Quote(Quote::new(Rc::new(Syntax::HApplication(
    //         HApplication::new(
    //             Rc::new(Syntax::Constant(Constant::new(ConstantId::from_with_db(
    //                 &db, "42",
    //             )))),
    //             Rc::new(Syntax::Constant(Constant::new(ConstantId::from_with_db(
    //                 &db, "99",
    //             )))),
    //         ),
    //     ))));
    //     assert_snapshot!(
    //         print_syntax_to_string(&db, &quote_happ),
    //         @"'(@42 @99)"
    //     );

    //     // Quote with Splice: '~@42
    //     let quote_splice = Syntax::Quote(Quote::new(Rc::new(Syntax::Splice(Splice::new(
    //         Syntax::constant_rc(ConstantId::from_with_db(&db, "42")),
    //     )))));
    //     assert_snapshot!(
    //         print_syntax_to_string(&db, &quote_splice),
    //         @"'~@42"
    //     );

    //     // Lift with Quote: ^'@42
    //     let lift_quote = Syntax::Lift(Lift::new(Syntax::quote_rc(Rc::new(Syntax::Constant(
    //         Constant::new(ConstantId::from_with_db(&db, "42")),
    //     )))));
    //     assert_snapshot!(
    //         print_syntax_to_string(&db, &lift_quote),
    //         @"^'@42"
    //     );
    // }

    #[test]
    fn test_print_bit_zero_one() {
        use crate::syn::Syntax;
        use crate::Database;
        let db = Database::default();

        // Test Bit type: $Bit
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::bit()),
            @"$Bit"
        );

        // Test Zero constant: 0
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::zero()),
            @"0"
        );

        // Test One constant: 1
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::one()),
            @"1"
        );

        // Test Xor operation: $xor
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::prim("xor".into_with_db(&db))),
            @"$xor"
        );

        // Test Constant: @Add
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::constant("Add".into_with_db(&db))),
            @"@Add"
        );

        // Test Constant: @MyCircuit
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::constant("MyCircuit".into_with_db(&db))),
            @"@MyCircuit"
        );
    }

    #[test]
    fn test_print_data_constructors() {
        use crate::syn::{ConstantId, Syntax};
        use crate::Database;
        let db = Database::default();

        // Data constructor with no arguments: @Nil
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::data_constructor(
                ConstantId::from_with_db(&db, "Nil"),
                vec![]
            )),
            @"[@Nil]"
        );

        // Data constructor with one argument: [@Nil (λ %0 → λ %0 → %0]
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::data_constructor(
                ConstantId::from_with_db(&db, "Some"),
                vec![Syntax::lambda_rc(Syntax::lambda_rc(Syntax::variable_rc(Index(0))))]
            )),
            @"[@Some λ %0 %1 → %1]"
        );

        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::data_constructor(
                ConstantId::from_with_db(&db, "Pair"),
                vec![
                    Syntax::lambda_rc(Syntax::variable_rc(Index(0))),
                    Syntax::lambda_rc(Syntax::variable_rc(Index(0)))
                ]
            )),
            @"[@Pair (λ %0 → %0) λ %0 → %0]"
        );
    }

    #[test]
    fn test_print_case_expressions() {
        use crate::syn::{CaseBranch, ConstantId, Syntax};
        use crate::Database;
        let db = Database::default();

        // Simple case with zero-arity constructors: case @x { @true => @1; @false => @0 }
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::case(
                Syntax::constant_rc(ConstantId::from_with_db(&db, "x")),
            Syntax::constant_rc_from(&db, "Nat"),
                vec![
                    CaseBranch::new(
                        ConstantId::from_with_db(&db, "true"),
                        0,
                        Syntax::constant_rc(ConstantId::from_with_db(&db, "1")),
                    ),
                    CaseBranch::new(
                        ConstantId::from_with_db(&db, "false"),
                        0,
                        Syntax::constant_rc(ConstantId::from_with_db(&db, "0")),
                    ),
                ],
            )),
            @"@x case %0 → @Nat { @true => @1 | @false => @0 }"
        );

        // Single branch case: case @x { @unit => @42 }
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::case(
                Syntax::constant_rc(ConstantId::from_with_db(&db, "x")),
                Syntax::constant_rc_from(&db, "Nat"),
                vec![
                    CaseBranch::new(
                        ConstantId::from_with_db(&db, "unit"),
                        0,
                        Syntax::constant_rc(ConstantId::from_with_db(&db, "42")),
                    ),
                ],
            )),
            @"@x case %0 → @Nat { @unit => @42 }"
        );

        // Empty case (edge case): case @x { }
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::case(
                Syntax::constant_rc(ConstantId::from_with_db(&db, "x")),
                Syntax::constant_rc_from(&db, "False"),
                vec![],
            )),
            @"@x case %0 → @False { }"
        );
    }

    #[test]
    fn test_print_case_with_arity() {
        use crate::common::Index;
        use crate::syn::{CaseBranch, ConstantId, Syntax};
        use crate::Database;
        let db = Database::default();

        // Case with arity-1 constructor: case @x { @some %0 => %0; @none => @42 }
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::case(
                Syntax::constant_rc(ConstantId::from_with_db(&db, "x")),
                Syntax::constant_rc_from(&db, "Nat"),
                vec![
                    CaseBranch::new(
                        ConstantId::from_with_db(&db, "some"),
                        1,
                        Syntax::variable_rc(Index(0)), // bound by the pattern
                    ),
                    CaseBranch::new(
                        ConstantId::from_with_db(&db, "none"),
                        0,
                        Syntax::constant_rc(ConstantId::from_with_db(&db, "42")),
                    ),
                ],
            )),
            @"@x case %0 → @Nat { @some %0 => %0 | @none => @42 }"
        );

        // Case with arity-2 constructor: case @x { @pair %0 %1 => %1; @empty => @0 }
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::case(
                Syntax::constant_rc(ConstantId::from_with_db(&db, "x")),
                Syntax::constant_rc_from(&db, "Nat"),
                vec![
                    CaseBranch::new(
                        ConstantId::from_with_db(&db, "pair"),
                        2,
                        Syntax::variable_rc(Index(0)), // second element of pair (innermost binder)
                    ),
                    CaseBranch::new(
                        ConstantId::from_with_db(&db, "empty"),
                        0,
                        Syntax::constant_rc(ConstantId::from_with_db(&db, "0")),
                    ),
                ],
            )),
            @"@x case %0 → @Nat { @pair %0 %1 => %1 | @empty => @0 }"
        );

        // Case with arity-3 constructor: case @x { @triple %0 %1 %2 => %2 }
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::case(
                Syntax::constant_rc(ConstantId::from_with_db(&db, "x")),
                Syntax::constant_rc_from(&db, "Nat"),
                vec![
                    CaseBranch::new(
                        ConstantId::from_with_db(&db, "triple"),
                        3,
                        Syntax::variable_rc(Index(0)), // third element (innermost binder)
                    ),
                ],
            )),
            @"@x case %0 → @Nat { @triple %0 %1 %2 => %2 }"
        );
    }

    #[test]
    fn test_print_case_with_complex_bodies() {
        use crate::common::{Index, UniverseLevel};
        use crate::syn::{CaseBranch, ConstantId, Syntax};
        use crate::Database;
        let db = Database::default();

        // Case with lambda body: case @x { @f => λ%0 → %0 }
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::case(
                Syntax::constant_rc(ConstantId::from_with_db(&db, "x")),
                Syntax::constant_rc_from(&db, "Function"),
                vec![
                    CaseBranch::new(
                        ConstantId::from_with_db(&db, "f"),
                        0,
                        Syntax::lambda_rc(Syntax::variable_rc(Index(0))),
                    ),
                ],
            )),
            @"@x case %0 → @Function { @f => λ %0 → %0 }"
        );

        // Case with application body: case @x { @app => @f @x }
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::case(
                Syntax::constant_rc(ConstantId::from_with_db(&db, "x")),
                Syntax::constant_rc_from(&db, "Application"),
                vec![
                    CaseBranch::new(
                        ConstantId::from_with_db(&db, "app"),
                        0,
                        Syntax::application_rc(
                            Syntax::constant_rc(ConstantId::from_with_db(&db, "f")),
                            Syntax::constant_rc(ConstantId::from_with_db(&db, "x")),
                        ),
                    ),
                ],
            )),
            @"@x case %0 → @Application { @app => @f @x }"
        );

        // Case with check body: case @x { @check => @42 : 𝒰0 }
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::case(
                Syntax::constant_rc(ConstantId::from_with_db(&db, "x")),
                Syntax::constant_rc_from(&db, "Check"),
                vec![
                    CaseBranch::new(
                        ConstantId::from_with_db(&db, "check"),
                        0,
                        Syntax::check_rc(
                            Syntax::universe_rc(UniverseLevel::new(0)),
                            Syntax::constant_rc(ConstantId::from_with_db(&db, "42")),
                        ),
                    ),
                ],
            )),
            @"@x case %0 → @Check { @check => @42 : 𝒰0 }"
        );
    }

    #[test]
    fn test_print_case_in_context() {
        use crate::common::Index;
        use crate::syn::{CaseBranch, ConstantId, Syntax};
        use crate::Database;
        let db = Database::default();

        // Case with scrutinee: case @y { @true => @1; @false => @0 }
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::case(
                Syntax::constant_rc(ConstantId::from_with_db(&db, "y")),
                Syntax::constant_rc_from(&db, "Bool"),
                vec![
                    CaseBranch::new(
                        ConstantId::from_with_db(&db, "true"),
                        0,
                        Syntax::constant_rc(ConstantId::from_with_db(&db, "1")),
                    ),
                    CaseBranch::new(
                        ConstantId::from_with_db(&db, "false"),
                        0,
                        Syntax::constant_rc(ConstantId::from_with_db(&db, "0")),
                    ),
                ],
            )),
            @"@y case %0 → @Bool { @true => @1 | @false => @0 }"
        );

        // Nested case: case @x { @outer => case @y { @inner => @42 } }
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::case(
                Syntax::constant_rc(ConstantId::from_with_db(&db, "x")),
                Syntax::constant_rc_from(&db, "Nat"),
                vec![
                    CaseBranch::new(
                        ConstantId::from_with_db(&db, "outer"),
                        0,
                        Syntax::case_rc(
                            Syntax::constant_rc(ConstantId::from_with_db(&db, "y")),
                            Syntax::constant_rc_from(&db, "Nat"),
                            vec![
                                CaseBranch::new(
                                    ConstantId::from_with_db(&db, "inner"),
                                    0,
                                    Syntax::constant_rc(ConstantId::from_with_db(&db, "42")),
                                ),
                            ],
                        ),
                    ),
                ],
            )),
            @"@x case %0 → @Nat { @outer => @y case %0 → @Nat { @inner => @42 } }"
        );

        // Case in lambda: λ%0 → case @x { @some %1 => %1; @none => !1 }
        assert_snapshot!(
            print_syntax_to_string(&db, &Syntax::lambda(
                Syntax::case_rc(
                    Syntax::constant_rc(ConstantId::from_with_db(&db, "x")),
                    Syntax::constant_rc_from(&db, "Option"),
                    vec![
                        CaseBranch::new(
                            ConstantId::from_with_db(&db, "some"),
                            1,
                            Syntax::variable_rc(Index(0)), // bound by pattern (innermost)
                        ),
                        CaseBranch::new(
                            ConstantId::from_with_db(&db, "none"),
                            0,
                            Syntax::variable_rc(Index(1)), // bound by lambda (outer scope)
                        ),
                    ],
                ),
            )),
            @"λ %0 → @x case %1 → @Option { @some %1 => %1 | @none => !0 }"
        );
    }
}
