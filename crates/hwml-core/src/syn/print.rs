use crate::{
    declaration::{self, Declaration, Primitive},
    syn::*,
    ConstantId,
};
use elegance::{Io, Printer, Render};

const INDENT: isize = 2;
const COLUMNS: usize = 80;

type Precedence = (Option<usize>, Option<usize>);

struct Properties {
    precedence: Precedence,
}

impl Properties {
    const fn new(precedence: Precedence) -> Self {
        Properties { precedence }
    }

    fn lhs_prec(&self) -> Option<usize> {
        self.precedence.0
    }

    fn rhs_prec(&self) -> Option<usize> {
        self.precedence.1
    }
}

const UNIVERSE: Properties = Properties::new((None, None));
const LIFT: Properties = Properties::new((None, Some(5)));
const PI: Properties = Properties::new((None, Some(3)));
const LAMBDA: Properties = Properties::new((None, Some(3)));
const APP: Properties = Properties::new((Some(4), Some(5)));
const TCON_APP: Properties = APP;
const DCON_APP: Properties = APP;
const TCON: Properties = Properties::new((None, None));
const DCON: Properties = Properties::new((None, None));
const CASE: Properties = Properties::new((APP.precedence.0, None));
const HARDWARE_UNIVERSE: Properties = Properties::new((None, None));
const SLIFT: Properties = Properties::new((None, Some(5)));
const MLIFT: Properties = Properties::new((None, Some(5)));
const SIGNAL_UNIVERSE: Properties = Properties::new((None, None));
const BIT: Properties = Properties::new((None, None));
const ZERO: Properties = Properties::new((None, None));
const ONE: Properties = Properties::new((None, None));
const MODULE_UNIVERSE: Properties = Properties::new((None, None));
const HARROW: Properties = Properties::new((Some(4), Some(3)));
const MODULE: Properties = LAMBDA;
const HAPP: Properties = APP;
const CHECK: Properties = Properties::new((Some(2), Some(3)));

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

#[derive(Clone, Copy)]
struct State {
    /// Ambient binder depth.
    depth: usize,
    // The parent precedence.
    precedence: Precedence,
}

impl State {
    fn new() -> State {
        State {
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

fn ensure<F, R>(st: State, p: &mut Printer<R>, properties: Properties, f: F) -> Result<(), R::Error>
where
    F: FnOnce(State, &mut Printer<R>) -> Result<(), R::Error>,
    R: Render,
{
    ensure_precedence(st, p, properties.precedence, f)
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
            // Collect all nested applications into a flat list
            let mut args = vec![];
            let mut current = self;
            let function = loop {
                args.push(current.argument.clone());
                match &*current.function {
                    Syntax::Application(app) => current = app,
                    other => break other,
                }
            };
            args.reverse();

            // Print: function[arg1, arg2, arg3]
            p.cgroup(0, |p| {
                print_internal_subterm(db, st, p, function)?;
                p.text("[")?;
                if let Some((first, rest)) = args.split_first() {
                    print_internal_subterm(db, st, p, &**first)?;
                    for arg in rest {
                        p.text(",")?;
                        p.space()?;
                        print_internal_subterm(db, st, p, &**arg)?;
                    }
                }
                p.text("]")
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
        ensure(st, p, HARDWARE_UNIVERSE, |st, p| p.text("HardwareType"))
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
        ensure(st, p, BIT, |st, p| p.text("Bit"))
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
        p.text("ModuleType")
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
                    p.text("mod ")?;
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
            // Print: module<module_ty>(argument)
            p.cgroup(0, |p| {
                print_internal_subterm(db, st, p, &*self.module)?;
                p.text("<")?;
                print_internal_subterm(db, st, p, &*self.module_ty)?;
                p.text(">")?;
                p.text("(")?;
                print_internal_subterm(db, st, p, &*self.argument)?;
                p.text(")")
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
    use crate::Database;
    use hwml_support::IntoWithDb;
    use insta::assert_snapshot;

    /// Helper to print syntax and return string
    fn p(db: &Database, s: &Syntax) -> String {
        print_syntax_to_string(db, s)
    }

    // =========================================================================
    // Core Type Theory
    // =========================================================================

    #[test]
    fn print_universe() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::universe(UniverseLevel::new(0))), @"𝒰0");
        assert_snapshot!(p(&db, &Syntax::universe(UniverseLevel::new(1))), @"𝒰1");
    }

    #[test]
    fn print_lift() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::lift(Syntax::bit_rc())), @"^Bit");
    }

    #[test]
    fn print_pi() {
        let db = Database::new();
        let u0 = || Syntax::universe_rc(UniverseLevel::new(0));
        let u1 = || Syntax::universe_rc(UniverseLevel::new(1));
        let v = |i| Syntax::variable_rc(Index(i));
        assert_snapshot!(p(&db, &Syntax::pi(u0(), u1())), @"∀ (%0 : 𝒰0) → 𝒰1");
        assert_snapshot!(p(&db, &Syntax::pi(u0(), Syntax::pi_rc(v(0), v(0)))), @"∀ (%0 : 𝒰0) (%1 : %0) → %1");
    }

    #[test]
    fn print_lambda() {
        let db = Database::new();
        let v = |i| Syntax::variable_rc(Index(i));
        assert_snapshot!(p(&db, &Syntax::lambda(v(0))), @"λ %0 → %0");
        assert_snapshot!(p(&db, &Syntax::lambda(Syntax::lambda_rc(v(1)))), @"λ %0 %1 → %0");
    }

    #[test]
    fn print_application() {
        let db = Database::new();
        let f = Syntax::constant_rc("f".into_with_db(&db));
        let x = Syntax::constant_rc("x".into_with_db(&db));
        let y = Syntax::constant_rc("y".into_with_db(&db));
        assert_snapshot!(p(&db, &Syntax::application(f.clone(), x.clone())), @"@f[@x]");
        assert_snapshot!(p(&db, &Syntax::application(Syntax::application_rc(f, x), y)), @"@f[@x, @y]");
    }

    // =========================================================================
    // Inductive Types
    // =========================================================================

    #[test]
    fn print_type_constructor() {
        let db = Database::new();
        let c = |s: &str| Syntax::constant_rc(s.into_with_db(&db));
        assert_snapshot!(p(&db, &Syntax::type_constructor("Nat".into_with_db(&db), vec![])), @"#[@Nat]");
        assert_snapshot!(p(&db, &Syntax::type_constructor("Vec".into_with_db(&db), vec![c("A"), c("n")])), @"#[@Vec @A @n]");
    }

    #[test]
    fn print_data_constructor() {
        let db = Database::new();
        let c = |s: &str| Syntax::constant_rc(s.into_with_db(&db));
        assert_snapshot!(p(&db, &Syntax::data_constructor("Nil".into_with_db(&db), vec![])), @"[@Nil]");
        assert_snapshot!(p(&db, &Syntax::data_constructor("Cons".into_with_db(&db), vec![c("x"), c("xs")])), @"[@Cons @x @xs]");
    }

    #[test]
    fn print_case() {
        let db = Database::new();
        let c = |s: &str| Syntax::constant_rc(s.into_with_db(&db));
        let v = |i| Syntax::variable_rc(Index(i));
        let scrutinee = c("n");
        let motive = Syntax::universe_rc(UniverseLevel::new(0));
        let branches = vec![
            CaseBranch::new("Zero".into_with_db(&db), 0, c("a")),
            CaseBranch::new("Succ".into_with_db(&db), 1, v(0)),
        ];
        assert_snapshot!(p(&db, &Syntax::case(scrutinee, motive, branches)), @"@n case %0 → 𝒰0 { @Zero => @a | @Succ %0 => %0 }");
    }

    // =========================================================================
    // Hardware Universe
    // =========================================================================

    #[test]
    fn print_hardware_universe() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::hardware()), @"HardwareType");
    }

    #[test]
    fn print_slift() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::slift(Syntax::bit_rc())), @"^sBit");
    }

    #[test]
    fn print_mlift() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::mlift(Syntax::harrow_rc(Syntax::bit_rc(), Syntax::bit_rc()))), @"^m(Bit → Bit)");
    }

    // =========================================================================
    // Signal Universe
    // =========================================================================

    #[test]
    fn print_signal_universe() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::signal_universe()), @"SignalType");
    }

    #[test]
    fn print_bit() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::bit()), @"Bit");
    }

    #[test]
    fn print_zero() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::zero()), @"0");
    }

    #[test]
    fn print_one() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::one()), @"1");
    }

    // =========================================================================
    // Module Universe
    // =========================================================================

    #[test]
    fn print_module_universe() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::module_universe()), @"ModuleType");
    }

    #[test]
    fn print_harrow() {
        let db = Database::new();
        let bit = || Syntax::bit_rc();
        assert_snapshot!(p(&db, &Syntax::harrow(bit(), bit())), @"Bit → Bit");
        assert_snapshot!(p(&db, &Syntax::harrow(bit(), Syntax::harrow_rc(bit(), bit()))), @"Bit → Bit → Bit");
    }

    #[test]
    fn print_module() {
        let db = Database::new();
        let v = |i| Syntax::variable_rc(Index(i));
        assert_snapshot!(p(&db, &Syntax::module(v(0))), @"mod %0 → %0");
        assert_snapshot!(p(&db, &Syntax::module(Syntax::module_rc(v(1)))), @"mod %0 %1 → %0");
    }

    #[test]
    fn print_happlication() {
        let db = Database::new();
        let c = |s: &str| Syntax::constant_rc(s.into_with_db(&db));
        let bit = || Syntax::bit_rc();
        let ty = Syntax::harrow_rc(bit(), bit());
        assert_snapshot!(p(&db, &Syntax::happlication(c("m"), ty, c("x"))), @"@m<Bit → Bit>(@x)");
    }

    // =========================================================================
    // Variables and References
    // =========================================================================

    #[test]
    fn print_prim() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::prim_from(&db, "and")), @"$and");
    }

    #[test]
    fn print_constant() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::constant_from(&db, "myConst")), @"@myConst");
    }

    #[test]
    fn print_variable_bound() {
        let db = Database::new();
        let v = |i| Syntax::variable_rc(Index(i));
        assert_snapshot!(p(&db, &Syntax::lambda(v(0))), @"λ %0 → %0");
    }

    #[test]
    fn print_variable_unbound() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::variable(Index(0))), @"!0");
        assert_snapshot!(p(&db, &Syntax::variable(Index(1))), @"!1");
    }

    #[test]
    fn print_metavariable() {
        let db = Database::new();
        let v = |i| Syntax::variable_rc(Index(i));
        assert_snapshot!(p(&db, &Syntax::metavariable(MetaVariableId(0), vec![])), @"?[0]");
        assert_snapshot!(p(&db, &Syntax::metavariable(MetaVariableId(1), vec![v(0), v(1)])), @"?[1 !0 !1]");
    }

    // =========================================================================
    // Type Annotations
    // =========================================================================

    #[test]
    fn print_check() {
        let db = Database::new();
        let c = |s: &str| Syntax::constant_rc(s.into_with_db(&db));
        let u0 = Syntax::universe_rc(UniverseLevel::new(0));
        assert_snapshot!(p(&db, &Syntax::check(u0, c("x"))), @"@x : 𝒰0");
    }
}
