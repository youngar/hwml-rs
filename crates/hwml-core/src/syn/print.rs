use crate::syn::*;
use crate::*;
use elegance::{Io, Printer, Render};

const INDENT: isize = 2;
const COLUMNS: usize = 80;

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

pub fn dump_module<'db>(db: &'db dyn salsa::Database, module: &CompilationUnit<'db>) {
    let mut p = Printer::new(Io(std::io::stdout()), COLUMNS);
    let _ = print_module(db, module, &mut p);
    let _ = p.hard_break();
    let _ = p.finish();
}

pub fn print_module_to_string<'db>(
    db: &'db dyn salsa::Database,
    module: &CompilationUnit<'db>,
) -> String {
    let mut p = Printer::new(String::new(), 80);
    let _ = print_module(db, module, &mut p);
    p.finish().unwrap_or_default()
}

fn print_module<'db, R: Render>(
    db: &'db dyn salsa::Database,
    module: &CompilationUnit<'db>,
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
    decl: &Declaration<'db>,
    p: &mut Printer<R>,
) -> Result<(), R::Error> {
    match decl {
        Declaration::PrimitiveDecl(prim) => print_primitive_decl(db, prim, p),
        Declaration::ConstantDecl(c) => print_constant_decl(db, c, p),
        Declaration::TypeConstructorDecl(tc) => print_type_constructor_decl(db, tc, p),
        Declaration::MetavariableDecl(meta) => print_metavariable_decl(db, meta, p),
    }
}

pub fn print_primitive_decl<'db, R: Render>(
    db: &'db dyn salsa::Database,
    prim: &PrimitiveDecl<'db>,
    p: &mut Printer<R>,
) -> Result<(), R::Error> {
    p.text("prim $")?;
    p.text_owned(prim.name.to_string(db))?;
    p.text(" : ")?;
    let st = State::new();
    prim.ty.print(db, st, p)?;
    p.text(";")?;
    Ok(())
}

pub fn print_constant_decl<'db, R: Render>(
    db: &'db dyn salsa::Database,
    c: &ConstantDecl<'db>,
    p: &mut Printer<R>,
) -> Result<(), R::Error> {
    p.text("const @")?;
    p.text_owned(c.name.to_string(db))?;
    p.text(" : ")?;
    let st = State::new();
    c.ty.print(db, st, p)?;
    p.text(" = ")?;
    c.value.print(db, st, p)?;
    p.text(";")?;
    Ok(())
}

pub fn print_type_constructor_decl<'db, R: Render>(
    db: &'db dyn salsa::Database,
    tc: &TypeConstructorDecl<'db>,
    p: &mut Printer<R>,
) -> Result<(), R::Error> {
    p.text("tcon @")?;
    p.text_owned(tc.name.to_string(db))?;

    // Print parameters as telescope
    let mut st = State::new();
    for param_ty in tc.parameters.iter() {
        p.text(" (%")?;
        p.text_owned(format!("{}", st.depth))?;
        p.text(" : ")?;
        param_ty.print(db, st, p)?;
        p.text(")")?;
        st = st.inc_depth();
    }

    p.text(" : ")?;

    // Print indices as telescope
    for index_ty in tc.indices.iter() {
        p.text("(%")?;
        p.text_owned(format!("{}", st.depth))?;
        p.text(" : ")?;
        index_ty.print(db, st, p)?;
        p.text(") ")?;
        st = st.inc_depth();
    }

    p.text("-> ")?;
    tc.universe.print(db, st, p)?;

    let dcon_base_st = State::new().with_depth(tc.parameters.len());

    if !tc.data_constructors.is_empty() {
        p.text(" where")?;
        p.hard_break()?;
        for dcon in &tc.data_constructors {
            p.text("    dcon @")?;
            p.text_owned(dcon.name.to_string(db))?;
            // Print dcon parameters as telescope, then result type
            let mut dcon_st = dcon_base_st;
            for param_ty in dcon.parameters.iter() {
                p.text(" (%")?;
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

pub fn print_metavariable_decl<'db, R: Render>(
    db: &'db dyn salsa::Database,
    meta: &MetavariableDecl<'db>,
    p: &mut Printer<R>,
) -> Result<(), R::Error> {
    p.text("meta ?[")?;
    p.text_owned(format!("{}", meta.id))?;
    p.text("]")?;
    let mut st = State::new();
    // Print argument telescope
    for arg_ty in meta.arguments.iter() {
        p.text(" (")?;
        p.text("%")?;
        p.text_owned(format!("{}", st.depth))?;
        p.text(" : ")?;
        arg_ty.print(db, st, p)?;
        p.text(")")?;
        st = st.inc_depth();
    }
    p.text(" : ")?;
    meta.ty.print(db, st, p)?;
    p.text(";")?;
    Ok(())
}

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

const LAMBDA: Properties = Properties::new((None, Some(3)));
const APP: Properties = Properties::new((Some(4), Some(5)));
#[allow(dead_code)]
const TCON_APP: Properties = APP;
const DCON_APP: Properties = APP;
const TCON: Properties = Properties::new((None, None));
#[allow(dead_code)]
const DCON: Properties = Properties::new((None, None));
const CASE: Properties = Properties::new((APP.precedence.0, None));
const HARDWARE_UNIVERSE: Properties = Properties::new((None, None));
const SLIFT: Properties = Properties::new((None, Some(5)));
const MLIFT: Properties = Properties::new((None, Some(5)));
const SIGNAL_UNIVERSE: Properties = Properties::new((None, None));
const BIT: Properties = Properties::new((None, None));
const ZERO: Properties = Properties::new((None, None));
const ONE: Properties = Properties::new((None, None));
#[allow(dead_code)]
const MODULE_UNIVERSE: Properties = Properties::new((None, None));
const HARROW: Properties = Properties::new((Some(4), Some(3)));
const MODULE: Properties = LAMBDA;
const HAPP: Properties = APP;
const CHECK: Properties = Properties::new((Some(2), Some(3)));

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

    fn with_depth(self, depth: usize) -> State {
        State { depth, ..self }
    }

    fn under_binders(self, n: usize) -> State {
        State {
            depth: self.depth + n,
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

fn print_binder<'db, R>(
    st: State,
    p: &mut Printer<R>,
    _binding: &BindingSyntax<'db>,
) -> Result<(), R::Error>
where
    R: Render,
{
    p.text_owned(format!("%{}", st.depth))
}

#[allow(dead_code)]
fn print_binders<'db, R>(
    st: State,
    p: &mut Printer<R>,
    binding: &DynBindingSyntax<'db>,
) -> Result<(), R::Error>
where
    R: Render,
{
    if binding.arity == 0 {
        return Ok(());
    }
    let depth = st.depth;
    let _ = p.text_owned(format!("%{}", depth));
    for i in 1..binding.arity {
        p.space()?;
        let _ = p.text_owned(format!("%{}", depth + i));
    }
    Ok(())
}

impl<'db> Print for QualifiedName<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        _st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        p.text_owned(&format!("@{}", self.to_string(db)))
    }
}

impl<'db> Print for RcSyntax<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        self.as_ref().print(db, st, p)
    }
}

impl<'db, A> Print for Binding<A>
where
    A: Print,
{
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        let st = st.inc_depth();
        self.term().print(db, st, p)
    }
}

impl<'db> Print for DynBindingSyntax<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        let st = st.under_binders(st.depth + self.arity);
        self.body.print(db, st, p)
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
            // NEW: Type codes
            Syntax::UniverseCode(level) => p.text_owned(&format!("𝒰{}", level)),
            Syntax::LiftCode(shift, inner) => {
                p.text_owned(&format!("↑{} ", shift))?;
                inner.print(db, st, p)
            }
            Syntax::PiCode(source, target) => {
                p.text("∀")?;
                p.space()?;
                p.text("(")?;
                p.text_owned(&format!("%{}", st.depth))?;
                p.space()?;
                p.text(":")?;
                p.space()?;
                source.print(db, st, p)?;
                p.text(")")?;
                p.space()?;
                p.text("→")?;
                p.space()?;
                target.print(db, st, p)
            }
            Syntax::BitCode => p.text("$Bit"),

            // Terms
            Syntax::Lambda(lam) => lam.print(db, st, p),
            Syntax::Application(app) => app.print(db, st, p),
            Syntax::Let(let_expr) => let_expr.print(db, st, p),

            Syntax::TypeConstructor(type_constructor) => type_constructor.print(db, st, p),
            Syntax::DataConstructor(data_constructor) => data_constructor.print(db, st, p),
            Syntax::Case(case) => case.print(db, st, p),

            Syntax::Eq(eq) => eq.print(db, st, p),
            Syntax::Refl(refl) => refl.print(db, st, p),
            Syntax::Transport(transport) => transport.print(db, st, p),

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

impl<'db> Print for EqType<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, APP, |st, p| {
            p.text("Eq")?;
            p.space()?;
            print_rhs_subterm(db, st, p, &*self.ty, APP.rhs_prec())?;
            p.space()?;
            print_rhs_subterm(db, st, p, &*self.lhs, APP.rhs_prec())?;
            p.space()?;
            print_rhs_subterm(db, st, p, &*self.rhs, APP.rhs_prec())
        })
    }
}

impl<'db> Print for Refl<'db> {
    fn print<R: Render>(
        &self,
        _db: &dyn salsa::Database,
        _st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        p.text("refl")
    }
}

impl<'db> Print for Transport<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        // Print as: transport VALUE to MOTIVE by PROOF
        // Keywords provide clear boundaries, so we can use print_internal_subterm
        ensure(st, p, APP, |st, p| {
            p.text("transport")?;
            p.space()?;
            print_internal_subterm(db, st, p, &*self.value)?;
            p.space()?;
            p.text("to")?;
            p.space()?;
            print_internal_subterm(db, st, p, &*self.motive)?;
            p.space()?;
            p.text("by")?;
            p.space()?;
            print_internal_subterm(db, st, p, &*self.proof)
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
                        print_binder(st, p, &next.body)?;
                        st = st.inc_depth();
                        match next.body.term().as_ref() {
                            Syntax::Lambda(lam) => next = &lam,
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
                match current.function.as_ref() {
                    Syntax::Application(app) => current = &app,
                    _ => break &current.function,
                }
            };
            args.reverse();

            // Print: function[arg1, arg2, arg3]
            p.cgroup(0, |p| {
                print_internal_subterm(db, st, p, &**function)?;
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
    constructor: QualifiedName<'db>,
    arguments: &[RcSyntax<'db>],
) -> Result<(), R::Error> {
    p.cgroup(0, |p| {
        p.text(sigil)?;
        p.text("[")?;
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
        p.text("]")?;
        Ok(())
    })
}

impl<'db> Print for Case<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, CASE, |st, p| {
            // Print the scrutinee as a variable (de Bruijn index).
            // The scrutinee is always a variable, never an arbitrary expression.
            self.scrutinee.print(db, st, p)?;
            p.space()?;
            p.text("case")?;
            p.space()?;
            p.text("{")?;
            p.cgroup(0, |p| {
                p.space()?;
                if let Some((first, rest)) = self.branches.split_first() {
                    print_internal_subterm(db, st, p, first)?;
                    p.space()?;
                    for branch in rest {
                        p.text("|")?;
                        p.space()?;
                        print_internal_subterm(db, st, p, branch)?;
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
        self.constructor.print(db, st, p)?;
        if self.body.arity > 0 {
            p.space()?;
        }
        print_binders(st, p, &self.body)?;
        p.space()?;
        p.text("=>")?;
        p.space()?;
        // Print the body with the state incremented by the number of binders
        // We've already printed the binders manually, so print the body directly
        let body_st = st.under_binders(self.body.arity);
        print_internal_subterm(db, body_st, p, &*self.body.body)
    }
}

impl<'db> Print for HardwareUniverse<'db> {
    fn print<R: Render>(
        &self,
        _db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, HARDWARE_UNIVERSE, |_st, p| {
            p.text("HardwareUniverse")
        })
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
        ensure(st, p, SIGNAL_UNIVERSE, |_st, p| p.text("SignalUniverse"))
    }
}

impl<'db> Print for Bit<'db> {
    fn print<R: Render>(
        &self,
        _db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, BIT, |_st, p| p.text("Bit"))
    }
}

impl<'db> Print for Zero<'db> {
    fn print<R: Render>(
        &self,
        _db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, ZERO, |_st, p| p.text("0"))
    }
}

impl<'db> Print for One<'db> {
    fn print<R: Render>(
        &self,
        _db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, p, ONE, |_st, p| p.text("1"))
    }
}

impl<'db> Print for ModuleUniverse<'db> {
    fn print<R: Render>(
        &self,
        _db: &dyn salsa::Database,
        _st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        p.text("ModuleUniverse")
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
                        print_binder(st, p, &next.body)?;
                        st = st.inc_depth();
                        match next.body.term().as_ref() {
                            Syntax::Module(lam) => next = &lam,
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
        p.text_owned(&format!("${}", self.name.to_string(db)))
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
        _db: &dyn salsa::Database,
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
        p.text_owned(&format!("{}", self.id))?;
        for arg in &self.substitution {
            p.text(" ")?;
            arg.print(db, st, p)?;
        }
        p.text("]")?;
        Ok(())
    }
}

impl<'db> Print for Let<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        // Print: let %x : ty = value; body
        p.cgroup(2, |p| {
            p.text("let ")?;
            print_binder(st, p, &self.body)?;
            p.text(" : ")?;
            print_internal_subterm(db, st, p, &*self.ty)?;
            p.text(" = ")?;
            print_internal_subterm(db, st, p, &*self.value)?;
            p.text(";")?;
            p.space()?;
            print_internal_subterm(db, st, p, &self.body)
        })
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
    use crate::common::{Index, MetaVariableId};
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
    fn print_universe_code() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::UniverseCode(0)), @"𝒰0");
        assert_snapshot!(p(&db, &Syntax::UniverseCode(1)), @"𝒰1");
    }

    #[test]
    fn print_pi_code() {
        let db = Database::new();
        let pi1: RcSyntax = Syntax::PiCode(
            Syntax::UniverseCode(0).into(),
            Binding(Syntax::UniverseCode(1).into()),
        )
        .into();
        assert_snapshot!(p(&db, &pi1), @"∀ (%0 : 𝒰0) → 𝒰1");
        let inner: RcSyntax = Syntax::PiCode(
            Syntax::variable_rc(Index(0)),
            Binding(Syntax::variable_rc(Index(0))),
        )
        .into();
        let pi2: RcSyntax = Syntax::PiCode(Syntax::UniverseCode(0).into(), Binding(inner)).into();
        assert_snapshot!(p(&db, &pi2), @"∀ (%0 : 𝒰0) → ∀ (%1 : %0) → %1");
    }

    #[test]
    fn print_lambda() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::lambda(Binding(Syntax::variable_rc(Index(0))))), @"λ %0 → %0");
        assert_snapshot!(p(&db, &Syntax::lambda(Binding(Syntax::lambda_rc(Binding(Syntax::variable_rc(Index(1))))))), @"λ %0 %1 → %0");
    }

    #[test]
    fn print_application() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::application(Syntax::constant_rc("f".into_with_db(&db)), Syntax::constant_rc("x".into_with_db(&db)))), @"@f[@x]");
        assert_snapshot!(p(&db, &Syntax::application(Syntax::application_rc(Syntax::constant_rc("f".into_with_db(&db)), Syntax::constant_rc("x".into_with_db(&db))), Syntax::constant_rc("y".into_with_db(&db)))), @"@f[@x, @y]");
    }

    // =========================================================================
    // Inductive Types
    // =========================================================================

    #[test]
    fn print_type_constructor() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::type_constructor("Nat".into_with_db(&db), vec![])), @"#[@Nat]");
        assert_snapshot!(p(&db, &Syntax::type_constructor("Vec".into_with_db(&db), vec![Syntax::constant_rc("A".into_with_db(&db)), Syntax::constant_rc("n".into_with_db(&db))])), @"#[@Vec @A @n]");
    }

    #[test]
    fn print_data_constructor() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::data_constructor("Nil".into_with_db(&db), vec![])), @"[@Nil]");
        assert_snapshot!(p(&db, &Syntax::data_constructor("Cons".into_with_db(&db), vec![Syntax::constant_rc("x".into_with_db(&db)), Syntax::constant_rc("xs".into_with_db(&db))])), @"[@Cons @x @xs]");
    }

    #[test]
    fn print_case() {
        let db = Database::new();
        // Case with scrutinee at Index(0), which means the most recently bound variable
        // At depth 1 (under one binder), Index(0) prints as %0
        assert_snapshot!(p(&db, &Syntax::lambda_rc(Binding(Syntax::case_rc(
                        Index(0),
            vec![
                CaseBranch::new("Zero".into_with_db(&db), DynBinding::new(0, Syntax::constant_rc("a".into_with_db(&db)))),
                CaseBranch::new("Succ".into_with_db(&db), DynBinding::new(1, Syntax::variable_rc(Index(0)))),
            ]
        )))), @"λ %0 → %0 case { @Zero => @a | @Succ %1 => %1 }");
    }

    // =========================================================================
    // Hardware Universe
    // =========================================================================

    #[test]
    fn print_hardware_universe() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::hardware()), @"HardwareUniverse");
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
        assert_snapshot!(p(&db, &Syntax::signal_universe()), @"SignalUniverse");
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
    // Equality Types
    // =========================================================================

    #[test]
    fn print_eq_type() {
        let db = Database::new();
        let eq = Syntax::eq_rc(
            Syntax::UniverseCode(0).into(),
            Syntax::variable_rc(Index(0)),
            Syntax::variable_rc(Index(1)),
        );
        // Variables are unbound at depth 0, so they print as !0, !1
        assert_snapshot!(p(&db, &eq), @"Eq 𝒰0 !0 !1");
    }

    #[test]
    fn print_refl() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::refl()), @"refl");
    }

    #[test]
    fn print_transport() {
        let db = Database::new();
        // The motive is just a regular syntax term now, not a Closure
        let motive = Syntax::variable_rc(Index(0)); // !0 (unbound at depth 0)
        let transport =
            Syntax::transport_rc(motive, Syntax::refl_rc(), Syntax::variable_rc(Index(2)));
        // Prints as: transport VALUE to MOTIVE by PROOF
        assert_snapshot!(p(&db, &transport), @"transport !2 to !0 by refl");

        // Test with lambda motive - keywords eliminate need for parentheses
        let lambda_motive = Syntax::lambda_rc(Binding(Syntax::bit_rc()));
        let transport2 = Syntax::transport_rc(lambda_motive, Syntax::refl_rc(), Syntax::zero_rc());
        assert_snapshot!(p(&db, &transport2), @"transport 0 to λ %0 → Bit by refl");
    }

    // =========================================================================
    // Module Universe
    // =========================================================================

    #[test]
    fn print_module_universe() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::module_universe()), @"ModuleUniverse");
    }

    #[test]
    fn print_harrow() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::harrow(Syntax::bit_rc(), Syntax::bit_rc())), @"Bit → Bit");
        assert_snapshot!(p(&db, &Syntax::harrow(Syntax::bit_rc(), Syntax::harrow_rc(Syntax::bit_rc(), Syntax::bit_rc()))), @"Bit → Bit → Bit");
    }

    #[test]
    fn print_module() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::module(Binding(Syntax::variable_rc(Index(0))))), @"mod %0 → %0");
        assert_snapshot!(p(&db, &Syntax::module(Binding(Syntax::module_rc(Binding(Syntax::variable_rc(Index(1))))))), @"mod %0 %1 → %0");
    }

    #[test]
    fn print_happlication() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::happlication(
                        Syntax::constant_rc("m".into_with_db(&db)),
            Syntax::harrow_rc(Syntax::bit_rc(), Syntax::bit_rc()),
            Syntax::constant_rc("x".into_with_db(&db))
        )), @"@m<Bit → Bit>(@x)");
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
        assert_snapshot!(p(&db, &Syntax::lambda(Binding(Syntax::variable_rc(Index(0))))), @"λ %0 → %0");
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
        assert_snapshot!(p(&db, &Syntax::metavariable(MetaVariableId(0), vec![])), @"?[0]");
        assert_snapshot!(p(&db, &Syntax::metavariable(MetaVariableId(1), vec![Syntax::variable_rc(Index(0)), Syntax::variable_rc(Index(1))])), @"?[1 !0 !1]");
    }

    // =========================================================================
    // Type Annotations
    // =========================================================================

    #[test]
    fn print_check() {
        let db = Database::new();
        assert_snapshot!(p(&db, &Syntax::check(Syntax::UniverseCode(0).into(), Syntax::constant_rc("x".into_with_db(&db)))), @"@x : 𝒰0");
    }

    // =========================================================================
    // Hierarchical Qualified Names in Declarations
    // =========================================================================

    #[test]
    fn print_constant_hierarchical_two_components() {
        let db = Database::new();
        let foo: QualifiedName = hwml_support::FromWithDb::from_with_db(&db, "foo");
        let foo_bar = foo.qualify_name(&db, "bar");
        assert_snapshot!(p(&db, &Syntax::constant_rc(foo_bar)), @"@foo/bar");
    }

    #[test]
    fn print_constant_hierarchical_three_components() {
        let db = Database::new();
        let foo: QualifiedName = hwml_support::FromWithDb::from_with_db(&db, "foo");
        let foo_bar = foo.qualify_name(&db, "bar");
        let foo_bar_baz = foo_bar.qualify_name(&db, "baz");
        assert_snapshot!(p(&db, &Syntax::constant_rc(foo_bar_baz)), @"@foo/bar/baz");
    }

    #[test]
    fn print_primitive_hierarchical_two_components() {
        let db = Database::new();
        let path: QualifiedName = hwml_support::FromWithDb::from_with_db(&db, "path");
        let path_to = path.qualify_name(&db, "to");
        assert_snapshot!(p(&db, &Syntax::prim_rc(path_to)), @"$path/to");
    }

    #[test]
    fn print_primitive_hierarchical_three_components() {
        let db = Database::new();
        let path: QualifiedName = hwml_support::FromWithDb::from_with_db(&db, "path");
        let path_to = path.qualify_name(&db, "to");
        let path_to_prim = path_to.qualify_name(&db, "prim");
        assert_snapshot!(p(&db, &Syntax::prim_rc(path_to_prim)), @"$path/to/prim");
    }

    #[test]
    fn print_type_constructor_hierarchical() {
        let db = Database::new();
        let std: QualifiedName = hwml_support::FromWithDb::from_with_db(&db, "std");
        let std_vec = std.qualify_name(&db, "Vec");
        assert_snapshot!(
            p(&db, &Syntax::type_constructor(std_vec, vec![Syntax::constant_rc("A".into_with_db(&db))])),
            @"#[@std/Vec @A]"
        );
    }

    #[test]
    fn print_data_constructor_hierarchical() {
        let db = Database::new();
        let std: QualifiedName = hwml_support::FromWithDb::from_with_db(&db, "std");
        let std_some = std.qualify_name(&db, "Some");
        assert_snapshot!(
            p(&db, &Syntax::data_constructor(std_some, vec![Syntax::constant_rc("x".into_with_db(&db))])),
            @"[@std/Some @x]"
        );
    }
}
