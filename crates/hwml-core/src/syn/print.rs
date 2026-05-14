use crate::common::Icit;
use crate::syn::*;
use crate::*;
use elegance::{Io, Printer, Render};

const INDENT: isize = 2;
const COLUMNS: usize = 80;

/// Stack of binder names in binding order (innermost at the end).
type NameStack = Vec<String>;

trait NameStackExt {
    /// Push a name, freshening if it shadows an existing binding.
    /// Returns the freshened name. Anonymous binders ("_") are never freshened.
    fn push_fresh(&mut self, name: String) -> String;
}

impl NameStackExt for NameStack {
    fn push_fresh(&mut self, name: String) -> String {
        if name == "_" {
            self.push(name.clone());
            return name;
        }

        if !self.contains(&name) {
            self.push(name.clone());
            return name;
        }

        let mut suffix = 1;
        loop {
            let fresh_name = format!("{}_{}", name, suffix);
            if !self.contains(&fresh_name) {
                self.push(fresh_name.clone());
                return fresh_name;
            }
            suffix += 1;
        }
    }
}

pub fn dump_syntax<'db>(db: &'db dyn salsa::Database, syntax: &Syntax<'db>) {
    let mut p = Printer::new(Io(std::io::stdout()), COLUMNS);
    let st = State::new();
    let mut names = NameStack::new();
    let _ = syntax.print(db, st, &mut names, &mut p);
    let _ = p.hard_break();
    let _ = p.finish();
}

pub fn print_syntax_to_string<'db>(db: &'db dyn salsa::Database, syntax: &Syntax<'db>) -> String {
    let mut p = Printer::new(String::new(), 80);
    let st = State::new();
    let mut names = NameStack::new();
    let _ = syntax.print(db, st, &mut names, &mut p);
    p.finish().unwrap_or_default()
}

pub fn dump_module<'db>(db: &'db dyn salsa::Database, module: &CompilationUnit<'db>) {
    let mut p = Printer::new(Io(std::io::stdout()), COLUMNS);
    let mut names = NameStack::new();
    let _ = print_module(db, module, &mut names, &mut p);
    let _ = p.hard_break();
    let _ = p.finish();
}

pub fn print_module_to_string<'db>(
    db: &'db dyn salsa::Database,
    module: &CompilationUnit<'db>,
) -> String {
    let mut p = Printer::new(String::new(), 80);
    let mut names = NameStack::new();
    let _ = print_module(db, module, &mut names, &mut p);
    p.finish().unwrap_or_default()
}

pub fn print_constant_decl_to_string<'db>(
    db: &'db dyn salsa::Database,
    constant: &ConstantDecl<'db>,
) -> String {
    let mut p = Printer::new(String::new(), 80);
    let mut names = NameStack::new();
    let _ = print_constant_decl(db, constant, &mut names, &mut p);
    p.finish().unwrap_or_default()
}

fn print_module<'db, R: Render>(
    db: &'db dyn salsa::Database,
    module: &CompilationUnit<'db>,
    ns: &mut NameStack,
    p: &mut Printer<R>,
) -> Result<(), R::Error> {
    let mut iter = module.declarations.iter();

    // Print the first element
    if let Some(first) = iter.next() {
        print_declaration(db, first, ns, p)?;

        // Print remaining elements with hard break before each
        for decl in iter {
            p.hard_break()?;
            print_declaration(db, decl, ns, p)?;
        }
    }

    Ok(())
}

fn print_declaration<'db, R: Render>(
    db: &'db dyn salsa::Database,
    decl: &Declaration<'db>,
    ns: &mut NameStack,
    p: &mut Printer<R>,
) -> Result<(), R::Error> {
    match decl {
        Declaration::PrimitiveDecl(prim) => print_primitive_decl(db, prim, ns, p),
        Declaration::ConstantDecl(c) => print_constant_decl(db, c, ns, p),
        Declaration::TypeConstructorDecl(tc) => print_type_constructor_decl(db, tc, ns, p),
        Declaration::MetavariableDecl(meta) => print_metavariable_decl(db, meta, ns, p),
    }
}

pub fn print_primitive_decl<'db, R: Render>(
    db: &'db dyn salsa::Database,
    prim: &PrimitiveDecl<'db>,
    ns: &mut NameStack,
    p: &mut Printer<R>,
) -> Result<(), R::Error> {
    p.text("prim $")?;
    p.text_owned(prim.name.to_string(db))?;
    p.text(" : ")?;
    let st = State::new();
    prim.ty.print(db, st, ns, p)?;
    p.text(";")?;
    Ok(())
}

pub fn print_constant_decl<'db, R: Render>(
    db: &'db dyn salsa::Database,
    c: &ConstantDecl<'db>,
    ns: &mut NameStack,
    p: &mut Printer<R>,
) -> Result<(), R::Error> {
    p.text("const @")?;
    p.text_owned(c.name.to_string(db))?;
    p.text(" : ")?;
    let st = State::new();
    c.ty.print(db, st, ns, p)?;
    p.text(" = ")?;
    c.value.print(db, st, ns, p)?;
    p.text(";")?;
    Ok(())
}

pub fn print_type_constructor_decl<'db, R: Render>(
    db: &'db dyn salsa::Database,
    tc: &TypeConstructorDecl<'db>,
    ns: &mut NameStack,
    p: &mut Printer<R>,
) -> Result<(), R::Error> {
    p.text("tcon @")?;
    p.text_owned(tc.name.to_string(db))?;

    // Print parameters as telescope with names
    let mut st = State::new();
    for binder in tc.parameters.iter() {
        p.text(" (%")?;
        p.text_owned(binder.name.clone())?;
        p.text(" : ")?;
        binder.value.print(db, st, ns, p)?;
        p.text(")")?;
        // Push the name AFTER printing the type (with freshening to avoid shadowing ambiguity)
        ns.push_fresh(binder.name.clone());
        st = st.inc_depth();
    }

    p.text(" : ")?;

    // Print indices as telescope with names
    for binder in tc.indices.iter() {
        p.text("(%")?;
        p.text_owned(binder.name.clone())?;
        p.text(" : ")?;
        binder.value.print(db, st, ns, p)?;
        p.text(") ")?;
        // Push the name AFTER printing the type (with freshening to avoid shadowing ambiguity)
        ns.push_fresh(binder.name.clone());
        st = st.inc_depth();
    }

    p.text("-> ")?;
    tc.universe.print(db, st, ns, p)?;

    for _ in 0..tc.indices.len() {
        ns.pop();
    }

    let dcon_base_st = State::new().with_depth(tc.parameters.len());

    if !tc.data_constructors.is_empty() {
        p.text(" where")?;
        p.hard_break()?;
        for dcon in &tc.data_constructors {
            p.text("    dcon @")?;
            p.text_owned(dcon.name.to_string(db))?;
            let mut dcon_st = dcon_base_st;
            let dcon_param_count = dcon.parameters.len();
            for binder in dcon.parameters.iter() {
                p.text(" (%")?;
                p.text_owned(binder.name.clone())?;
                p.text(" : ")?;
                binder.value.print(db, dcon_st, ns, p)?;
                p.text(")")?;
                ns.push_fresh(binder.name.clone());
                dcon_st = dcon_st.inc_depth();
            }
            p.text(" : ")?;
            dcon.result_type.print(db, dcon_st, ns, p)?;
            p.hard_break()?;

            for _ in 0..dcon_param_count {
                ns.pop();
            }
        }
    }
    p.text(";")?;

    for _ in 0..tc.parameters.len() {
        ns.pop();
    }

    Ok(())
}

pub fn print_metavariable_decl<'db, R: Render>(
    db: &'db dyn salsa::Database,
    meta: &MetavariableDecl<'db>,
    ns: &mut NameStack,
    p: &mut Printer<R>,
) -> Result<(), R::Error> {
    p.text("meta ?[")?;
    p.text_owned(format!("{}", meta.id))?;
    p.text("]")?;
    let mut st = State::new();
    for arg_binder in meta.arguments.iter() {
        p.text(" (")?;
        p.text("%")?;
        p.text_owned(format!("{}", st.depth))?;
        p.text(" : ")?;
        arg_binder.value.print(db, st, ns, p)?;
        p.text(")")?;
        st = st.inc_depth();
    }
    p.text(" : ")?;
    meta.ty.print(db, st, ns, p)?;
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
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error>;
}

fn print_lhs_subterm<R, A>(
    db: &dyn salsa::Database,
    st: State,
    ns: &mut NameStack,
    p: &mut Printer<R>,
    x: &A,
    lhs_prec: Option<usize>,
) -> Result<(), R::Error>
where
    R: Render,
    A: Print,
{
    x.print(db, st.set_rhs_prec(lhs_prec), ns, p)
}

fn print_rhs_subterm<R, A>(
    db: &dyn salsa::Database,
    st: State,
    ns: &mut NameStack,
    p: &mut Printer<R>,
    x: &A,
    rhs_prec: Option<usize>,
) -> Result<(), R::Error>
where
    R: Render,
    A: Print,
{
    x.print(db, st.set_lhs_prec(rhs_prec), ns, p)
}

fn print_internal_subterm<R, A>(
    db: &dyn salsa::Database,
    st: State,
    ns: &mut NameStack,
    p: &mut Printer<R>,
    x: &A,
) -> Result<(), R::Error>
where
    R: Render,
    A: Print,
{
    x.print(db, st.set_prec((None, None)), ns, p)
}

fn ensure_precedence<F, R>(
    st: State,
    ns: &mut NameStack,
    p: &mut Printer<R>,
    (lhs_prec, rhs_prec): Precedence,
    f: F,
) -> Result<(), R::Error>
where
    F: FnOnce(State, &mut NameStack, &mut Printer<R>) -> Result<(), R::Error>,
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
            f(st.set_prec((None, None)), ns, p)?;
            p.text(")")
        })
    } else {
        f(st, ns, p)
    }
}

fn ensure<F, R>(st: State, ns: &mut NameStack, p: &mut Printer<R>, properties: Properties, f: F) -> Result<(), R::Error>
where
    F: FnOnce(State, &mut NameStack, &mut Printer<R>) -> Result<(), R::Error>,
    R: Render,
{
    ensure_precedence(st, ns, p, properties.precedence, f)
}

impl<'db> Print for QualifiedName<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        _st: State,
        _ns: &mut NameStack,
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
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        self.as_ref().print(db, st, ns, p)
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
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        // Push the binder name onto the stack (with freshening to avoid shadowing ambiguity)
        ns.push_fresh(self.name.clone());

        let st = st.inc_depth();
        let result = self.term().print(db, st, ns, p);

        // Pop the name after printing the body
        ns.pop();
        result
    }
}

impl<'db> Print for DynBindingSyntax<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        for name in self.names.iter() {
            ns.push_fresh(name.clone());
        }

        let st = st.under_binders(st.depth + self.arity);
        let result = self.body.print(db, st, ns, p);

        for _ in 0..self.arity {
            ns.pop();
        }
        result
    }
}

impl<'db> Print for Syntax<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        match self {
            // NEW: Type codes
            Syntax::UniverseCode(level) => p.text_owned(&format!("𝒰{}", level)),
            Syntax::LiftCode(shift, inner) => {
                p.text_owned(&format!("↑{} ", shift))?;
                inner.print(db, st, ns, p)
            }
            Syntax::PiCode(source, icit, target) => {
                use crate::common::Icit;
                p.text("∀")?;
                p.space()?;
                match icit {
                    Icit::Implicit => p.text("{")?,
                    Icit::Explicit => p.text("(")?,
                }
                p.text_owned(&format!("%{}", st.depth))?;
                p.space()?;
                p.text(":")?;
                p.space()?;
                source.print(db, st, ns, p)?;
                match icit {
                    Icit::Implicit => p.text("}")?,
                    Icit::Explicit => p.text(")")?,
                }
                p.space()?;
                p.text("→")?;
                p.space()?;
                target.print(db, st, ns, p)
            }
            Syntax::BitCode => p.text("$Bit"),

            // Terms
            Syntax::Lambda(lam) => lam.print(db, st, ns, p),
            Syntax::Application(app) => app.print(db, st, ns, p),
            Syntax::Let(let_expr) => let_expr.print(db, st, ns, p),

            Syntax::TypeConstructor(type_constructor) => type_constructor.print(db, st, ns, p),
            Syntax::DataConstructor(data_constructor) => data_constructor.print(db, st, ns, p),
            Syntax::Case(case) => case.print(db, st, ns, p),

            Syntax::Eq(eq) => eq.print(db, st, ns, p),
            Syntax::Refl(refl) => refl.print(db, st, ns, p),
            Syntax::Transport(transport) => transport.print(db, st, ns, p),

            Syntax::HardwareUniverse(hwu) => hwu.print(db, st, ns, p),
            Syntax::SLift(slift) => slift.print(db, st, ns, p),
            Syntax::MLift(mlift) => mlift.print(db, st, ns, p),

            Syntax::SignalUniverse(sig) => sig.print(db, st, ns, p),
            Syntax::Bit(bit) => bit.print(db, st, ns, p),
            Syntax::Zero(zero) => zero.print(db, st, ns, p),
            Syntax::One(one) => one.print(db, st, ns, p),

            Syntax::ModuleUniverse(mty) => mty.print(db, st, ns, p),
            Syntax::HArrow(harrow) => harrow.print(db, st, ns, p),
            Syntax::Module(module) => module.print(db, st, ns, p),
            Syntax::HApplication(app) => app.print(db, st, ns, p),

            Syntax::Prim(prim) => prim.print(db, st, ns, p),
            Syntax::Constant(constant) => constant.print(db, st, ns, p),
            Syntax::Variable(var) => var.print(db, st, ns, p),
            Syntax::Metavariable(meta) => meta.print(db, st, ns, p),

            Syntax::Check(chk) => chk.print(db, st, ns, p),
        }
    }
}

impl<'db> Print for EqType<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, ns, p, APP, |st, ns, p| {
            p.text("Eq")?;
            p.space()?;
            print_rhs_subterm(db, st, ns, p, &*self.ty, APP.rhs_prec())?;
            p.space()?;
            print_rhs_subterm(db, st, ns, p, &*self.lhs, APP.rhs_prec())?;
            p.space()?;
            print_rhs_subterm(db, st, ns, p, &*self.rhs, APP.rhs_prec())
        })
    }
}

impl<'db> Print for Refl<'db> {
    fn print<R: Render>(
        &self,
        _db: &dyn salsa::Database,
        _st: State,
        _ns: &mut NameStack,
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
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        // Print as: transport VALUE to MOTIVE by PROOF
        // Keywords provide clear boundaries, so we can use print_internal_subterm
        ensure(st, ns, p, APP, |st, ns, p| {
            p.text("transport")?;
            p.space()?;
            print_internal_subterm(db, st, ns, p, &*self.value)?;
            p.space()?;
            p.text("to")?;
            p.space()?;
            print_internal_subterm(db, st, ns, p, &*self.motive)?;
            p.space()?;
            p.text("by")?;
            p.space()?;
            print_internal_subterm(db, st, ns, p, &*self.proof)
        })
    }
}

impl<'db> Print for Lambda<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        use crate::common::Icit;
        ensure(st, ns, p, LAMBDA, |st, ns, p| {
            p.cgroup(2, |p| {
                let mut next = self;
                let mut st = st;
                let initial_stack_depth = ns.len();

                p.cgroup(0, |p| {
                    p.text("λ ")?;
                    loop {
                        // Push the binder name onto the stack (with freshening to avoid shadowing ambiguity)
                        let fresh_name = ns.push_fresh(next.body.name.clone());

                        // Show {binder} for implicit, binder for explicit
                        // Print the freshened name in the binder position
                        match next.icit {
                            Icit::Implicit => {
                                p.text("{")?;
                                p.text_owned(format!("%{}", fresh_name))?;
                                p.text("}")?;
                            }
                            Icit::Explicit => {
                                p.text_owned(format!("%{}", fresh_name))?;
                            }
                        }
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
                let body_result = print_rhs_subterm(db, st, ns, p, &*next.body, LAMBDA.rhs_prec());

                while ns.len() > initial_stack_depth {
                    ns.pop();
                }

                body_result
            })
        })
    }
}

impl<'db> Print for Application<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        use crate::common::Icit;
        ensure(st, ns, p, APP, |st, ns, p| {
            // Collect all nested applications into a flat list with their icits
            let mut args_with_icit = vec![];
            let mut current = self;
            let function = loop {
                args_with_icit.push((current.argument.clone(), current.icit));
                match current.function.as_ref() {
                    Syntax::Application(app) => current = &app,
                    _ => break &current.function,
                }
            };
            args_with_icit.reverse();

            // Print: function[arg1, {arg2}, arg3] (show implicit args with braces)
            p.cgroup(0, |p| {
                print_internal_subterm(db, st, ns, p, &**function)?;
                p.text("[")?;
                if let Some(((first_arg, first_icit), rest)) = args_with_icit.split_first() {
                    match first_icit {
                        Icit::Implicit => {
                            p.text("{")?;
                            print_internal_subterm(db, st, ns, p, &**first_arg)?;
                            p.text("}")?;
                        }
                        Icit::Explicit => {
                            print_internal_subterm(db, st, ns, p, &**first_arg)?;
                        }
                    }
                    for (arg, icit) in rest {
                        p.text(",")?;
                        p.space()?;
                        match icit {
                            Icit::Implicit => {
                                p.text("{")?;
                                print_internal_subterm(db, st, ns, p, &**arg)?;
                                p.text("}")?;
                            }
                            Icit::Explicit => {
                                print_internal_subterm(db, st, ns, p, &**arg)?;
                            }
                        }
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
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, ns, p, TCON, |st, ns, p| {
            print_constructor(db, st, ns, p, "#", self.constructor, &self.arguments)
        })
    }
}

impl<'db> Print for DataConstructor<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, ns, p, DCON_APP, |st, ns, p| {
            print_constructor(db, st, ns, p, "", self.constructor, &self.arguments)
        })
    }
}

fn print_constructor<'db, R: Render>(
    db: &dyn salsa::Database,
    st: State,
    ns: &mut NameStack,
    p: &mut Printer<R>,
    sigil: &'static str,
    constructor: QualifiedName<'db>,
    arguments: &[RcSyntax<'db>],
) -> Result<(), R::Error> {
    p.cgroup(0, |p| {
        p.text(sigil)?;
        p.text("[")?;
        constructor.print(db, st, ns, p)?;
        if let Some((last, rest)) = arguments.split_last() {
            let st = st.set_lhs_prec(DCON_APP.rhs_prec());
            let ist = st.set_rhs_prec(DCON_APP.lhs_prec());
            for arg in rest {
                p.space()?;
                arg.print(db, ist, ns, p)?;
            }
            p.space()?;
            last.print(db, st, ns, p)?;
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
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, ns, p, CASE, |st, ns, p| {
            self.scrutinee.print(db, st, ns, p)?;
            p.space()?;
            p.text("case")?;
            p.space()?;
            p.text("{")?;
            p.cgroup(0, |p| {
                p.space()?;
                if let Some((first, rest)) = self.branches.split_first() {
                    print_internal_subterm(db, st, ns, p, first)?;
                    p.space()?;
                    for branch in rest {
                        p.text("|")?;
                        p.space()?;
                        print_internal_subterm(db, st, ns, p, branch)?;
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
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        let mut fresh_names = Vec::new();
        for i in 0..self.body.arity {
            let name = self.body.names.get(i)
                .cloned()
                .unwrap_or_else(|| format!("{}", st.depth + i));
            let fresh_name = ns.push_fresh(name);
            fresh_names.push(fresh_name);
        }

        self.constructor.print(db, st, ns, p)?;
        if self.body.arity > 0 {
            p.space()?;
        }
        for (i, fresh_name) in fresh_names.iter().enumerate() {
            if i > 0 {
                p.space()?;
            }
            p.text_owned(format!("%{}", fresh_name))?;
        }
        p.space()?;
        p.text("=>")?;
        p.space()?;
        let body_st = st.under_binders(self.body.arity);
        let result = print_internal_subterm(db, body_st, ns, p, &*self.body.body);

        for _ in 0..self.body.arity {
            ns.pop();
        }

        result
    }
}

impl<'db> Print for HardwareUniverse<'db> {
    fn print<R: Render>(
        &self,
        _db: &dyn salsa::Database,
        st: State,
        _ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, _ns, p, HARDWARE_UNIVERSE, |_st, _ns, p| {
            p.text("HardwareUniverse")
        })
    }
}

impl<'db> Print for SLift<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, ns, p, SLIFT, |st, ns, p| {
            p.text("^s")?;
            print_rhs_subterm(db, st, ns, p, &*self.ty, SLIFT.rhs_prec())
        })
    }
}

impl<'db> Print for MLift<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, ns, p, MLIFT, |st, ns, p| {
            p.text("^m")?;
            print_rhs_subterm(db, st, ns, p, &*self.ty, MLIFT.rhs_prec())
        })
    }
}

impl<'db> Print for SignalUniverse<'db> {
    fn print<R: Render>(
        &self,
        _db: &dyn salsa::Database,
        st: State,
        _ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, _ns, p, SIGNAL_UNIVERSE, |_st, _ns, p| p.text("SignalUniverse"))
    }
}

impl<'db> Print for Bit<'db> {
    fn print<R: Render>(
        &self,
        _db: &dyn salsa::Database,
        st: State,
        _ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, _ns, p, BIT, |_st, _ns, p| p.text("Bit"))
    }
}

impl<'db> Print for Zero<'db> {
    fn print<R: Render>(
        &self,
        _db: &dyn salsa::Database,
        st: State,
        _ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, _ns, p, ZERO, |_st, _ns, p| p.text("0"))
    }
}

impl<'db> Print for One<'db> {
    fn print<R: Render>(
        &self,
        _db: &dyn salsa::Database,
        st: State,
        _ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, _ns, p, ONE, |_st, _ns, p| p.text("1"))
    }
}

impl<'db> Print for ModuleUniverse<'db> {
    fn print<R: Render>(
        &self,
        _db: &dyn salsa::Database,
        _st: State,
        _ns: &mut NameStack,
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
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, ns, p, HARROW, |st, ns, p| {
            p.cgroup(0, |p| {
                print_lhs_subterm(db, st, ns, p, &*self.source, HARROW.lhs_prec())?;
                p.space()?;
                p.text("→")?;
                p.space()?;
                print_rhs_subterm(db, st, ns, p, &*self.target, HARROW.rhs_prec())
            })
        })
    }
}

impl<'db> Print for Module<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, ns, p, MODULE, |st, ns, p| {
            p.cgroup(2, |p| {
                let mut next = self;
                let mut st = st;
                let initial_stack_depth = ns.len();

                p.cgroup(0, |p| {
                    p.text("mod ")?;
                    loop {
                        let fresh_name = ns.push_fresh(next.body.name.clone());
                        p.text_owned(format!("%{}", fresh_name))?;
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
                let body_result = print_rhs_subterm(db, st, ns, p, &*next.body, MODULE.rhs_prec());

                while ns.len() > initial_stack_depth {
                    ns.pop();
                }

                body_result
            })
        })
    }
}

impl<'db> Print for HApplication<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, ns, p, HAPP, |st, ns, p| {
            // Print: module<module_ty>(argument)
            p.cgroup(0, |p| {
                print_internal_subterm(db, st, ns, p, &*self.module)?;
                p.text("<")?;
                print_internal_subterm(db, st, ns, p, &*self.module_ty)?;
                p.text(">")?;
                p.text("(")?;
                print_internal_subterm(db, st, ns, p, &*self.argument)?;
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
        _ns: &mut NameStack,
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
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        self.name.print(db, st, ns, p)
    }
}

impl<'db> Print for Variable<'db> {
    fn print<R: Render>(
        &self,
        _db: &dyn salsa::Database,
        st: State,
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        if self.index.is_bound(st.depth) {
            let stack_index = ns.len().saturating_sub(1 + self.index.0);
            if let Some(name) = ns.get(stack_index) {
                p.text_owned(format!("%{}", name))
            } else {
                p.text_owned(format!("%{}", self.index.to_level(st.depth)))
            }
        } else {
            p.text_owned(format!("{}", self.index.to_negative_level(st.depth)))
        }
    }
}

impl<'db> Print for Metavariable<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        p.text("?[")?;
        p.text_owned(&format!("{}", self.id))?;
        for arg in &self.substitution {
            p.text(" ")?;
            arg.print(db, st, ns, p)?;
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
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        // Print: let %x : ty = value; body
        // Push the binder name onto the stack (with freshening to avoid shadowing ambiguity)
        let fresh_name = ns.push_fresh(self.body.name.clone());

        let result = p.cgroup(2, |p| {
            p.text("let ")?;
            // Print the freshened name in the binder position
            p.text_owned(format!("%{}", fresh_name))?;
            p.text(" : ")?;
            print_internal_subterm(db, st, ns, p, &*self.ty)?;
            p.text(" = ")?;
            print_internal_subterm(db, st, ns, p, &*self.value)?;
            p.text(";")?;
            p.space()?;
            print_internal_subterm(db, st, ns, p, &self.body)
        });

        // Pop the binder name
        ns.pop();
        result
    }
}

impl<'db> Print for Check<'db> {
    fn print<R: Render>(
        &self,
        db: &dyn salsa::Database,
        st: State,
        ns: &mut NameStack,
        p: &mut Printer<R>,
    ) -> Result<(), R::Error> {
        ensure(st, ns, p, CHECK, |st, ns, p| {
            p.igroup(0, |p| {
                print_lhs_subterm(db, st, ns, p, &*self.term, CHECK.lhs_prec())?;
                p.text(" :")?;
                p.space()?;
                print_rhs_subterm(db, st, ns, p, &*self.ty, CHECK.rhs_prec())
            })
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{Index, MetaVariableId};
    use crate::TestDatabase;
    use hwml_support::IntoWithDb;
    use insta::assert_snapshot;

    /// Helper to print syntax and return string
    fn p(db: &TestDatabase, s: &Syntax) -> String {
        print_syntax_to_string(db, s)
    }

    // =========================================================================
    // Core Type Theory
    // =========================================================================

    #[test]
    fn print_universe_code() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::UniverseCode(0)), @"𝒰0");
        assert_snapshot!(p(&db, &Syntax::UniverseCode(1)), @"𝒰1");
    }

    #[test]
    fn print_pi_code() {
        let db = TestDatabase::default();
        let pi1: RcSyntax = Syntax::PiCode(
            Syntax::UniverseCode(0).into(),
            Icit::Explicit,
            Binding::anonymous(Syntax::UniverseCode(1).into()),
        )
        .into();
        assert_snapshot!(p(&db, &pi1), @"∀ (%0 : 𝒰0) → 𝒰1");
        let inner: RcSyntax = Syntax::PiCode(
            Syntax::variable_rc(Index(0)),
            Icit::Explicit,
            Binding::anonymous(Syntax::variable_rc(Index(0))),
        )
        .into();
        let pi2: RcSyntax = Syntax::PiCode(
            Syntax::UniverseCode(0).into(),
            Icit::Explicit,
            Binding::anonymous(inner),
        )
        .into();
        assert_snapshot!(p(&db, &pi2), @"∀ (%0 : 𝒰0) → ∀ (%1 : %_) → %_");
    }

    #[test]
    fn print_lambda() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::lambda(Icit::Explicit, Binding::anonymous(Syntax::variable_rc(Index(0))))), @"λ %_ → %_");
        assert_snapshot!(p(&db, &Syntax::lambda(Icit::Explicit, Binding::anonymous(Syntax::lambda_rc(Icit::Explicit, Binding::anonymous(Syntax::variable_rc(Index(1))))))), @"λ %_ %_ → %_");
    }

    #[test]
    fn print_application() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::application(Syntax::constant_rc("f".into_with_db(&db)), Syntax::constant_rc("x".into_with_db(&db)), Icit::Explicit)), @"@/f[@/x]");
        assert_snapshot!(p(&db, &Syntax::application(Syntax::application_rc(Syntax::constant_rc("f".into_with_db(&db)), Syntax::constant_rc("x".into_with_db(&db)), Icit::Explicit), Syntax::constant_rc("y".into_with_db(&db)), Icit::Explicit)), @"@/f[@/x, @/y]");
    }

    // =========================================================================
    // Inductive Types
    // =========================================================================

    #[test]
    fn print_type_constructor() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::type_constructor("Nat".into_with_db(&db), vec![])), @"#[@/Nat]");
        assert_snapshot!(p(&db, &Syntax::type_constructor("Vec".into_with_db(&db), vec![Syntax::constant_rc("A".into_with_db(&db)), Syntax::constant_rc("n".into_with_db(&db))])), @"#[@/Vec @/A @/n]");
    }

    #[test]
    fn print_data_constructor() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::data_constructor("Nil".into_with_db(&db), vec![])), @"[@/Nil]");
        assert_snapshot!(p(&db, &Syntax::data_constructor("Cons".into_with_db(&db), vec![Syntax::constant_rc("x".into_with_db(&db)), Syntax::constant_rc("xs".into_with_db(&db))])), @"[@/Cons @/x @/xs]");
    }

    #[test]
    fn print_case() {
        let db = TestDatabase::default();
        // Case with scrutinee at Index(0), which means the most recently bound variable
        // At depth 1 (under one binder), Index(0) prints as %0
        assert_snapshot!(p(&db, &Syntax::lambda_rc(Icit::Explicit, Binding::anonymous(Syntax::case_rc(
                        Index(0),
            vec![
                CaseBranch::new("Zero".into_with_db(&db), DynBinding::new(0, Syntax::constant_rc("a".into_with_db(&db)))),
                CaseBranch::new("Succ".into_with_db(&db), DynBinding::new(1, Syntax::variable_rc(Index(0)))),
            ]
        )))), @"λ %_ → %_ case { @/Zero => @/a | @/Succ %_0 => %_0 }");
    }

    // =========================================================================
    // Hardware Universe
    // =========================================================================

    #[test]
    fn print_hardware_universe() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::hardware()), @"HardwareUniverse");
    }

    #[test]
    fn print_slift() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::slift(Syntax::bit_rc())), @"^sBit");
    }

    #[test]
    fn print_mlift() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::mlift(Syntax::harrow_rc(Syntax::bit_rc(), Syntax::bit_rc()))), @"^m(Bit → Bit)");
    }

    // =========================================================================
    // Signal Universe
    // =========================================================================

    #[test]
    fn print_signal_universe() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::signal_universe()), @"SignalUniverse");
    }

    #[test]
    fn print_bit() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::bit()), @"Bit");
    }

    #[test]
    fn print_zero() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::zero()), @"0");
    }

    #[test]
    fn print_one() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::one()), @"1");
    }

    // =========================================================================
    // Equality Types
    // =========================================================================

    #[test]
    fn print_eq_type() {
        let db = TestDatabase::default();
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
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::refl()), @"refl");
    }

    #[test]
    fn print_transport() {
        let db = TestDatabase::default();
        // The motive is just a regular syntax term now, not a Closure
        let motive = Syntax::variable_rc(Index(0)); // !0 (unbound at depth 0)
        let transport =
            Syntax::transport_rc(motive, Syntax::refl_rc(), Syntax::variable_rc(Index(2)));
        // Prints as: transport VALUE to MOTIVE by PROOF
        assert_snapshot!(p(&db, &transport), @"transport !2 to !0 by refl");

        // Test with lambda motive - keywords eliminate need for parentheses
        let lambda_motive = Syntax::lambda_rc(Icit::Explicit, Binding::anonymous(Syntax::bit_rc()));
        let transport2 = Syntax::transport_rc(lambda_motive, Syntax::refl_rc(), Syntax::zero_rc());
        assert_snapshot!(p(&db, &transport2), @"transport 0 to λ %_ → Bit by refl");
    }

    // =========================================================================
    // Module Universe
    // =========================================================================

    #[test]
    fn print_module_universe() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::module_universe()), @"ModuleUniverse");
    }

    #[test]
    fn print_harrow() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::harrow(Syntax::bit_rc(), Syntax::bit_rc())), @"Bit → Bit");
        assert_snapshot!(p(&db, &Syntax::harrow(Syntax::bit_rc(), Syntax::harrow_rc(Syntax::bit_rc(), Syntax::bit_rc()))), @"Bit → Bit → Bit");
    }

    #[test]
    fn print_module() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::module(Binding::anonymous(Syntax::variable_rc(Index(0))))), @"mod %_ → %_");
        assert_snapshot!(p(&db, &Syntax::module(Binding::anonymous(Syntax::module_rc(Binding::anonymous(Syntax::variable_rc(Index(1))))))), @"mod %_ %_ → %_");
    }

    #[test]
    fn print_happlication() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::happlication(
                        Syntax::constant_rc("m".into_with_db(&db)),
            Syntax::harrow_rc(Syntax::bit_rc(), Syntax::bit_rc()),
            Syntax::constant_rc("x".into_with_db(&db))
        )), @"@/m<Bit → Bit>(@/x)");
    }

    // =========================================================================
    // Variables and References
    // =========================================================================

    #[test]
    fn print_prim() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::prim_from(&db, "and")), @"$/and");
    }

    #[test]
    fn print_constant() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::constant_from(&db, "myConst")), @"@/myConst");
    }

    #[test]
    fn print_variable_bound() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::lambda(Icit::Explicit, Binding::anonymous(Syntax::variable_rc(Index(0))))), @"λ %_ → %_");
    }

    #[test]
    fn print_variable_unbound() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::variable(Index(0))), @"!0");
        assert_snapshot!(p(&db, &Syntax::variable(Index(1))), @"!1");
    }

    #[test]
    fn print_metavariable() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::metavariable(MetaVariableId::new(0), vec![])), @"?[0]");
        assert_snapshot!(p(&db, &Syntax::metavariable(MetaVariableId::new(1), vec![Syntax::variable_rc(Index(0)), Syntax::variable_rc(Index(1))])), @"?[1 !0 !1]");
    }

    // =========================================================================
    // Type Annotations
    // =========================================================================

    #[test]
    fn print_check() {
        let db = TestDatabase::default();
        assert_snapshot!(p(&db, &Syntax::check(Syntax::UniverseCode(0).into(), Syntax::constant_rc("x".into_with_db(&db)))), @"@/x : 𝒰0");
    }

    // =========================================================================
    // Hierarchical Qualified Names in Declarations
    // =========================================================================

    #[test]
    fn print_constant_hierarchical_two_components() {
        let db = TestDatabase::default();
        let foo: QualifiedName = hwml_support::FromWithDb::from_with_db(&db, "foo");
        let foo_bar = foo.qualify_name(&db, "bar");
        assert_snapshot!(p(&db, &Syntax::constant_rc(foo_bar)), @"@foo/bar");
    }

    #[test]
    fn print_constant_hierarchical_three_components() {
        let db = TestDatabase::default();
        let foo: QualifiedName = hwml_support::FromWithDb::from_with_db(&db, "foo");
        let foo_bar = foo.qualify_name(&db, "bar");
        let foo_bar_baz = foo_bar.qualify_name(&db, "baz");
        assert_snapshot!(p(&db, &Syntax::constant_rc(foo_bar_baz)), @"@foo/bar/baz");
    }

    #[test]
    fn print_primitive_hierarchical_two_components() {
        let db = TestDatabase::default();
        let path: QualifiedName = hwml_support::FromWithDb::from_with_db(&db, "path");
        let path_to = path.qualify_name(&db, "to");
        assert_snapshot!(p(&db, &Syntax::prim_rc(path_to)), @"$path/to");
    }

    #[test]
    fn print_primitive_hierarchical_three_components() {
        let db = TestDatabase::default();
        let path: QualifiedName = hwml_support::FromWithDb::from_with_db(&db, "path");
        let path_to = path.qualify_name(&db, "to");
        let path_to_prim = path_to.qualify_name(&db, "prim");
        assert_snapshot!(p(&db, &Syntax::prim_rc(path_to_prim)), @"$path/to/prim");
    }

    #[test]
    fn print_type_constructor_hierarchical() {
        let db = TestDatabase::default();
        let std: QualifiedName = hwml_support::FromWithDb::from_with_db(&db, "std");
        let std_vec = std.qualify_name(&db, "Vec");
        assert_snapshot!(
            p(&db, &Syntax::type_constructor(std_vec, vec![Syntax::constant_rc("A".into_with_db(&db))])),
            @"#[@std/Vec @/A]"
        );
    }

    #[test]
    fn print_data_constructor_hierarchical() {
        let db = TestDatabase::default();
        let std: QualifiedName = hwml_support::FromWithDb::from_with_db(&db, "std");
        let std_some = std.qualify_name(&db, "Some");
        assert_snapshot!(
            p(&db, &Syntax::data_constructor(std_some, vec![Syntax::constant_rc("x".into_with_db(&db))])),
            @"[@std/Some @/x]"
        );
    }
}
