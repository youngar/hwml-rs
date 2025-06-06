
// De-Bruijn Index.
struct Id(usize);

impl Id {
    fn weaken(&self, n: usize) -> Id {
        Id(self.0 + n)
    }
    
    fn rename(&self, n: usize) -> Id {
        Id(self.0 - n)
    }
}

enum Term {
    Lambda (Id, Normal, Term),
    Neutral(Head, [Elim]),
    Type(),
    Pi(Term, Term),
    Sigma(Term, Term),
    Pair(Term, Term),
}

enum Head {
    Value(Normal, Twin),
    Meta(Normal),
}

enum Twin {
    Only,
    TwinL,
    TwinR,
}

enum Elim {
    App(Term),
    Head,
    Tail,
}

type Substitution = [(Nom, Term)];

struct Neutral {
    head: S

}

impl Syntax {
    fn weaken(&self, n: usize) -> Syntax {
        match self {
            Syntax::Var(id) => Syntax::Var(id.weaken(n)),
            Syntax::Meta() => Syntax::Meta(),
            Syntax::Pi() => Syntax::Pi(),
            Syntax::Sigma() => Syntax::Sigma(),
            Syntax::Type() => Syntax::Type(),
            Syntax::Const(s) => Syntax::Const(s.clone()),
        }
    }

    fn rename(&self, n: usize) -> Syntax {
        match self {
            Syntax::Var(id) => Syntax::Var(id.rename(n)),
            Syntax::Meta() => Syntax::Meta(),
            Syntax::Pi() => Syntax::Pi(),
            Syntax::Sigma() => Syntax::Sigma(),
            Syntax::Type() => Syntax::Type(),
            Syntax::Const(s) => Syntax::Const(s.clone()),
        }
    }
}

struct Constraint {
    env: ??,
    l : Syntax
    lt : Syntax,
    r : Syntax,
    rt : Syntax
}