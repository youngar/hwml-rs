use std::{
    fmt::{Display, Formatter},
    hash::Hash,
    rc::Rc,
    str,
};

use elegance::{Printer, Render};
use hwml_support::pp::{State, PP};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Symbol(Rc<str>);

impl Symbol {
    pub fn new(text: &str) -> Symbol {
        Symbol(Rc::from(text))
    }

    pub fn str(&self) -> &str {
        let Symbol(str) = self;
        str
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.str().fmt(f)
    }
}

impl From<Rc<str>> for Symbol {
    fn from(s: Rc<str>) -> Symbol {
        Symbol(s)
    }
}

impl From<&str> for Symbol {
    fn from(s: &str) -> Self {
        Symbol(Rc::from(s))
    }
}

impl From<String> for Symbol {
    fn from(s: String) -> Symbol {
        Symbol(Rc::from(s))
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum Component {
    Sym(Symbol),
    Num(usize),
}

impl Display for Component {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Component::Sym(sym) => sym.fmt(f),
            Component::Num(num) => num.fmt(f),
        }
    }
}

impl<T> From<T> for Component
where
    T: Into<Symbol>,
{
    fn from(x: T) -> Component {
        Component::Sym(x.into())
    }
}

impl From<usize> for Component {
    fn from(n: usize) -> Component {
        Component::Num(n)
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum Path {
    Top,
    Ext(Rc<Path>, Component),
}

impl Path {
    pub fn top_rc() -> Rc<Path> {
        Rc::new(Path::Top)
    }

    pub fn ext_rc(prefix: Rc<Path>, extension: Component) -> Rc<Path> {
        Rc::new(Path::Ext(prefix, extension))
    }
}

fn fmt_prefix(path: &Path, f: &mut Formatter<'_>) -> std::fmt::Result {
    match path {
        Path::Top => Ok(()),
        Path::Ext(p, c) => {
            fmt_prefix(p, f)?;
            c.fmt(f)?;
            f.write_str("/")?;
            Ok(())
        }
    }
}

impl Display for Path {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Path::Top => f.write_str("_"),
            Path::Ext(p, c) => {
                fmt_prefix(p, f)?;
                c.fmt(f)
            }
        }
    }
}

impl<T> From<T> for Path
where
    T: Into<Symbol>,
{
    fn from(x: T) -> Path {
        Path::Ext(Path::top_rc(), Component::Sym(x.into()))
    }
}

impl From<usize> for Path {
    fn from(n: usize) -> Path {
        Path::Ext(Path::top_rc(), Component::Num(n))
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Name(Rc<Path>);

impl Name {
    pub fn anon() -> Name {
        Name(Rc::new(Path::Top))
    }

    pub fn top() -> Name {
        Name(Rc::new(Path::Top))
    }

    pub fn path_rc(&self) -> &Rc<Path> {
        let Name(path) = self;
        &path
    }

    pub fn path(&self) -> &Path {
        self.path_rc()
    }

    pub fn ext<T>(&self, c: T) -> Name
    where
        T: Into<Component>,
    {
        Name(Path::ext_rc(self.path_rc().clone(), c.into()))
    }
}

impl Display for Name {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.path().fmt(f)
    }
}

impl PP for Name {
    fn print<R: Render>(&self, _: State, p: &mut Printer<R>) -> Result<(), R::Error> {
        p.text_owned(self.to_string())
    }
}

impl<T> From<T> for Name
where
    T: Into<Path>,
{
    fn from(x: T) -> Name {
        Name(Rc::new(x.into()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_name_to_string() {
        assert_eq!(Name::anon().to_string(), "_");
        assert_eq!(Name::top().ext("foo").to_string(), "foo");
        assert_eq!(Name::top().ext(123).to_string(), "123");
        assert_eq!(
            Name::top()
                .ext("hi")
                .ext("how")
                .ext("are")
                .ext("you")
                .to_string(),
            "hi/how/are/you"
        );
    }
}
