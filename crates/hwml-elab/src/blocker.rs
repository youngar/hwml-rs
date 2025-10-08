use hwml_core::syn::Metavariable;

use crate::Constraint;

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Debug)]
pub enum Blocker<'db> {
    /// Unblock when the meta is solved.
    Meta(Metavariable<'db>),
    /// Unblock when the constraint is satisfied.
    Constraint(Constraint<'db>),
    /// Unblock when all are unblocked.
    All(Vec<Blocker<'db>>),
    /// Unblock when any are unblocked.
    Any(Vec<Blocker<'db>>),
    /// Unblocked,
    None,
}

impl<'db> Blocker<'db> {
    pub fn all(mut xs: Vec<Blocker<'db>>) -> Blocker<'db> {
        xs.retain(|x| x != &Blocker::None);
        if xs.is_empty() {
            return Blocker::None;
        }
        xs.sort();
        xs.dedup();
        Blocker::All(xs)
    }

    pub fn all_and(mut xs: Vec<Blocker<'db>>, y: Blocker<'db>) -> Blocker<'db> {
        match y {
            Blocker::All(ys) => xs.extend(ys),
            y => xs.push(y),
        }
        Blocker::all(xs)
    }

    pub fn and(x: Blocker<'db>, y: Blocker<'db>) -> Blocker<'db> {
        if let Blocker::All(xs) = x {
            return Blocker::all_and(xs, y);
        }
        if let Blocker::All(mut ys) = y {
            ys.push(x);
            return Blocker::all(ys);
        }
        Blocker::all(vec![x, y])
    }

    pub fn any(mut xs: Vec<Blocker<'db>>) -> Blocker<'db> {
        if xs.iter().any(|x| x == &Blocker::None) {
            return Blocker::None;
        }
        if xs.is_empty() {
            return Blocker::None;
        }
        xs.sort();
        xs.dedup();
        Blocker::Any(xs)
    }

    pub fn any_or(mut xs: Vec<Blocker<'db>>, y: Blocker<'db>) -> Blocker<'db> {
        match y {
            Blocker::Any(ys) => xs.extend(ys),
            y => xs.push(y),
        }
        Blocker::any(xs)
    }

    pub fn or(x: Blocker<'db>, y: Blocker<'db>) -> Blocker<'db> {
        if let Blocker::Any(xs) = x {
            return Blocker::any_or(xs, y);
        }
        if let Blocker::Any(mut ys) = y {
            ys.push(x);
            return Blocker::any(ys);
        }
        Blocker::any(vec![x, y])
    }

    pub fn meta(meta: Metavariable<'db>) -> Blocker<'db> {
        Blocker::Meta(meta)
    }

    pub fn constraint(constaint: Constraint<'db>) -> Blocker<'db> {
        Blocker::Constraint(constaint)
    }

    pub fn is_blocked(&self) -> bool {
        !self.is_unblocked()
    }

    pub fn is_unblocked(&self) -> bool {
        match self {
            Blocker::Meta(_) => false,
            Blocker::Constraint(_) => false,
            Blocker::All(xs) => xs.iter().all(Self::is_unblocked),
            Blocker::Any(xs) => xs.iter().any(Self::is_unblocked),
            Blocker::None => true,
        }
    }

    /// Unblock a meta, by ID. If this blocker is now unblocked, return true.
    pub fn unblock_meta(&mut self, meta: Metavariable<'db>) -> bool {
        match self {
            Blocker::Meta(x) => {
                if *x == meta {
                    *self = Blocker::None;
                    return true;
                }
                false
            }
            Blocker::Constraint(_) => false,
            Blocker::All(xs) => {
                xs.retain_mut(|x| !x.unblock_meta(meta.clone()));
                if xs.is_empty() {
                    *self = Blocker::None;
                    return true;
                }
                false
            }
            Blocker::Any(xs) => {
                if xs.iter_mut().any(|x| x.unblock_meta(meta.clone())) {
                    *self = Blocker::None;
                    return true;
                }
                false
            }
            Blocker::None => true,
        }
    }

    /// Unblock a constraint. If this blocker is now unblocked, return true.
    pub fn unblock_constraint(&mut self, constraint: &Constraint<'db>) -> bool {
        match self {
            Blocker::Meta(_) => false,
            Blocker::Constraint(x) => {
                if x == constraint {
                    *self = Blocker::None;
                    return true;
                }
                false
            }
            Blocker::All(xs) => {
                xs.retain_mut(|x| !x.unblock_constraint(constraint));
                if xs.is_empty() {
                    *self = Blocker::None;
                    return true;
                }
                false
            }
            Blocker::Any(xs) => {
                if xs.iter_mut().any(|x| x.unblock_constraint(constraint)) {
                    *self = Blocker::None;
                    return true;
                }
                false
            }
            Blocker::None => true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_all_empty() {
        assert_eq!(Blocker::all(vec![]), Blocker::None);
    }

    #[test]
    fn test_all_no_blockers() {
        assert_eq!(Blocker::all(vec![Blocker::None]), Blocker::None);
    }

    #[test]
    fn test_any_empty() {
        assert_eq!(Blocker::any(vec![]), Blocker::None);
    }

    #[test]
    fn test_any_no_blockers() {
        assert_eq!(Blocker::any(vec![Blocker::None]), Blocker::None);
    }
}
