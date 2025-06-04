use crate::{ConstraintId, MetaId};

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Debug)]
pub enum Blocker {
    /// Unblock when the meta is solved.
    Meta(MetaId),
    /// Unblock when the constraint is satisfied.
    Constraint(ConstraintId),
    /// Unblock when all are unblocked.
    All(Vec<Blocker>),
    /// Unblock when any are unblocked.
    Any(Vec<Blocker>),
    /// Unblocked,
    None,
}

impl Blocker {
    pub fn all(mut xs: Vec<Blocker>) -> Blocker {
        xs.retain(|x| x != &Blocker::None);
        if xs.is_empty() {
            return Blocker::None;
        }
        xs.sort();
        xs.dedup();
        Blocker::All(xs)
    }

    pub fn all_and(mut xs: Vec<Blocker>, y: Blocker) -> Blocker {
        match y {
            Blocker::All(ys) => {
                xs.extend(ys);
                Blocker::all(xs)
            }
            y => {
                xs.push(y);
                Blocker::all(xs)
            }
        }
    }

    pub fn and(x: Blocker, y: Blocker) -> Blocker {
        match x {
            Blocker::All(xs) => Blocker::all_and(xs, y),
            x => Blocker::all(vec![x, y]),
        }
    }

    pub fn any(mut xs: Vec<Blocker>) -> Blocker {
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

    pub fn any_or(mut xs: Vec<Blocker>, y: Blocker) -> Blocker {
        match y {
            Blocker::Any(ys) => {
                xs.extend(ys);
                Blocker::any(xs)
            }
            y => {
                xs.push(y);
                Blocker::any(xs)
            }
        }
    }

    pub fn or(x: Blocker, y: Blocker) -> Blocker {
        match x {
            Blocker::Any(xs) => Blocker::any_or(xs, y),
            x => Blocker::any(vec![x, y]),
        }
    }

    pub fn meta(id: MetaId) -> Blocker {
        Blocker::Meta(id)
    }

    pub fn constraint(id: ConstraintId) -> Blocker {
        Blocker::Constraint(id)
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
    pub fn unblock_meta(&mut self, id: MetaId) -> bool {
        match self {
            Blocker::Meta(x) => {
                if *x == id {
                    *self = Blocker::None;
                    return true;
                }
                false
            }
            Blocker::Constraint(_) => false,
            Blocker::All(xs) => {
                xs.retain_mut(|x| !x.unblock_meta(id));
                if xs.is_empty() {
                    *self = Blocker::None;
                    return true;
                }
                false
            }
            Blocker::Any(xs) => {
                if xs.iter_mut().any(|x| x.unblock_meta(id)) {
                    *self = Blocker::None;
                    return true;
                }
                false
            }
            Blocker::None => true,
        }
    }

    /// Unblock a constraint, by ID. If this blocker is now unblocked, return true.
    pub fn unblock_constraint(&mut self, id: ConstraintId) -> bool {
        match self {
            Blocker::Meta(_) => false,
            Blocker::Constraint(x) => {
                if *x == id {
                    *self = Blocker::None;
                    return true;
                }
                false
            }
            Blocker::All(xs) => {
                xs.retain_mut(|x| !x.unblock_constraint(id));
                if xs.is_empty() {
                    *self = Blocker::None;
                    return true;
                }
                false
            }
            Blocker::Any(xs) => {
                if xs.iter_mut().any(|x| x.unblock_constraint(id)) {
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
