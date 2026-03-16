use hwml_core::*;

#[derive(Clone)]
pub enum Dubbed<'db> {
    Value(TypedValue<'db>),
    Local(Level),
}

#[derive(Clone)]
pub struct Dubbing<'db> {
    pub name: Name<'db>,
    pub subject: Dubbed<'db>,
}

#[derive(Clone)]
pub struct DubbingTable<'db> {
    dubbings: Vec<Dubbing<'db>>,
}

impl<'db> DubbingTable<'db> {
    pub fn new() -> DubbingTable<'db> {
        DubbingTable {
            dubbings: Vec::new(),
        }
    }

    pub fn extend(&mut self, dubbing: Dubbing<'db>) {
        self.dubbings.push(dubbing);
    }

    pub fn resolve(&self, name: Name<'db>) -> Option<Dubbed<'db>> {
        for dubbing in self.dubbings.iter().rev() {
            if dubbing.name == name {
                return Some(dubbing.subject.clone());
            }
        }
        None
    }

    pub fn name<T>(&self, i: T, depth: usize) -> Option<Name<'db>>
    where
        T: Debruijn,
    {
        let i = i.to_level(depth);
        for dubbing in self.dubbings.iter().rev() {
            match &dubbing.subject {
                Dubbed::Local(j) => {
                    if i == *j {
                        return Some(dubbing.name);
                    }
                }
                Dubbed::Value(v) => {
                    todo!("implement equality between level and ")
                }
            }
        }
        None
    }
}
