use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Serialize, Deserialize)]
pub struct Level(pub usize);

impl Level {
    pub fn new(x: usize) -> Level {
        Level(x)
    }

    pub fn to_index(self: Level, depth: usize) -> Index {
        Index(depth - self.to_usize() - 1)
    }

    pub fn to_usize(self: Level) -> usize {
        self.0
    }
}

#[derive(Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Serialize, Deserialize)]
pub struct Index(pub usize);

impl Index {
    pub fn new(x: usize) -> Index {
        Index(x)
    }

    pub fn to_level(self: Index, depth: usize) -> Level {
        Level(depth - self.to_usize() - 1)
    }

    pub fn to_usize(self: Index) -> usize {
        self.0
    }

    pub fn raise(self: Index, amount: usize) -> Index {
        Index(self.to_usize() + amount)
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone, Copy)]
pub struct UniverseLevel(pub u32);

impl std::fmt::Display for UniverseLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
