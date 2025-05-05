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

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Serialize, Deserialize)]
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
}
