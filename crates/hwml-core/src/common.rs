use serde::{Deserialize, Serialize};
use std::{
    convert::{From, Into},
    fmt::{self, Display, Formatter},
    str::{self, FromStr},
};

#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum DBParseError {
    MissingSigil(&'static str),
    ParseIntError(std::num::ParseIntError),
}

fn db_parse(sigil: &'static str, str: &str) -> Result<usize, DBParseError> {
    if !str.starts_with(sigil) {
        return Err(DBParseError::MissingSigil(sigil));
    }
    let x: usize = str[sigil.len()..].parse()?;
    Ok(x)
}

impl From<std::num::ParseIntError> for DBParseError {
    fn from(err: std::num::ParseIntError) -> Self {
        Self::ParseIntError(err)
    }
}

impl Display for DBParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            DBParseError::MissingSigil(sig) => write!(f, "missing sigil '{}'", sig),
            DBParseError::ParseIntError(err) => err.fmt(f),
        }
    }
}

#[derive(Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Serialize, Deserialize)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Level(pub usize);

impl Level {
    pub fn new(x: usize) -> Level {
        Level(x)
    }

    pub fn to_index(self, depth: usize) -> Index {
        Index(depth - self.0 - 1)
    }
}

impl Display for Level {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "%{}", self.0)
    }
}

impl FromStr for Level {
    type Err = DBParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match db_parse("?", s) {
            Ok(x) => Ok(Level::from(x)),
            Err(err) => Err(err),
        }
    }
}

impl Into<usize> for Level {
    fn into(self) -> usize {
        self.0
    }
}

impl From<usize> for Level {
    fn from(x: usize) -> Level {
        Level(x)
    }
}

#[derive(Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Serialize, Deserialize)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct NegativeLevel(pub usize);

impl NegativeLevel {
    pub fn new(x: usize) -> NegativeLevel {
        assert!(x >= 1);
        NegativeLevel(x)
    }

    pub fn to_index(self, depth: usize) -> Option<Index> {
        match depth.checked_add(self.0 - 1) {
            Some(i) => Some(Index(i)),
            None => None,
        }
    }
}

impl Display for NegativeLevel {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "!{}", self.0)
    }
}

impl FromStr for NegativeLevel {
    type Err = DBParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match db_parse("!", s) {
            Ok(x) => Ok(NegativeLevel::from(x)),
            Err(err) => Err(err),
        }
    }
}

impl Into<usize> for NegativeLevel {
    fn into(self) -> usize {
        self.0
    }
}

impl From<usize> for NegativeLevel {
    fn from(x: usize) -> NegativeLevel {
        NegativeLevel(x)
    }
}

#[derive(Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Serialize, Deserialize)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Index(pub usize);

impl Index {
    pub fn new(x: usize) -> Index {
        Index(x)
    }

    pub fn to_level(self, depth: usize) -> Level {
        Level(depth - self.0 - 1)
    }

    pub fn to_negative_level(self, depth: usize) -> NegativeLevel {
        NegativeLevel(self.0 - depth + 1)
    }

    pub fn raise(self, amount: usize) -> Index {
        Index(self.0 + amount)
    }

    pub fn is_bound(self, depth: usize) -> bool {
        self.0 < depth
    }
}

impl Display for Index {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "${}", self.0)
    }
}

impl FromStr for Index {
    type Err = DBParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match db_parse("$", s) {
            Ok(x) => Ok(Index::from(x)),
            Err(err) => Err(err),
        }
    }
}

impl Into<usize> for Index {
    fn into(self) -> usize {
        self.0
    }
}

impl From<usize> for Index {
    fn from(x: usize) -> Index {
        Index(x)
    }
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Clone, Copy)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct UniverseLevel(pub usize);

impl Display for UniverseLevel {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "^{}", self.0)
    }
}

impl FromStr for UniverseLevel {
    type Err = DBParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match db_parse("!", s) {
            Ok(x) => Ok(UniverseLevel::from(x)),
            Err(err) => Err(err),
        }
    }
}

impl Into<usize> for UniverseLevel {
    fn into(self) -> usize {
        self.0
    }
}

impl From<usize> for UniverseLevel {
    fn from(x: usize) -> UniverseLevel {
        UniverseLevel(x)
    }
}
