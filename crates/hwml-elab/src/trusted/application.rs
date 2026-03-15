use crate::*;
use hwml_core::*;

struct Application<A, B> {
    location: Location,
    fun: A,
    arg: B,
}

impl<A, B> Located for Application<A, B> {
    fn location(&self) -> Location {
        self.location
    }
}
