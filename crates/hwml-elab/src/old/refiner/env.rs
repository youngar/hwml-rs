use std::ops::Range;
use std::rc::Rc;
use std::result::Result;

use hwml_core::*;
use syn::Syntax;
use val::Value;

type Identifier = String;
type Pos = usize;
type Span = Range<Pos>;

#[derive(Clone, Debug)]
pub struct Cell<A> {
    pub contents: A,
    pub identifier: Identifier,
}

#[derive(Clone, Debug)]
pub struct EnvEntry<'db> {
    pub ty: Rc<Value<'db>>,
    pub tm: Rc<Value<'db>>,
}

pub type EnvCell<'db> = Cell<EnvEntry<'db>>;

#[derive(Clone, Debug)]
pub struct Env<'db> {
    /// Local assumptions.
    pub locals: Vec<EnvCell<'db>>,
    pub location: Option<Span>,
}

impl<'db> Env<'db> {
    pub fn new() -> Env<'db> {
        Env {
            locals: Vec::new(),
            location: None,
        }
    }

    /// Clear the global assumptions.
    pub fn into_global(&self) -> Self {
        Self {
            locals: Vec::new(),
            location: self.location.clone(),
        }
    }

    pub fn size(&self) -> usize {
        self.locals.len()
    }

    pub fn cell(&self, index: Index) -> &EnvCell<'db> {
        let i: usize = index.into();
        &self.locals[i]
    }

    pub fn local_ty(&self, index: Index) -> &Rc<Value<'db>> {
        &self.cell(index).contents.ty
    }

    pub fn resolve_local(&self, id: Identifier) -> Result<&EnvCell<'db>, ()> {
        for cell in &self.locals {
            if cell.identifier == id {
                return Ok(cell);
            }
        }
        Err(())
    }

    pub fn set_location(&mut self, location: Option<Span>) {
        if let Some(span) = location {
            self.location = Some(span);
        }
    }
}
