//! CIRCT dialect helpers for building hardware IR.
//!
//! This module provides safe Rust wrappers around CIRCT dialect operations.
//!
//! # Dialects
//!
//! - **HW**: HardwareUniverse structural dialect (modules, ports, instances)
//! - **Comb**: Combinational logic operations (AND, OR, XOR, ADD, etc.)
//! - **Seq**: Sequential logic (registers, clocks, FSMs)

pub mod comb;
pub mod hw;
pub mod seq;

pub use hw::*;
