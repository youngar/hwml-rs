//! Combinational (Comb) dialect operations.
//!
//! The Comb dialect provides operations for combinational logic:
//! - Boolean operations (AND, OR, XOR, NOT)
//! - Arithmetic operations (ADD, SUB, MUL, DIV)
//! - Comparison operations (EQ, NE, LT, LE, GT, GE)
//! - Multiplexers and selectors


/// Combinational operation types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CombOp {
    // Boolean operations
    And,
    Or,
    Xor,
    Not,

    // Arithmetic operations
    Add,
    Sub,
    Mul,
    DivU, // Unsigned division
    DivS, // Signed division
    ModU, // Unsigned modulo
    ModS, // Signed modulo

    // Comparison operations
    Eq,
    Ne,
    LtU, // Unsigned less than
    LtS, // Signed less than
    LeU, // Unsigned less than or equal
    LeS, // Signed less than or equal
    GtU, // Unsigned greater than
    GtS, // Signed greater than
    GeU, // Unsigned greater than or equal
    GeS, // Signed greater than or equal

    // Shift operations
    Shl,  // Shift left
    ShrU, // Unsigned shift right
    ShrS, // Signed shift right (arithmetic)

    // Bit manipulation
    Extract, // Extract bits
    Concat,  // Concatenate bits
}

impl CombOp {
    /// Get the MLIR operation name for this combinational operation.
    pub fn operation_name(&self) -> &'static str {
        match self {
            CombOp::And => "comb.and",
            CombOp::Or => "comb.or",
            CombOp::Xor => "comb.xor",
            CombOp::Not => "comb.not",
            CombOp::Add => "comb.add",
            CombOp::Sub => "comb.sub",
            CombOp::Mul => "comb.mul",
            CombOp::DivU => "comb.divu",
            CombOp::DivS => "comb.divs",
            CombOp::ModU => "comb.modu",
            CombOp::ModS => "comb.mods",
            CombOp::Eq => "comb.icmp eq",
            CombOp::Ne => "comb.icmp ne",
            CombOp::LtU => "comb.icmp ult",
            CombOp::LtS => "comb.icmp slt",
            CombOp::LeU => "comb.icmp ule",
            CombOp::LeS => "comb.icmp sle",
            CombOp::GtU => "comb.icmp ugt",
            CombOp::GtS => "comb.icmp sgt",
            CombOp::GeU => "comb.icmp uge",
            CombOp::GeS => "comb.icmp sge",
            CombOp::Shl => "comb.shl",
            CombOp::ShrU => "comb.shru",
            CombOp::ShrS => "comb.shrs",
            CombOp::Extract => "comb.extract",
            CombOp::Concat => "comb.concat",
        }
    }

    /// Check if this operation is binary (takes two operands).
    pub fn is_binary(&self) -> bool {
        !matches!(self, CombOp::Not)
    }

    /// Check if this operation is unary (takes one operand).
    pub fn is_unary(&self) -> bool {
        matches!(self, CombOp::Not)
    }
}

// TODO: Add operation builders using raw MLIR C API when needed

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_comb_op_names() {
        assert_eq!(CombOp::And.operation_name(), "comb.and");
        assert_eq!(CombOp::Or.operation_name(), "comb.or");
        assert_eq!(CombOp::Xor.operation_name(), "comb.xor");
        assert_eq!(CombOp::Add.operation_name(), "comb.add");
    }

    #[test]
    fn test_comb_op_arity() {
        assert!(CombOp::And.is_binary());
        assert!(CombOp::Not.is_unary());
        assert!(!CombOp::Not.is_binary());
    }
}
