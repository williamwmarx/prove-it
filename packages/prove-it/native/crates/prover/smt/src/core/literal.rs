//! Ported from Z3 (src/smt/smt_literal.h, src/smt/smt_types.h), MIT license, see z3-license.txt,
//! through `literal.ts`. A Boolean variable numbers an atom. A literal is a variable or its
//! negation, encoded as twice the variable plus one when negated, so a literal indexes per-literal
//! arrays directly.

pub type BoolVar = u32;
pub type Literal = u32;

/// The variable of true. Its positive literal is true and its negative literal false.
pub const TRUE_BOOL_VAR: BoolVar = 0;
pub const TRUE_LITERAL: Literal = 0;
pub const FALSE_LITERAL: Literal = 1;

pub fn mk_literal(bool_var: BoolVar, is_negated: bool) -> Literal {
    bool_var * 2 + u32::from(is_negated)
}

pub fn negate(literal: Literal) -> Literal {
    literal ^ 1
}

pub fn get_var(literal: Literal) -> BoolVar {
    literal >> 1
}

pub fn is_negated(literal: Literal) -> bool {
    literal & 1 == 1
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encodes_a_variable_and_its_sign() {
        let literal = mk_literal(5, true);
        assert_eq!(literal, 11);
        assert_eq!(get_var(literal), 5);
        assert!(is_negated(literal));
        assert_eq!(negate(literal), mk_literal(5, false));
        assert_eq!(negate(TRUE_LITERAL), FALSE_LITERAL);
        assert_eq!(get_var(FALSE_LITERAL), TRUE_BOOL_VAR);
    }
}
