//! Ported from Z3 (src/util/lbool.h), MIT license, through `lbool.ts`. The three truth values of a
//! literal, an assignment or a search. The TypeScript's numbers `L_TRUE` 1, `L_FALSE` -1 and
//! `L_UNDEF` 0 are `to_i8`.

use std::ops::Not;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(i8)]
pub enum LBool {
    False = -1,
    Undef = 0,
    True = 1,
}

impl LBool {
    pub fn from_bool(value: bool) -> LBool {
        if value { LBool::True } else { LBool::False }
    }

    pub fn to_i8(self) -> i8 {
        self as i8
    }

    /// The value of a TypeScript number: its sign.
    pub fn from_sign(value: i32) -> LBool {
        match value.signum() {
            1 => LBool::True,
            -1 => LBool::False,
            _ => LBool::Undef,
        }
    }
}

/// `-value`: true and false swap, undef stays.
impl Not for LBool {
    type Output = LBool;
    fn not(self) -> LBool {
        LBool::from_sign(-i32::from(self.to_i8()))
    }
}
