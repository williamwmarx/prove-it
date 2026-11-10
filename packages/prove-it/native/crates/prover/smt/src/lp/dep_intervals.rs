// Ported from Z3 (src/math/interval/interval.h, src/math/interval/interval_def.h,
// src/math/interval/dep_intervals.h, src/math/interval/dep_intervals.cpp), MIT license, see
// z3-license.txt. Exact rational intervals with open, closed, or infinite bounds, where each bound
// carries the dependency that justifies it. Only the operations nla_intervals, horner,
// pdd_interval, and monomial_bounds call are here; mpq is exact, so there is no rounding.
//
// The TypeScript lets a result be one of the arguments (monomial_bounds' `power(i, k, i)` and
// `mul(p, i, p)`), which Rust's borrows forbid: `power_in_place` and `mul_in_place` are those
// calls. Every operation reads all of its arguments before it writes the result, so for the
// others a caller passes a clone of the argument the result replaces.
use prove_num::Rational;

use crate::lp::dependency::{Dependency, linearize, mk_join};

#[derive(Clone)]
pub struct DepInterval {
    pub lower: Rational,
    pub upper: Rational,
    pub is_lower_open: bool,
    pub is_upper_open: bool,
    pub is_lower_inf: bool,
    pub is_upper_inf: bool,
    pub lower_dep: Dependency,
    pub upper_dep: Dependency,
}

// with_deps_t: whether an operation also computes the dependencies of the result.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DepsMode {
    WithDeps,
    WithoutDeps,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ExtKind {
    MinusInf,
    Numeral,
    PlusInf,
}

#[derive(Clone)]
struct ExtNumeral {
    kind: ExtKind,
    value: Rational,
}

// interval_deps_combine_rule: bitmasks of the argument bounds that justify each result bound.
struct CombineRule {
    lower: u32,
    upper: u32,
}

const DEP_IN_LOWER1: u32 = 1;
const DEP_IN_UPPER1: u32 = 2;
const DEP_IN_LOWER2: u32 = 4;
const DEP_IN_UPPER2: u32 = 8;

pub fn mk_dep_interval() -> DepInterval {
    DepInterval {
        lower: Rational::zero(),
        upper: Rational::zero(),
        is_lower_open: true,
        is_upper_open: true,
        is_lower_inf: true,
        is_upper_inf: true,
        lower_dep: None,
        upper_dep: None,
    }
}

fn minus_inf() -> ExtNumeral {
    ExtNumeral {
        kind: ExtKind::MinusInf,
        value: Rational::zero(),
    }
}

fn plus_inf() -> ExtNumeral {
    ExtNumeral {
        kind: ExtKind::PlusInf,
        value: Rational::zero(),
    }
}

fn mk_numeral(value: Rational) -> ExtNumeral {
    ExtNumeral {
        kind: ExtKind::Numeral,
        value,
    }
}

fn get_lower_ext(interval: &DepInterval) -> ExtNumeral {
    if interval.is_lower_inf {
        minus_inf()
    } else {
        mk_numeral(interval.lower.clone())
    }
}

fn get_upper_ext(interval: &DepInterval) -> ExtNumeral {
    if interval.is_upper_inf {
        plus_inf()
    } else {
        mk_numeral(interval.upper.clone())
    }
}

fn ext_is_zero(numeral: &ExtNumeral) -> bool {
    numeral.kind == ExtKind::Numeral && numeral.value.is_zero()
}

fn ext_is_pos(numeral: &ExtNumeral) -> bool {
    numeral.kind == ExtKind::PlusInf
        || (numeral.kind == ExtKind::Numeral && numeral.value.is_positive())
}

fn ext_is_neg(numeral: &ExtNumeral) -> bool {
    numeral.kind == ExtKind::MinusInf
        || (numeral.kind == ExtKind::Numeral && numeral.value.is_negative())
}

fn ext_add(first: &ExtNumeral, second: &ExtNumeral) -> ExtNumeral {
    if first.kind != ExtKind::Numeral {
        return first.clone();
    }
    if second.kind != ExtKind::Numeral {
        return second.clone();
    }
    mk_numeral(first.value.add(&second.value))
}

fn ext_mul(first: &ExtNumeral, second: &ExtNumeral) -> ExtNumeral {
    if ext_is_zero(first) || ext_is_zero(second) {
        return mk_numeral(Rational::zero());
    }
    if first.kind != ExtKind::Numeral || second.kind != ExtKind::Numeral {
        return if ext_is_pos(first) == ext_is_pos(second) {
            plus_inf()
        } else {
            minus_inf()
        };
    }
    mk_numeral(first.value.mul(&second.value))
}

fn ext_div(first: &ExtNumeral, second: &ExtNumeral) -> ExtNumeral {
    if ext_is_zero(first) {
        return mk_numeral(Rational::zero());
    }
    if first.kind != ExtKind::Numeral {
        return if ext_is_pos(first) == ext_is_pos(second) {
            plus_inf()
        } else {
            minus_inf()
        };
    }
    if second.kind != ExtKind::Numeral {
        return mk_numeral(Rational::zero());
    }
    mk_numeral(first.value.div(&second.value))
}

fn ext_power(numeral: &ExtNumeral, exponent: u32) -> ExtNumeral {
    if numeral.kind == ExtKind::Numeral {
        return mk_numeral(numeral.value.pow(exponent));
    }
    if numeral.kind == ExtKind::MinusInf && exponent.is_multiple_of(2) {
        plus_inf()
    } else {
        numeral.clone()
    }
}

fn ext_eq(first: &ExtNumeral, second: &ExtNumeral) -> bool {
    if first.kind == ExtKind::Numeral {
        second.kind == ExtKind::Numeral && first.value == second.value
    } else {
        first.kind == second.kind
    }
}

fn ext_lt(first: &ExtNumeral, second: &ExtNumeral) -> bool {
    if first.kind == ExtKind::MinusInf {
        return second.kind != ExtKind::MinusInf;
    }
    if first.kind == ExtKind::PlusInf {
        return false;
    }
    if second.kind == ExtKind::Numeral {
        return first.value.compare(&second.value).is_lt();
    }
    second.kind == ExtKind::PlusInf
}

// The bounds of a result go in only after every bound of the arguments is read, since the result
// may be one of the arguments.
fn set_bounds(
    result: &mut DepInterval,
    lower: ExtNumeral,
    is_lower_open: bool,
    upper: ExtNumeral,
    is_upper_open: bool,
) {
    result.is_lower_inf = lower.kind == ExtKind::MinusInf;
    result.lower = lower.value;
    result.is_lower_open = is_lower_open;
    result.is_upper_inf = upper.kind == ExtKind::PlusInf;
    result.upper = upper.value;
    result.is_upper_open = is_upper_open;
}

fn lower_is_neg(interval: &DepInterval) -> bool {
    ext_is_neg(&get_lower_ext(interval))
}

fn lower_is_pos(interval: &DepInterval) -> bool {
    ext_is_pos(&get_lower_ext(interval))
}

fn lower_is_zero(interval: &DepInterval) -> bool {
    ext_is_zero(&get_lower_ext(interval))
}

fn upper_is_neg(interval: &DepInterval) -> bool {
    ext_is_neg(&get_upper_ext(interval))
}

fn upper_is_pos(interval: &DepInterval) -> bool {
    ext_is_pos(&get_upper_ext(interval))
}

fn upper_is_zero(interval: &DepInterval) -> bool {
    ext_is_zero(&get_upper_ext(interval))
}

fn is_p0(interval: &DepInterval) -> bool {
    lower_is_zero(interval) && !interval.is_lower_open
}

fn is_p1(interval: &DepInterval) -> bool {
    lower_is_pos(interval) || (lower_is_zero(interval) && interval.is_lower_open)
}

fn is_n(interval: &DepInterval) -> bool {
    upper_is_neg(interval) || upper_is_zero(interval)
}

fn is_n0(interval: &DepInterval) -> bool {
    upper_is_zero(interval) && !interval.is_upper_open
}

fn is_n1(interval: &DepInterval) -> bool {
    upper_is_neg(interval) || (upper_is_zero(interval) && interval.is_upper_open)
}

fn is_m(interval: &DepInterval) -> bool {
    lower_is_neg(interval) && upper_is_pos(interval)
}

// interval_manager::is_zero, which unlike dep_intervals::is_zero ignores openness.
fn are_bounds_zero(interval: &DepInterval) -> bool {
    lower_is_zero(interval) && upper_is_zero(interval)
}

// The TypeScript returns at once when target is source, which Rust's borrows rule out.
fn im_set(target: &mut DepInterval, source: &DepInterval) {
    if !source.is_lower_inf {
        target.lower = source.lower.clone();
    }
    target.is_lower_inf = source.is_lower_inf;
    if !source.is_upper_inf {
        target.upper = source.upper.clone();
    }
    target.is_upper_inf = source.is_upper_inf;
    target.is_lower_open = source.is_lower_open;
    target.is_upper_open = source.is_upper_open;
}

fn im_add(first: &DepInterval, second: &DepInterval, result: &mut DepInterval) {
    set_bounds(
        result,
        ext_add(&get_lower_ext(first), &get_lower_ext(second)),
        first.is_lower_open || second.is_lower_open,
        ext_add(&get_upper_ext(first), &get_upper_ext(second)),
        first.is_upper_open || second.is_upper_open,
    );
}

// div_mul with inv_k false.
fn im_mul_scalar(scalar: &Rational, interval: &DepInterval, result: &mut DepInterval) {
    if scalar.is_zero() {
        return set_bounds(result, minus_inf(), true, plus_inf(), true);
    }
    let factor = mk_numeral(scalar.clone());
    let lower = ext_mul(&get_lower_ext(interval), &factor);
    let upper = ext_mul(&get_upper_ext(interval), &factor);
    if scalar.is_positive() {
        return set_bounds(
            result,
            lower,
            interval.is_lower_open,
            upper,
            interval.is_upper_open,
        );
    }
    set_bounds(
        result,
        upper,
        interval.is_upper_open,
        lower,
        interval.is_lower_open,
    );
}

fn im_mul(first: &DepInterval, second: &DepInterval, result: &mut DepInterval) {
    if are_bounds_zero(first) {
        return im_set(result, first);
    }
    if are_bounds_zero(second) {
        return im_set(result, second);
    }
    let a = get_lower_ext(first);
    let b = get_upper_ext(first);
    let c = get_lower_ext(second);
    let d = get_upper_ext(second);
    let is_a_open = first.is_lower_open;
    let is_b_open = first.is_upper_open;
    let is_c_open = second.is_lower_open;
    let is_d_open = second.is_upper_open;
    if is_n(first) {
        if is_n(second) {
            return set_bounds(
                result,
                ext_mul(&b, &d),
                if is_n0(first) || is_n0(second) {
                    false
                } else {
                    is_b_open || is_d_open
                },
                ext_mul(&a, &c),
                is_a_open || is_c_open,
            );
        }
        if is_m(second) {
            return set_bounds(
                result,
                ext_mul(&a, &d),
                is_a_open || is_d_open,
                ext_mul(&a, &c),
                is_a_open || is_c_open,
            );
        }
        return set_bounds(
            result,
            ext_mul(&a, &d),
            is_a_open || is_d_open,
            ext_mul(&b, &c),
            if is_n0(first) || is_p0(second) {
                false
            } else {
                is_b_open || is_c_open
            },
        );
    }
    if is_m(first) {
        if is_n(second) {
            return set_bounds(
                result,
                ext_mul(&b, &c),
                is_b_open || is_c_open,
                ext_mul(&a, &c),
                is_a_open || is_c_open,
            );
        }
        if is_m(second) {
            let ad = ext_mul(&a, &d);
            let bc = ext_mul(&b, &c);
            let ac = ext_mul(&a, &c);
            let bd = ext_mul(&b, &d);
            let is_ad_open = is_a_open || is_d_open;
            let is_bc_open = is_b_open || is_c_open;
            let is_ac_open = is_a_open || is_c_open;
            let is_bd_open = is_b_open || is_d_open;
            let is_ad_lower = ext_lt(&ad, &bc) || (ext_eq(&ad, &bc) && !is_ad_open && is_bc_open);
            let is_ac_upper = ext_lt(&bd, &ac) || (ext_eq(&ac, &bd) && !is_ac_open && is_bd_open);
            return set_bounds(
                result,
                if is_ad_lower { ad } else { bc },
                if is_ad_lower { is_ad_open } else { is_bc_open },
                if is_ac_upper { ac } else { bd },
                if is_ac_upper { is_ac_open } else { is_bd_open },
            );
        }
        return set_bounds(
            result,
            ext_mul(&a, &d),
            is_a_open || is_d_open,
            ext_mul(&b, &d),
            is_b_open || is_d_open,
        );
    }
    if is_n(second) {
        return set_bounds(
            result,
            ext_mul(&b, &c),
            is_b_open || is_c_open,
            ext_mul(&a, &d),
            if is_p0(first) || is_n0(second) {
                false
            } else {
                is_a_open || is_d_open
            },
        );
    }
    if is_m(second) {
        return set_bounds(
            result,
            ext_mul(&b, &c),
            is_b_open || is_c_open,
            ext_mul(&b, &d),
            is_b_open || is_d_open,
        );
    }
    set_bounds(
        result,
        ext_mul(&a, &c),
        if is_p0(first) || is_p0(second) {
            false
        } else {
            is_a_open || is_c_open
        },
        ext_mul(&b, &d),
        is_b_open || is_d_open,
    );
}

// The divisor must not contain zero. Like Z3, a zero test of c or d reads the stored value.
fn im_div(first: &DepInterval, second: &DepInterval, result: &mut DepInterval) {
    if are_bounds_zero(first) {
        return set_bounds(
            result,
            mk_numeral(Rational::zero()),
            false,
            mk_numeral(Rational::zero()),
            false,
        );
    }
    let a = get_lower_ext(first);
    let b = get_upper_ext(first);
    let c = get_lower_ext(second);
    let d = get_upper_ext(second);
    let is_a_open = first.is_lower_open;
    let is_b_open = first.is_upper_open;
    let is_c_open = second.is_lower_open;
    let is_d_open = second.is_upper_open;
    let is_c_zero = second.lower.is_zero();
    let is_d_zero = second.upper.is_zero();
    if is_n(first) {
        if is_n1(second) {
            return set_bounds(
                result,
                ext_div(&b, &c),
                if is_n0(first) {
                    false
                } else {
                    is_b_open || is_c_open
                },
                if is_d_zero {
                    plus_inf()
                } else {
                    ext_div(&a, &d)
                },
                is_a_open || is_d_open,
            );
        }
        return set_bounds(
            result,
            if is_c_zero {
                minus_inf()
            } else {
                ext_div(&a, &c)
            },
            is_a_open || is_c_open,
            ext_div(&b, &d),
            if is_n0(first) {
                false
            } else {
                is_b_open || is_d_open
            },
        );
    }
    if is_m(first) {
        if is_n1(second) {
            return set_bounds(
                result,
                if is_d_zero {
                    minus_inf()
                } else {
                    ext_div(&b, &d)
                },
                is_b_open || is_d_open,
                if is_d_zero {
                    plus_inf()
                } else {
                    ext_div(&a, &d)
                },
                is_a_open || is_d_open,
            );
        }
        return set_bounds(
            result,
            if is_c_zero {
                minus_inf()
            } else {
                ext_div(&a, &c)
            },
            is_a_open || is_c_open,
            if is_c_zero {
                plus_inf()
            } else {
                ext_div(&b, &c)
            },
            is_b_open || is_c_open,
        );
    }
    if is_n1(second) {
        return set_bounds(
            result,
            if is_d_zero {
                minus_inf()
            } else {
                ext_div(&b, &d)
            },
            is_b_open || is_d_open,
            ext_div(&a, &c),
            if is_p0(first) {
                false
            } else {
                is_a_open || is_c_open
            },
        );
    }
    set_bounds(
        result,
        ext_div(&a, &d),
        if is_p0(first) {
            false
        } else {
            is_a_open || is_d_open
        },
        if is_c_zero {
            plus_inf()
        } else {
            ext_div(&b, &c)
        },
        is_b_open || is_c_open,
    );
}

fn im_power(interval: &DepInterval, exponent: u32, result: &mut DepInterval) {
    if exponent == 1 {
        return im_set(result, interval);
    }
    let lower = get_lower_ext(interval);
    let upper = get_upper_ext(interval);
    if exponent % 2 == 1 {
        return set_bounds(
            result,
            if interval.is_lower_inf {
                minus_inf()
            } else {
                ext_power(&lower, exponent)
            },
            interval.is_lower_inf || interval.is_lower_open,
            if interval.is_upper_inf {
                plus_inf()
            } else {
                ext_power(&upper, exponent)
            },
            interval.is_upper_inf || interval.is_upper_open,
        );
    }
    if lower_is_pos(interval) {
        return set_bounds(
            result,
            ext_power(&lower, exponent),
            interval.is_lower_open,
            if interval.is_upper_inf {
                plus_inf()
            } else {
                ext_power(&upper, exponent)
            },
            interval.is_upper_inf || interval.is_upper_open,
        );
    }
    if upper_is_neg(interval) {
        return set_bounds(
            result,
            ext_power(&upper, exponent),
            interval.is_upper_open,
            if interval.is_lower_inf {
                plus_inf()
            } else {
                ext_power(&lower, exponent)
            },
            interval.is_lower_inf || interval.is_lower_open,
        );
    }
    let lower_power = ext_power(&lower, exponent);
    let upper_power = ext_power(&upper, exponent);
    let is_lower_power_max = ext_lt(&upper_power, &lower_power)
        || (ext_eq(&lower_power, &upper_power)
            && !interval.is_lower_open
            && interval.is_upper_open);
    set_bounds(
        result,
        mk_numeral(Rational::zero()),
        false,
        if is_lower_power_max {
            lower_power
        } else {
            upper_power
        },
        if is_lower_power_max {
            interval.is_lower_open
        } else {
            interval.is_upper_open
        },
    );
}

fn get_add_rule() -> CombineRule {
    CombineRule {
        lower: DEP_IN_LOWER1 | DEP_IN_LOWER2,
        upper: DEP_IN_UPPER1 | DEP_IN_UPPER2,
    }
}

fn get_mul_rule(first: &DepInterval, second: &DepInterval) -> CombineRule {
    if are_bounds_zero(first) {
        return CombineRule {
            lower: DEP_IN_LOWER1 | DEP_IN_UPPER1,
            upper: DEP_IN_LOWER1 | DEP_IN_UPPER1,
        };
    }
    if are_bounds_zero(second) {
        return CombineRule {
            lower: DEP_IN_LOWER2 | DEP_IN_UPPER2,
            upper: DEP_IN_LOWER2 | DEP_IN_UPPER2,
        };
    }
    if is_n(first) {
        if is_n(second) {
            return CombineRule {
                lower: DEP_IN_UPPER1 | DEP_IN_UPPER2,
                upper: DEP_IN_LOWER1 | DEP_IN_LOWER2 | DEP_IN_UPPER1,
            };
        }
        if is_m(second) {
            return CombineRule {
                lower: DEP_IN_LOWER1 | DEP_IN_UPPER2 | DEP_IN_UPPER1,
                upper: DEP_IN_LOWER1 | DEP_IN_LOWER2 | DEP_IN_UPPER1,
            };
        }
        return CombineRule {
            lower: DEP_IN_LOWER1 | DEP_IN_UPPER2 | DEP_IN_UPPER1,
            upper: DEP_IN_UPPER1 | DEP_IN_LOWER2,
        };
    }
    if is_m(first) {
        if is_n(second) {
            return CombineRule {
                lower: DEP_IN_UPPER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2,
                upper: DEP_IN_LOWER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2,
            };
        }
        if is_m(second) {
            return CombineRule {
                lower: DEP_IN_LOWER1 | DEP_IN_UPPER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2,
                upper: DEP_IN_LOWER1 | DEP_IN_UPPER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2,
            };
        }
        return CombineRule {
            lower: DEP_IN_LOWER1 | DEP_IN_UPPER2 | DEP_IN_LOWER2,
            upper: DEP_IN_UPPER1 | DEP_IN_UPPER2 | DEP_IN_LOWER2,
        };
    }
    if is_n(second) {
        return CombineRule {
            lower: DEP_IN_UPPER1 | DEP_IN_LOWER2 | DEP_IN_LOWER1,
            upper: DEP_IN_LOWER1 | DEP_IN_UPPER2,
        };
    }
    if is_m(second) {
        return CombineRule {
            lower: DEP_IN_UPPER1 | DEP_IN_LOWER2 | DEP_IN_LOWER1,
            upper: DEP_IN_UPPER1 | DEP_IN_UPPER2 | DEP_IN_LOWER1,
        };
    }
    CombineRule {
        lower: DEP_IN_LOWER1 | DEP_IN_LOWER2,
        upper: DEP_IN_UPPER1 | DEP_IN_UPPER2 | DEP_IN_LOWER1,
    }
}

fn get_div_rule(first: &DepInterval, second: &DepInterval) -> CombineRule {
    if are_bounds_zero(first) {
        return if is_p1(second) {
            CombineRule {
                lower: DEP_IN_LOWER1 | DEP_IN_LOWER2,
                upper: DEP_IN_UPPER1 | DEP_IN_LOWER2,
            }
        } else {
            CombineRule {
                lower: DEP_IN_UPPER1 | DEP_IN_UPPER2,
                upper: DEP_IN_LOWER1 | DEP_IN_UPPER2,
            }
        };
    }
    if is_n(first) {
        return if is_n1(second) {
            CombineRule {
                lower: DEP_IN_UPPER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2,
                upper: DEP_IN_LOWER1 | DEP_IN_UPPER2,
            }
        } else {
            CombineRule {
                lower: DEP_IN_LOWER1 | DEP_IN_LOWER2,
                upper: DEP_IN_UPPER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2,
            }
        };
    }
    if is_m(first) {
        return if is_n1(second) {
            CombineRule {
                lower: DEP_IN_UPPER1 | DEP_IN_UPPER2,
                upper: DEP_IN_LOWER1 | DEP_IN_UPPER2,
            }
        } else {
            CombineRule {
                lower: DEP_IN_LOWER1 | DEP_IN_LOWER2,
                upper: DEP_IN_UPPER1 | DEP_IN_LOWER2,
            }
        };
    }
    if is_n1(second) {
        CombineRule {
            lower: DEP_IN_UPPER1 | DEP_IN_UPPER2,
            upper: DEP_IN_LOWER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2,
        }
    } else {
        CombineRule {
            lower: DEP_IN_LOWER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2,
            upper: DEP_IN_UPPER1 | DEP_IN_LOWER2,
        }
    }
}

fn get_power_rule(interval: &DepInterval, exponent: u32) -> CombineRule {
    if exponent == 1 {
        return CombineRule {
            lower: DEP_IN_LOWER1,
            upper: DEP_IN_UPPER1,
        };
    }
    if exponent % 2 == 1 {
        return CombineRule {
            lower: if interval.is_lower_inf {
                0
            } else {
                DEP_IN_LOWER1
            },
            upper: if interval.is_upper_inf {
                0
            } else {
                DEP_IN_UPPER1
            },
        };
    }
    if lower_is_pos(interval) {
        return CombineRule {
            lower: DEP_IN_LOWER1,
            upper: if interval.is_upper_inf {
                0
            } else {
                DEP_IN_LOWER1 | DEP_IN_UPPER1
            },
        };
    }
    if upper_is_neg(interval) {
        return CombineRule {
            lower: DEP_IN_UPPER1,
            upper: if interval.is_lower_inf {
                0
            } else {
                DEP_IN_LOWER1 | DEP_IN_UPPER1
            },
        };
    }
    CombineRule {
        lower: 0,
        upper: DEP_IN_LOWER1 | DEP_IN_UPPER1,
    }
}

// im_config::mk_dependency: the joined dependencies of the bounds in the mask.
fn mk_dependency(first: &DepInterval, second: Option<&DepInterval>, mask: u32) -> Dependency {
    let with_lower1 = if mask & DEP_IN_LOWER1 != 0 {
        first.lower_dep.clone()
    } else {
        None
    };
    let with_lower2 = match second {
        Some(second) if mask & DEP_IN_LOWER2 != 0 => mk_join(&with_lower1, &second.lower_dep),
        _ => with_lower1,
    };
    let with_upper1 = if mask & DEP_IN_UPPER1 != 0 {
        mk_join(&with_lower2, &first.upper_dep)
    } else {
        with_lower2
    };
    match second {
        Some(second) if mask & DEP_IN_UPPER2 != 0 => mk_join(&with_upper1, &second.upper_dep),
        _ => with_upper1,
    }
}

// im_config::add_deps.
fn combine_deps(
    first: &DepInterval,
    second: Option<&DepInterval>,
    rule: &CombineRule,
    result: &mut DepInterval,
) {
    let lower_dep = if result.is_lower_inf {
        None
    } else {
        mk_dependency(first, second, rule.lower)
    };
    let upper_dep = if result.is_upper_inf {
        None
    } else {
        mk_dependency(first, second, rule.upper)
    };
    result.lower_dep = lower_dep;
    result.upper_dep = upper_dep;
}

pub fn set(target: &mut DepInterval, source: &DepInterval, mode: DepsMode) {
    im_set(target, source);
    if mode == DepsMode::WithoutDeps {
        return;
    }
    target.lower_dep = source.lower_dep.clone();
    target.upper_dep = source.upper_dep.clone();
}

pub fn power(interval: &DepInterval, exponent: u32, result: &mut DepInterval, mode: DepsMode) {
    let rule = get_power_rule(interval, exponent);
    im_power(interval, exponent, result);
    if mode == DepsMode::WithDeps {
        combine_deps(interval, None, &rule, result);
    }
}

// power(interval, exponent, interval, mode), where the TypeScript returns at once for exponent 1.
pub fn power_in_place(interval: &mut DepInterval, exponent: u32, mode: DepsMode) {
    if exponent == 1 {
        return;
    }
    let source = interval.clone();
    power(&source, exponent, interval, mode);
}

pub fn mul_scalar(
    scalar: &Rational,
    interval: &DepInterval,
    result: &mut DepInterval,
    mode: DepsMode,
) {
    let lower_dep = interval.lower_dep.clone();
    let upper_dep = interval.upper_dep.clone();
    im_mul_scalar(scalar, interval, result);
    if mode == DepsMode::WithoutDeps {
        return;
    }
    let is_positive = scalar.is_positive();
    result.lower_dep = if is_positive {
        lower_dep.clone()
    } else {
        upper_dep.clone()
    };
    result.upper_dep = if is_positive { upper_dep } else { lower_dep };
}

pub fn mul(first: &DepInterval, second: &DepInterval, result: &mut DepInterval, mode: DepsMode) {
    let rule = get_mul_rule(first, second);
    im_mul(first, second, result);
    if mode == DepsMode::WithDeps {
        combine_deps(first, Some(second), &rule, result);
    }
}

// mul(product, second, product, mode).
pub fn mul_in_place(product: &mut DepInterval, second: &DepInterval, mode: DepsMode) {
    let first = product.clone();
    mul(&first, second, product, mode);
}

pub fn div(first: &DepInterval, second: &DepInterval, result: &mut DepInterval, mode: DepsMode) {
    let rule = get_div_rule(first, second);
    im_div(first, second, result);
    if mode == DepsMode::WithDeps {
        combine_deps(first, Some(second), &rule, result);
    }
}

pub fn add(first: &DepInterval, second: &DepInterval, result: &mut DepInterval, mode: DepsMode) {
    im_add(first, second, result);
    if mode == DepsMode::WithDeps {
        combine_deps(first, Some(second), &get_add_rule(), result);
    }
}

// add(rational, interval): shifts the finite bounds and keeps the dependencies.
pub fn add_scalar(scalar: &Rational, interval: &mut DepInterval) {
    if !interval.is_lower_inf {
        interval.lower = interval.lower.add(scalar);
    }
    if !interval.is_upper_inf {
        interval.upper = interval.upper.add(scalar);
    }
}

fn copy_lower_bound(source: &DepInterval, target: &mut DepInterval, mode: DepsMode) {
    target.is_lower_inf = false;
    target.lower = source.lower.clone();
    target.is_lower_open = source.is_lower_open;
    if mode == DepsMode::WithDeps {
        target.lower_dep = source.lower_dep.clone();
    }
}

fn copy_upper_bound(source: &DepInterval, target: &mut DepInterval, mode: DepsMode) {
    target.is_upper_inf = false;
    target.upper = source.upper.clone();
    target.is_upper_open = source.is_upper_open;
    if mode == DepsMode::WithDeps {
        target.upper_dep = source.upper_dep.clone();
    }
}

// On equal bounds the bound of first wins if it is open, else the bound of second.
pub fn intersect(
    first: &DepInterval,
    second: &DepInterval,
    result: &mut DepInterval,
    mode: DepsMode,
) {
    if !first.is_lower_inf || !second.is_lower_inf {
        let is_first_lower = second.is_lower_inf
            || (!first.is_lower_inf
                && (first.lower.compare(&second.lower).is_gt()
                    || (first.lower == second.lower && first.is_lower_open)));
        copy_lower_bound(if is_first_lower { first } else { second }, result, mode);
    }
    if !first.is_upper_inf || !second.is_upper_inf {
        let is_first_upper = second.is_upper_inf
            || (!first.is_upper_inf
                && (first.upper.compare(&second.upper).is_lt()
                    || (first.upper == second.upper && first.is_upper_open)));
        copy_upper_bound(if is_first_upper { first } else { second }, result, mode);
    }
}

// set_value and set_interval_for_scalar: the closed point interval, keeping the dependencies.
pub fn set_value(interval: &mut DepInterval, value: &Rational) {
    set_bounds(
        interval,
        mk_numeral(value.clone()),
        false,
        mk_numeral(value.clone()),
        false,
    );
}

pub fn set_zero_interval_deps_for_mult(interval: &mut DepInterval) {
    interval.lower_dep = mk_join(&interval.lower_dep, &interval.upper_dep);
    interval.upper_dep = interval.lower_dep.clone();
}

pub fn is_empty(interval: &DepInterval) -> bool {
    if interval.is_lower_inf || interval.is_upper_inf {
        return false;
    }
    let comparison = interval.lower.compare(&interval.upper);
    comparison.is_gt() || (comparison.is_eq() && (interval.is_lower_open || interval.is_upper_open))
}

fn separated_from_zero_on_lower(interval: &DepInterval) -> bool {
    !interval.is_lower_inf
        && !interval.lower.is_negative()
        && !(interval.lower.is_zero() && !interval.is_lower_open)
}

fn separated_from_zero_on_upper(interval: &DepInterval) -> bool {
    !interval.is_upper_inf
        && !interval.upper.is_positive()
        && !(interval.upper.is_zero() && !interval.is_upper_open)
}

pub fn separated_from_zero(interval: &DepInterval) -> bool {
    separated_from_zero_on_upper(interval) || separated_from_zero_on_lower(interval)
}

// When the interval excludes zero, reports the joined dependency of dep and the separating bound,
// lower first.
pub fn check_interval_for_conflict_on_zero(
    interval: &DepInterval,
    dep: &Dependency,
    report: &mut dyn FnMut(Vec<u32>),
) -> bool {
    if separated_from_zero_on_lower(interval) {
        report(linearize(&[mk_join(dep, &interval.lower_dep)]));
        return true;
    }
    if !separated_from_zero_on_upper(interval) {
        return false;
    }
    report(linearize(&[mk_join(dep, &interval.upper_dep)]));
    true
}

pub fn display_dep_interval(interval: &DepInterval) -> String {
    let lower = if interval.is_lower_inf {
        "(-oo".to_string()
    } else {
        format!(
            "{}{}",
            if interval.is_lower_open { "(" } else { "[" },
            interval.lower
        )
    };
    let upper = if interval.is_upper_inf {
        "oo)".to_string()
    } else {
        format!(
            "{}{}",
            interval.upper,
            if interval.is_upper_open { ")" } else { "]" }
        )
    };
    let get_deps = |name: &str, dep: &Dependency| match dep {
        None => String::new(),
        Some(_) => {
            let leaves: Vec<String> = linearize(std::slice::from_ref(dep))
                .iter()
                .map(u32::to_string)
                .collect();
            format!(" {name} {}", leaves.join(" "))
        }
    };
    format!(
        "{lower},{upper}{}{}",
        get_deps("ld", &interval.lower_dep),
        get_deps("ud", &interval.upper_dep)
    )
}
