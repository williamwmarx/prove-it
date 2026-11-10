// Ported from Z3 (src/math/dd/pdd_interval.h), MIT license, see z3-license.txt. The interval of a
// pdd under the intervals of its variables, as x*hi + lo by interval arithmetic. The distributed
// variant, which nla does not call, is not ported.
use crate::lp::dep_intervals::{DepInterval, DepsMode, add, mk_dep_interval, mul, set_value};
use crate::lp::pdd::{Pdd, PddManager};

pub fn get_pdd_interval(
    manager: &PddManager,
    poly: Pdd,
    mode: DepsMode,
    get_var_interval: &mut dyn FnMut(usize, DepsMode) -> DepInterval,
) -> DepInterval {
    let mut result = mk_dep_interval();
    if manager.is_val(poly) {
        set_value(&mut result, manager.val(poly));
        return result;
    }
    let var_interval = get_var_interval(manager.var(poly), mode);
    let hi = get_pdd_interval(manager, manager.hi(poly), mode, get_var_interval);
    let lo = get_pdd_interval(manager, manager.lo(poly), mode, get_var_interval);
    let mut product = mk_dep_interval();
    mul(&hi, &var_interval, &mut product, mode);
    add(&product, &lo, &mut result, mode);
    result
}
