// Ported from Z3 (src/nlsat/nlsat_interval_set.cpp), MIT license, see z3-license.txt. Sets of
// disjoint infeasible intervals of the values of one variable, each justified by the literal that
// excludes it. A null set is empty. The bounds are copies of the numbers they were built from, so
// refining a bound while comparing it narrows only that copy, as in Z3.
//
// A union drops the clauses of the intervals it copies, as Z3's push_back does, and this is
// sound. An interval's clause is read only by get_justifications, for R_propagate's lazy
// justification (nlsat_solver.cpp). Its literals come from the justifications alone, and the lazy
// clause they give is valid in the reals by itself. The clauses are used only for three things:
// - resolve_lazy_justification joins their assumptions into the lemma's. Resolution already
//   collects these: each core literal's own justification is resolved, or the literal stays in
//   the lemma.
// - update_var2eq skips a lazy justification with clauses. It also skips one with literals, and
//   every interval brings a literal.
// - Display.
// So a dropped clause can only shrink an over-approximated assumption set, and never removes a
// literal from an explanation.
//
// A null set is `None`. The manager holds no algebraic manager: its methods take it.
use super::algebraic::{AlgebraicManager, Anum};
use super::types::ClauseRef;
use super::{RandomGen, Rational, SmtError};

// A null bound is infinite, and an infinite end is always open.
#[derive(Clone)]
pub struct Interval {
    pub is_lower_open: bool,
    pub lower: Option<Anum>,
    pub is_upper_open: bool,
    pub upper: Option<Anum>,
    pub justification: u32,
    pub clause: Option<ClauseRef>,
}

#[derive(Clone)]
pub struct IntervalSet {
    pub intervals: Vec<Interval>,
    pub is_full: bool,
}

pub struct ComplementMax {
    pub sup: Anum,
    pub is_attained: bool,
}

pub struct Justifications {
    pub literals: Vec<u32>,
    pub clauses: Vec<ClauseRef>,
}

pub struct IntervalSetManager {
    rand: RandomGen,
}

impl Default for IntervalSetManager {
    fn default() -> IntervalSetManager {
        IntervalSetManager {
            rand: RandomGen::new(0),
        }
    }
}

// The finite bound a TS non-null assertion reads.
fn get_bound(bound: &Option<Anum>) -> Result<&Anum, SmtError> {
    bound
        .as_ref()
        .ok_or_else(|| SmtError::Invariant("an interval bound is infinite".to_string()))
}

fn compare_lower_lower(
    am: &mut AlgebraicManager,
    first: &Interval,
    second: &Interval,
) -> Result<i32, SmtError> {
    let Some(first_lower) = &first.lower else {
        return Ok(if second.lower.is_none() { 0 } else { -1 });
    };
    let Some(second_lower) = &second.lower else {
        return Ok(1);
    };
    let sign = am.compare(first_lower, second_lower)?;
    if sign != 0 {
        return Ok(sign);
    }
    if first.is_lower_open == second.is_lower_open {
        return Ok(0);
    }
    Ok(if first.is_lower_open { 1 } else { -1 })
}

fn compare_upper_upper(
    am: &mut AlgebraicManager,
    first: &Interval,
    second: &Interval,
) -> Result<i32, SmtError> {
    let Some(first_upper) = &first.upper else {
        return Ok(if second.upper.is_none() { 0 } else { 1 });
    };
    let Some(second_upper) = &second.upper else {
        return Ok(-1);
    };
    let sign = am.compare(first_upper, second_upper)?;
    if sign != 0 {
        return Ok(sign);
    }
    if first.is_upper_open == second.is_upper_open {
        return Ok(0);
    }
    Ok(if first.is_upper_open { -1 } else { 1 })
}

fn compare_upper_lower(
    am: &mut AlgebraicManager,
    first: &Interval,
    second: &Interval,
) -> Result<i32, SmtError> {
    let (Some(first_upper), Some(second_lower)) = (&first.upper, &second.lower) else {
        return Ok(1);
    };
    let sign = am.compare(first_upper, second_lower)?;
    if sign != 0 {
        return Ok(sign);
    }
    Ok(if !first.is_upper_open && !second.is_lower_open {
        0
    } else {
        -1
    })
}

// adjacent: curr ends where next starts and one of them holds the shared point. Both bounds are
// finite.
fn is_adjacent(
    am: &mut AlgebraicManager,
    current: &Interval,
    next: &Interval,
) -> Result<bool, SmtError> {
    Ok(
        am.compare(get_bound(&current.upper)?, get_bound(&next.lower)?)? == 0
            && (!current.is_upper_open || !next.is_lower_open),
    )
}

// push_back drops the clause, so a union only keeps the clauses of a set it returns unchanged.
fn copy_interval(
    am: &mut AlgebraicManager,
    interval: &Interval,
    is_upper_open: bool,
    upper: Option<&Anum>,
) -> Interval {
    Interval {
        is_lower_open: interval.is_lower_open,
        lower: interval.lower.as_ref().map(|lower| am.copy(lower)),
        is_upper_open,
        upper: upper.map(|upper| am.copy(upper)),
        justification: interval.justification,
        clause: None,
    }
}

// compare_interval_with_zero: -1 when the interval lies below zero, 1 above, 0 when it holds it.
fn compare_interval_with_zero(
    am: &mut AlgebraicManager,
    interval: &Interval,
    zero: &Anum,
) -> Result<i32, SmtError> {
    if let Some(upper) = &interval.upper {
        let sign = am.compare(upper, zero)?;
        if sign < 0 || (sign == 0 && interval.is_upper_open) {
            return Ok(-1);
        }
    }
    if let Some(lower) = &interval.lower {
        let sign = am.compare(lower, zero)?;
        if sign > 0 || (sign == 0 && interval.is_lower_open) {
            return Ok(1);
        }
    }
    Ok(0)
}

// find_complement_sup: the interval whose lower bound is the supremum of the complement, when
// the set reaches +oo and the complement is not empty.
fn find_complement_sup(
    am: &mut AlgebraicManager,
    set: Option<&IntervalSet>,
) -> Result<Option<usize>, SmtError> {
    let Some(set) = set else {
        return Ok(None);
    };
    if set.intervals[set.intervals.len() - 1].upper.is_some() {
        return Ok(None);
    }
    let mut index = set.intervals.len() - 1;
    loop {
        let current = &set.intervals[index];
        let Some(current_lower) = &current.lower else {
            return Ok(None);
        };
        let previous = if index > 0 {
            Some(&set.intervals[index - 1])
        } else {
            None
        };
        match previous {
            None => return Ok(Some(index)),
            Some(previous) => {
                if am.compare(get_bound(&previous.upper)?, current_lower)? < 0
                    || (current.is_lower_open && previous.is_upper_open)
                {
                    return Ok(Some(index));
                }
            }
        }
        index -= 1;
    }
}

impl IntervalSetManager {
    pub fn new() -> IntervalSetManager {
        IntervalSetManager::default()
    }

    pub fn set_seed(&mut self, seed: u32) {
        self.rand = RandomGen::new(seed);
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "the TS signature, and the manager"
    )]
    pub fn mk(
        &self,
        am: &mut AlgebraicManager,
        is_lower_open: bool,
        lower: Option<&Anum>,
        is_upper_open: bool,
        upper: Option<&Anum>,
        justification: u32,
        clause: Option<ClauseRef>,
    ) -> IntervalSet {
        IntervalSet {
            is_full: lower.is_none() && upper.is_none(),
            intervals: vec![Interval {
                is_lower_open,
                lower: lower.map(|lower| am.copy(lower)),
                is_upper_open,
                upper: upper.map(|upper| am.copy(upper)),
                justification,
                clause,
            }],
        }
    }

    pub fn mk_union(
        &self,
        am: &mut AlgebraicManager,
        first: Option<&IntervalSet>,
        second: Option<&IntervalSet>,
    ) -> Result<Option<IntervalSet>, SmtError> {
        let Some(first) = first else {
            return Ok(second.cloned());
        };
        if second.is_some_and(|second| std::ptr::eq(first, second)) {
            return Ok(second.cloned());
        }
        let Some(second) = second else {
            return Ok(Some(first.clone()));
        };
        if first.is_full {
            return Ok(Some(first.clone()));
        }
        if second.is_full {
            return Ok(Some(second.clone()));
        }
        let mut result: Vec<Interval> = Vec::new();
        let mut first_index = 0;
        let mut second_index = 0;
        while first_index < first.intervals.len() && second_index < second.intervals.len() {
            let first_interval = &first.intervals[first_index];
            let second_interval = &second.intervals[second_index];
            let lower_sign = compare_lower_lower(am, first_interval, second_interval)?;
            let upper_sign = compare_upper_upper(am, first_interval, second_interval)?;
            if lower_sign <= 0 {
                if upper_sign == 0 {
                    result.push(copy_interval(
                        am,
                        first_interval,
                        first_interval.is_upper_open,
                        first_interval.upper.as_ref(),
                    ));
                    first_index += 1;
                    second_index += 1;
                } else if upper_sign > 0 {
                    second_index += 1;
                } else {
                    let touch_sign = compare_upper_lower(am, first_interval, second_interval)?;
                    if touch_sign < 0 {
                        result.push(copy_interval(
                            am,
                            first_interval,
                            first_interval.is_upper_open,
                            first_interval.upper.as_ref(),
                        ));
                    } else if touch_sign == 0 {
                        if lower_sign != 0 {
                            result.push(copy_interval(
                                am,
                                first_interval,
                                true,
                                first_interval.upper.as_ref(),
                            ));
                        }
                    } else if lower_sign != 0 {
                        result.push(copy_interval(
                            am,
                            first_interval,
                            !second_interval.is_lower_open,
                            second_interval.lower.as_ref(),
                        ));
                    }
                    first_index += 1;
                }
            } else if upper_sign == 0 {
                result.push(copy_interval(
                    am,
                    second_interval,
                    second_interval.is_upper_open,
                    second_interval.upper.as_ref(),
                ));
                first_index += 1;
                second_index += 1;
            } else if upper_sign < 0 {
                first_index += 1;
            } else {
                let touch_sign = compare_upper_lower(am, second_interval, first_interval)?;
                if touch_sign < 0 {
                    result.push(copy_interval(
                        am,
                        second_interval,
                        second_interval.is_upper_open,
                        second_interval.upper.as_ref(),
                    ));
                } else if touch_sign == 0 {
                    result.push(copy_interval(
                        am,
                        second_interval,
                        true,
                        second_interval.upper.as_ref(),
                    ));
                } else {
                    result.push(copy_interval(
                        am,
                        second_interval,
                        !first_interval.is_lower_open,
                        first_interval.lower.as_ref(),
                    ));
                }
                second_index += 1;
            }
        }
        for interval in &first.intervals[first_index..] {
            result.push(copy_interval(
                am,
                interval,
                interval.is_upper_open,
                interval.upper.as_ref(),
            ));
        }
        for interval in &second.intervals[second_index..] {
            result.push(copy_interval(
                am,
                interval,
                interval.is_upper_open,
                interval.upper.as_ref(),
            ));
        }
        // Merge adjacent intervals with the same justification.
        let mut merged: Vec<Interval> = Vec::new();
        for next in result {
            if let Some(current) = merged.last_mut()
                && current.justification == next.justification
                && is_adjacent(am, current, &next)?
            {
                current.is_upper_open = next.is_upper_open;
                current.upper = next.upper;
                continue;
            }
            merged.push(next);
        }
        let mut is_slack = merged[0].lower.is_some() || merged[merged.len() - 1].upper.is_some();
        let mut index = 0;
        while index + 1 < merged.len() && !is_slack {
            if !is_adjacent(am, &merged[index], &merged[index + 1])? {
                is_slack = true;
            }
            index += 1;
        }
        Ok(Some(IntervalSet {
            intervals: merged,
            is_full: !is_slack,
        }))
    }

    pub fn is_full(&self, set: Option<&IntervalSet>) -> bool {
        set.is_some_and(|set| set.is_full)
    }

    // subset: every interval of first lies in a run of adjacent intervals of second.
    pub fn subset(
        &self,
        am: &mut AlgebraicManager,
        first: Option<&IntervalSet>,
        second: Option<&IntervalSet>,
    ) -> Result<bool, SmtError> {
        let Some(first) = first else {
            return Ok(true);
        };
        if second.is_some_and(|second| std::ptr::eq(first, second)) {
            return Ok(true);
        }
        let Some(second) = second else {
            return Ok(false);
        };
        if second.is_full {
            return Ok(true);
        }
        if first.is_full {
            return Ok(false);
        }
        let mut first_index = 0;
        let mut second_index = 0;
        while first_index < first.intervals.len() && second_index < second.intervals.len() {
            let first_interval = &first.intervals[first_index];
            if compare_lower_lower(am, first_interval, &second.intervals[second_index])? < 0 {
                return Ok(false);
            }
            while second_index < second.intervals.len() {
                let second_interval = &second.intervals[second_index];
                let upper_sign = compare_upper_upper(am, first_interval, second_interval)?;
                if upper_sign == 0 {
                    first_index += 1;
                    second_index += 1;
                    break;
                }
                if upper_sign < 0 {
                    first_index += 1;
                    break;
                }
                if compare_upper_lower(am, second_interval, first_interval)? < 0 {
                    second_index += 1;
                    break;
                }
                if second_index == second.intervals.len() - 1 {
                    return Ok(false);
                }
                if !is_adjacent(am, second_interval, &second.intervals[second_index + 1])? {
                    return Ok(false);
                }
                second_index += 1;
            }
        }
        Ok(first_index == first.intervals.len())
    }

    // get_justifications: the distinct justifications in order, and the clauses of the intervals
    // that first bring each.
    pub fn get_justifications(&self, set: Option<&IntervalSet>) -> Justifications {
        let mut literals: Vec<u32> = Vec::new();
        let mut clauses: Vec<ClauseRef> = Vec::new();
        for interval in set.map_or(&[][..], |set| &set.intervals) {
            if literals.contains(&interval.justification) {
                continue;
            }
            literals.push(interval.justification);
            if let Some(clause) = &interval.clause {
                clauses.push(clause.clone());
            }
        }
        Justifications { literals, clauses }
    }

    // pick_in_complement: zero when it is outside the set. Otherwise an integer above the last
    // interval, an integer below the first, or a number in a gap, picked uniformly at random among
    // them when randomizing, else the first found. With no gap, the shared open end of two
    // intervals, preferring a rational one. Z3 also takes is_int, and ignores it.
    pub fn pick_in_complement(
        &mut self,
        am: &mut AlgebraicManager,
        set: Option<&IntervalSet>,
        is_randomized: bool,
    ) -> Result<Anum, SmtError> {
        let Some(set) = set else {
            return Ok(Anum::new(Rational::zero()));
        };
        let zero = Anum::new(Rational::zero());
        let mut is_zero_available = true;
        for interval in &set.intervals {
            let sign = compare_interval_with_zero(am, interval, &zero)?;
            if sign == 0 {
                is_zero_available = false;
                break;
            }
            if sign > 0 {
                break;
            }
        }
        if is_zero_available {
            return Ok(zero);
        }
        let intervals = &set.intervals;
        let last = &intervals[intervals.len() - 1];
        let mut count: u32 = 0;
        let mut picked: Option<Anum> = None;
        if let Some(upper) = &last.upper {
            count += 1;
            let value = am.int_gt(upper)?;
            if !is_randomized {
                return Ok(value);
            }
            picked = Some(value);
        }
        if let Some(lower) = &intervals[0].lower {
            count += 1;
            let value = am.int_lt(lower)?;
            if !is_randomized {
                return Ok(value);
            }
            picked = Some(value);
        }
        for index in 1..intervals.len() {
            let previous_upper = get_bound(&intervals[index - 1].upper)?;
            let lower = get_bound(&intervals[index].lower)?;
            if am.compare(previous_upper, lower)? < 0 {
                count += 1;
                // Without randomizing, this is the first pick (count 1), returned at once.
                if count == 1 || self.rand.next().is_multiple_of(count) {
                    let value = am.select(previous_upper, lower)?;
                    if !is_randomized {
                        return Ok(value);
                    }
                    picked = Some(value);
                }
            }
        }
        if let Some(picked) = picked {
            return Ok(picked);
        }
        let mut irrational: Option<&Anum> = None;
        for index in 1..intervals.len() {
            let upper = get_bound(&intervals[index - 1].upper)?;
            if intervals[index - 1].is_upper_open && intervals[index].is_lower_open {
                if am.is_rational(upper)? {
                    return Ok(am.copy(upper));
                }
                irrational.get_or_insert(upper);
            }
        }
        let irrational = irrational.ok_or_else(|| {
            SmtError::Invariant("the complement of the interval set is empty".to_string())
        })?;
        Ok(am.copy(irrational))
    }

    // pick_max_in_complement: the largest number of the complement, or a number just below it.
    pub fn pick_max_in_complement(
        &self,
        am: &mut AlgebraicManager,
        set: Option<&IntervalSet>,
    ) -> Result<Option<Anum>, SmtError> {
        let (Some(index), Some(set)) = (find_complement_sup(am, set)?, set) else {
            return Ok(None);
        };
        let current = &set.intervals[index];
        if current.is_lower_open {
            return Ok(Some(am.copy(get_bound(&current.lower)?)));
        }
        if index == 0 {
            return Ok(Some(am.int_lt(get_bound(&current.lower)?)?));
        }
        Ok(Some(am.select(
            get_bound(&set.intervals[index - 1].upper)?,
            get_bound(&current.lower)?,
        )?))
    }

    // query_max_in_complement: the supremum of the complement, and whether it belongs to it.
    pub fn query_max_in_complement(
        &self,
        am: &mut AlgebraicManager,
        set: Option<&IntervalSet>,
    ) -> Result<Option<ComplementMax>, SmtError> {
        let (Some(index), Some(set)) = (find_complement_sup(am, set)?, set) else {
            return Ok(None);
        };
        let current = &set.intervals[index];
        Ok(Some(ComplementMax {
            sup: am.copy(get_bound(&current.lower)?),
            is_attained: current.is_lower_open,
        }))
    }
}
