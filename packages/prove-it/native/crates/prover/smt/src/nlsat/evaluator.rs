// Ported from Z3 (src/nlsat/nlsat_evaluator.cpp), MIT license, see z3-license.txt. Evaluates atoms
// at the assignment, and computes the intervals of the maximal variable of an atom that falsify a
// literal at the values of the variables below it. The assignment is the solver's, shared and
// refined in place.
//
// The evaluator holds neither the managers nor the assignment: its methods take them, the
// assignment as the solver's `(Anum | undefined)[]`.
use super::algebraic::{AlgebraicManager, Anum};
use super::atoms::AtomTable;
use super::interval_set::{IntervalSet, IntervalSetManager};
use super::polynomial::{Polynomial, PolynomialManager, Var};
use super::types::{Atom, AtomKind, ClauseRef, IneqAtom, IneqKind, RootAtom, RootKind};
use super::{L_FALSE, L_TRUE, L_UNDEF, LBool, SmtError};

// Z3's LINEAR_SEARCH_THRESHOLD.
const LINEAR_SEARCH_THRESHOLD: usize = 8;

struct Section {
    root: Anum,
    position: usize,
}

struct PolynomialInfo {
    root_count: usize,
    first_section: usize,
    first_sign: usize,
}

// sign_table: the roots of the factors of an atom merged into one sorted list of sections. Cell 2i
// is the sector below sorted section i, cell 2i + 1 the section itself.
#[derive(Default)]
struct SignTable {
    sections: Vec<Section>,
    sorted_sections: Vec<usize>,
    polynomial_sections: Vec<usize>,
    polynomial_signs: Vec<i32>,
    infos: Vec<PolynomialInfo>,
}

impl SignTable {
    fn mk_section(&mut self, am: &mut AlgebraicManager, root: &Anum, position: usize) -> usize {
        self.sections.push(Section {
            root: am.copy(root),
            position,
        });
        self.sections.len() - 1
    }

    fn merge(&mut self, am: &mut AlgebraicManager, roots: &[Anum]) -> Result<Vec<usize>, SmtError> {
        let mut section_ids: Vec<usize> = Vec::new();
        let mut sorted: Vec<usize> = Vec::new();
        let mut sorted_index = 0;
        let mut root_index = 0;
        while sorted_index < self.sorted_sections.len() && root_index < roots.len() {
            let section_id = self.sorted_sections[sorted_index];
            let sign = am.compare(&self.sections[section_id].root, &roots[root_index])?;
            if sign <= 0 {
                sorted.push(section_id);
                if sign == 0 {
                    section_ids.push(section_id);
                    root_index += 1;
                }
                self.sections[section_id].position = sorted.len() - 1;
                sorted_index += 1;
            } else {
                let id = self.mk_section(am, &roots[root_index], sorted.len());
                sorted.push(id);
                section_ids.push(id);
                root_index += 1;
            }
        }
        while sorted_index < self.sorted_sections.len() {
            self.sections[self.sorted_sections[sorted_index]].position = sorted.len();
            sorted.push(self.sorted_sections[sorted_index]);
            sorted_index += 1;
        }
        while root_index < roots.len() {
            let id = self.mk_section(am, &roots[root_index], sorted.len());
            sorted.push(id);
            section_ids.push(id);
            root_index += 1;
        }
        self.sorted_sections = sorted;
        Ok(section_ids)
    }

    fn add(
        &mut self,
        am: &mut AlgebraicManager,
        roots: &[Anum],
        signs: &[i32],
    ) -> Result<(), SmtError> {
        let section_ids = if roots.is_empty() {
            Vec::new()
        } else {
            self.merge(am, roots)?
        };
        self.infos.push(PolynomialInfo {
            root_count: roots.len(),
            first_section: self.polynomial_sections.len(),
            first_sign: self.polynomial_signs.len(),
        });
        self.polynomial_signs.extend_from_slice(signs);
        self.polynomial_sections.extend(section_ids);
        Ok(())
    }

    fn add_const(&mut self, sign: i32) {
        self.infos.push(PolynomialInfo {
            root_count: 0,
            first_section: self.polynomial_sections.len(),
            first_sign: self.polynomial_signs.len(),
        });
        self.polynomial_signs.push(sign);
    }

    fn cell_count(&self) -> usize {
        self.sections.len() * 2 + 1
    }

    fn is_section(&self, cell: usize) -> bool {
        cell % 2 == 1
    }

    fn get_root(&self, cell: usize) -> &Anum {
        &self.sections[self.sorted_sections[cell / 2]].root
    }

    fn get_cell_id(&self, info: &PolynomialInfo, index: usize) -> usize {
        self.sections[self.polynomial_sections[info.first_section + index]].position * 2 + 1
    }

    fn get_sign(&self, info: &PolynomialInfo, index: usize) -> i32 {
        self.polynomial_signs[info.first_sign + index]
    }

    // sign_at: the sign of the infoId-th polynomial in the cell.
    fn sign_at(&self, info_id: usize, cell: usize) -> i32 {
        let info = &self.infos[info_id];
        let root_count = info.root_count;
        if root_count < LINEAR_SEARCH_THRESHOLD {
            let mut index = 0;
            while index < root_count {
                let section_cell = self.get_cell_id(info, index);
                if section_cell == cell {
                    return 0;
                }
                if section_cell > cell {
                    break;
                }
                index += 1;
            }
            return self.get_sign(info, index);
        }
        let first_cell = self.get_cell_id(info, 0);
        let last_cell = self.get_cell_id(info, root_count - 1);
        if cell < first_cell {
            return self.get_sign(info, 0);
        }
        if cell == first_cell || cell == last_cell {
            return 0;
        }
        if cell > last_cell {
            return self.get_sign(info, root_count);
        }
        let mut low = 0;
        let mut high = root_count - 1;
        while high != low + 1 {
            let middle = low + (high - low) / 2;
            let middle_cell = self.get_cell_id(info, middle);
            if middle_cell == cell {
                return 0;
            }
            if cell < middle_cell {
                high = middle;
            } else {
                low = middle;
            }
        }
        self.get_sign(info, low + 1)
    }
}

fn is_satisfied(sign: i32, kind: AtomKind, is_neg: bool) -> bool {
    let is_true = (sign == 0
        && matches!(
            kind,
            AtomKind::Ineq(IneqKind::Eq)
                | AtomKind::Root(RootKind::RootEq | RootKind::RootLe | RootKind::RootGe)
        ))
        || (sign < 0
            && matches!(
                kind,
                AtomKind::Ineq(IneqKind::Lt) | AtomKind::Root(RootKind::RootLt | RootKind::RootLe)
            ))
        || (sign > 0
            && matches!(
                kind,
                AtomKind::Ineq(IneqKind::Gt) | AtomKind::Root(RootKind::RootGt | RootKind::RootGe)
            ));
    if is_neg { !is_true } else { is_true }
}

fn get_literal(bool_var: u32, is_neg: bool) -> u32 {
    2 * bool_var + u32::from(is_neg)
}

fn get_values_without(assignment: &[Option<Anum>], variable: Var) -> Vec<Option<Anum>> {
    assignment
        .iter()
        .enumerate()
        .map(|(index, value)| {
            if index as Var == variable {
                None
            } else {
                value.clone()
            }
        })
        .collect()
}

// The TS `assignment[variable]`, undefined out of range.
fn get_assigned(assignment: &[Option<Anum>], variable: Var) -> Option<&Anum> {
    usize::try_from(variable)
        .ok()
        .and_then(|index| assignment.get(index))
        .and_then(Option::as_ref)
}

// The TS `roots[atom.index - 1]`, with the root index from 1.
fn get_indexed_root(roots: &[Anum], index: u32) -> Result<&Anum, SmtError> {
    (index as usize)
        .checked_sub(1)
        .and_then(|position| roots.get(position))
        .ok_or_else(|| SmtError::Invariant(format!("a root atom has root index {index}")))
}

#[derive(Default)]
pub struct Evaluator {
    pub ism: IntervalSetManager,
}

impl Evaluator {
    pub fn new() -> Evaluator {
        Evaluator::default()
    }

    pub fn eval(
        &self,
        pm: &mut PolynomialManager,
        am: &mut AlgebraicManager,
        assignment: &[Option<Anum>],
        atom: &Atom,
        is_neg: bool,
    ) -> Result<bool, SmtError> {
        match atom {
            Atom::Ineq(atom) => self.eval_ineq(pm, am, assignment, atom, is_neg),
            Atom::Root(atom) => self.eval_root(pm, am, assignment, atom, is_neg),
        }
    }

    fn eval_ineq(
        &self,
        pm: &mut PolynomialManager,
        am: &mut AlgebraicManager,
        assignment: &[Option<Anum>],
        atom: &IneqAtom,
        is_neg: bool,
    ) -> Result<bool, SmtError> {
        let mut sign = 1;
        for (index, polynomial) in atom.polynomials.iter().enumerate() {
            let current_sign = am.eval_sign_at(pm, polynomial, assignment)?;
            sign *= if atom.is_even[index] && current_sign < 0 {
                1
            } else {
                current_sign
            };
            if sign == 0 {
                break;
            }
        }
        Ok(is_satisfied(sign, AtomKind::Ineq(atom.kind), is_neg))
    }

    fn eval_root(
        &self,
        pm: &mut PolynomialManager,
        am: &mut AlgebraicManager,
        assignment: &[Option<Anum>],
        atom: &RootAtom,
        is_neg: bool,
    ) -> Result<bool, SmtError> {
        let roots = am.isolate_roots(
            pm,
            &atom.polynomial,
            &get_values_without(assignment, atom.max_var.get()),
        )?;
        if atom.index as usize > roots.len() {
            return Ok(is_neg);
        }
        let value = get_assigned(assignment, atom.max_var.get()).ok_or_else(|| {
            SmtError::Invariant("a root atom's maximal variable is unassigned".to_string())
        })?;
        let sign = am.compare(value, get_indexed_root(&roots, atom.index)?)?;
        Ok(is_satisfied(sign, AtomKind::Root(atom.kind), is_neg))
    }

    pub fn infeasible_intervals(
        &self,
        pm: &mut PolynomialManager,
        am: &mut AlgebraicManager,
        assignment: &[Option<Anum>],
        atom: &Atom,
        is_neg: bool,
        clause: Option<&ClauseRef>,
    ) -> Result<Option<IntervalSet>, SmtError> {
        match atom {
            Atom::Ineq(atom) => {
                self.get_ineq_infeasible_intervals(pm, am, assignment, atom, is_neg, clause)
            }
            Atom::Root(atom) => {
                self.get_root_infeasible_intervals(pm, am, assignment, atom, is_neg, clause)
            }
        }
    }

    fn add_to_table(
        &self,
        pm: &mut PolynomialManager,
        am: &mut AlgebraicManager,
        assignment: &[Option<Anum>],
        polynomial: &Polynomial,
        variable: Var,
        table: &mut SignTable,
    ) -> Result<(), SmtError> {
        if pm.max_var(polynomial) < variable {
            let sign = am.eval_sign_at(pm, polynomial, assignment)?;
            table.add_const(sign);
            return Ok(());
        }
        let signed =
            am.isolate_roots_with_signs(pm, polynomial, &get_values_without(assignment, variable))?;
        table.add(am, &signed.roots, &signed.signs)
    }

    // The maximal runs of cells where the literal is false, as a union of intervals.
    fn get_ineq_infeasible_intervals(
        &self,
        pm: &mut PolynomialManager,
        am: &mut AlgebraicManager,
        assignment: &[Option<Anum>],
        atom: &IneqAtom,
        is_neg: bool,
        clause: Option<&ClauseRef>,
    ) -> Result<Option<IntervalSet>, SmtError> {
        let mut table = SignTable::default();
        for polynomial in &atom.polynomials {
            self.add_to_table(
                pm,
                am,
                assignment,
                polynomial,
                atom.max_var.get(),
                &mut table,
            )?;
        }
        let justification = get_literal(atom.bool_var, is_neg);
        let get_sign = |cell: usize| {
            let mut sign = 1;
            for index in 0..atom.polynomials.len() {
                let current_sign = table.sign_at(index, cell);
                sign *= if atom.is_even[index] && current_sign < 0 {
                    1
                } else {
                    current_sign
                };
                if sign == 0 {
                    break;
                }
            }
            sign
        };
        let mut result: Option<IntervalSet> = None;
        let mut is_previous_sat = true;
        let mut is_previous_open = true;
        let mut previous_root: Option<Anum> = None;
        let cell_count = table.cell_count();
        for cell in 0..cell_count {
            if is_satisfied(get_sign(cell), AtomKind::Ineq(atom.kind), is_neg) {
                if !is_previous_sat {
                    let set = self.ism.mk(
                        am,
                        is_previous_open,
                        previous_root.as_ref(),
                        table.is_section(cell),
                        Some(table.get_root(if table.is_section(cell) {
                            cell
                        } else {
                            cell - 1
                        })),
                        justification,
                        clause.cloned(),
                    );
                    result = self.ism.mk_union(am, result.as_ref(), Some(&set))?;
                    is_previous_sat = true;
                }
                continue;
            }
            if is_previous_sat {
                if cell == 0 {
                    if cell_count == 1 {
                        result = Some(self.ism.mk(
                            am,
                            true,
                            None,
                            true,
                            None,
                            justification,
                            clause.cloned(),
                        ));
                    }
                    is_previous_open = true;
                    previous_root = None;
                } else {
                    is_previous_open = !table.is_section(cell);
                    previous_root = Some(
                        table
                            .get_root(if table.is_section(cell) {
                                cell
                            } else {
                                cell - 1
                            })
                            .clone(),
                    );
                }
                is_previous_sat = false;
            }
            if cell == cell_count - 1 {
                let set = self.ism.mk(
                    am,
                    is_previous_open,
                    previous_root.as_ref(),
                    true,
                    None,
                    justification,
                    clause.cloned(),
                );
                result = self.ism.mk_union(am, result.as_ref(), Some(&set))?;
            }
        }
        Ok(result)
    }

    fn get_root_infeasible_intervals(
        &self,
        pm: &mut PolynomialManager,
        am: &mut AlgebraicManager,
        assignment: &[Option<Anum>],
        atom: &RootAtom,
        is_neg: bool,
        clause: Option<&ClauseRef>,
    ) -> Result<Option<IntervalSet>, SmtError> {
        let justification = get_literal(atom.bool_var, is_neg);
        let roots = am.isolate_roots(
            pm,
            &atom.polynomial,
            &get_values_without(assignment, atom.max_var.get()),
        )?;
        if atom.index as usize > roots.len() {
            return Ok(if is_neg {
                None
            } else {
                Some(
                    self.ism
                        .mk(am, true, None, true, None, justification, clause.cloned()),
                )
            });
        }
        let root = get_indexed_root(&roots, atom.index)?;
        let mk = |am: &mut AlgebraicManager,
                  is_lower_open: bool,
                  lower: Option<&Anum>,
                  is_upper_open: bool,
                  upper: Option<&Anum>| {
            self.ism.mk(
                am,
                is_lower_open,
                lower,
                is_upper_open,
                upper,
                justification,
                clause.cloned(),
            )
        };
        let set = match atom.kind {
            RootKind::RootEq => {
                if is_neg {
                    mk(am, false, Some(root), false, Some(root))
                } else {
                    let below = mk(am, true, None, true, Some(root));
                    let above = mk(am, true, Some(root), true, None);
                    return self.ism.mk_union(am, Some(&below), Some(&above));
                }
            }
            RootKind::RootLt => {
                if is_neg {
                    mk(am, true, None, true, Some(root))
                } else {
                    mk(am, false, Some(root), true, None)
                }
            }
            RootKind::RootGt => {
                if is_neg {
                    mk(am, true, Some(root), true, None)
                } else {
                    mk(am, true, None, false, Some(root))
                }
            }
            RootKind::RootLe => {
                if is_neg {
                    mk(am, true, None, false, Some(root))
                } else {
                    mk(am, true, Some(root), true, None)
                }
            }
            RootKind::RootGe => {
                if is_neg {
                    mk(am, false, Some(root), true, None)
                } else {
                    mk(am, true, None, true, Some(root))
                }
            }
        };
        Ok(Some(set))
    }
}

// The solver's getAssignedValue: the value of the literal's Boolean variable, negated for a
// negative literal.
pub fn get_assigned_value(bvalues: &[LBool], literal: u32) -> LBool {
    let value = bvalues[(literal >> 1) as usize];
    if literal & 1 == 1 { !value } else { value }
}

// The solver's value: the assigned value, else the atom's value once its maximal variable is
// assigned. Explain's getValue is this too.
pub fn get_literal_value(
    evaluator: &Evaluator,
    pm: &mut PolynomialManager,
    am: &mut AlgebraicManager,
    atoms: &AtomTable,
    bvalues: &[LBool],
    assignment: &[Option<Anum>],
    literal: u32,
) -> Result<LBool, SmtError> {
    let assigned = get_assigned_value(bvalues, literal);
    if assigned != L_UNDEF {
        return Ok(assigned);
    }
    let Some(atom) = atoms.get_atom(literal) else {
        return Ok(L_UNDEF);
    };
    if get_assigned(assignment, atom.max_var()).is_none() {
        return Ok(L_UNDEF);
    }
    Ok(
        if evaluator.eval(pm, am, assignment, atom, literal & 1 == 1)? {
            L_TRUE
        } else {
            L_FALSE
        },
    )
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::rc::Rc;

    use super::super::algebraic::{AlgebraicManager, Anum};
    use super::super::interval_set::IntervalSet;
    use super::super::polynomial::PolynomialManager;
    use super::super::test_util::{parse_atom, parse_rational, read_fixture, show_anum};
    use super::super::types::{Atom, Clause};
    use super::super::{Int, Rational, SmtError};
    use super::{Evaluator, get_assigned};

    fn show_flag(is_true: bool) -> String {
        format!(" {}", if is_true { 1 } else { 0 })
    }

    fn set_at<T>(items: &mut Vec<Option<T>>, index: usize, item: Option<T>) {
        if index >= items.len() {
            items.resize_with(index + 1, || None);
        }
        items[index] = item;
    }

    fn get_at<T>(items: &[Option<T>], index: usize) -> Option<&T> {
        items.get(index).and_then(Option::as_ref)
    }

    fn show_set(am: &mut AlgebraicManager, set: Option<&IntervalSet>) -> String {
        let Some(set) = set else {
            return " {}".to_string();
        };
        let intervals: Vec<String> = set
            .intervals
            .iter()
            .map(|interval| {
                format!(
                    " {}{} ,{} {}j{}{}",
                    if interval.is_lower_open { "(" } else { "[" },
                    interval
                        .lower
                        .as_ref()
                        .map_or(" -oo".to_string(), |lower| show_anum(am, lower)),
                    interval
                        .upper
                        .as_ref()
                        .map_or(" +oo".to_string(), |upper| show_anum(am, upper)),
                    if interval.is_upper_open { ")" } else { "]" },
                    interval.justification,
                    if interval.clause.is_none() { "" } else { "c" },
                )
            })
            .collect();
        format!(
            " {{{}{} }}",
            if set.is_full { "full" } else { "part" },
            intervals.join("")
        )
    }

    fn show_assignment(
        am: &mut AlgebraicManager,
        assignment: &[Option<Anum>],
        variable_count: usize,
    ) -> String {
        let values: Vec<String> = (0..variable_count)
            .map(|variable| {
                get_at(assignment, variable).map_or(" _".to_string(), |value| show_anum(am, value))
            })
            .collect();
        format!(" after{}", values.join(""))
    }

    // The harness's ev programs: an assignment of real algebraic numbers, atoms over it, the
    // infeasible intervals of their literals, unions of those, and samples picked outside them.
    // Each line prints the sets with their exact bounds and the assignment its refinements left
    // behind.
    fn run_evaluator_program(program: &str, expected: &str) -> Result<String, SmtError> {
        let mut am = AlgebraicManager::new();
        let mut pm = PolynomialManager::new();
        let mut assignment: Vec<Option<Anum>> = Vec::new();
        let mut evaluator = Evaluator::new();
        let mut registers: Vec<Option<Anum>> = Vec::new();
        let mut sets: Vec<Option<IntervalSet>> = Vec::new();
        let mut atoms: Vec<Atom> = Vec::new();
        let clause = Rc::new(Clause {
            id: 0,
            literals: Vec::new(),
            is_learned: false,
            assumptions: None,
            is_active: Cell::new(false),
        });
        let expected_lines: Vec<&str> = expected.split('\n').collect();
        let mut variable_count = 0;
        let mut lines = Vec::new();
        for (index, line) in program.split('\n').enumerate() {
            let words: Vec<&str> = line.split(' ').collect();
            let number =
                |position: usize| -> usize { words[position + 1].parse().expect("a number") };
            let output = match words[0] {
                "vars" => {
                    variable_count = number(0);
                    String::new()
                }
                "seed" => {
                    evaluator.ism.set_seed(number(0) as u32);
                    String::new()
                }
                "q" => {
                    let anum = Anum::new(parse_rational(words[2]));
                    let output = show_anum(&mut am, &anum);
                    set_at(&mut registers, number(0), Some(anum));
                    output
                }
                "root" => {
                    let mut coeffs: Vec<Int> = words[3..]
                        .iter()
                        .map(|word| word.parse().expect("a coefficient"))
                        .collect();
                    while coeffs.last().is_some_and(Int::is_zero) {
                        coeffs.pop();
                    }
                    let polynomial = pm.from_coeffs(&coeffs, 0);
                    let roots = am.isolate_roots(&mut pm, &polynomial, &[])?;
                    let root = roots[number(1) - 1].clone();
                    let output = show_anum(&mut am, &root);
                    set_at(&mut registers, number(0), Some(root));
                    output
                }
                "set" => {
                    // An unset register, such as 7 when every pick met a full set, is zero.
                    let value = get_at(&registers, number(1))
                        .cloned()
                        .unwrap_or_else(|| Anum::new(Rational::zero()));
                    let copy = am.copy(&value);
                    set_at(&mut assignment, number(0), Some(copy));
                    String::new()
                }
                "ineq" | "rootatom" => {
                    let printed = &expected_lines[index][words[0].len()..];
                    atoms.push(parse_atom(&mut pm, printed));
                    printed.to_string()
                }
                "eval" => {
                    let atom = &atoms[number(0)];
                    if get_assigned(&assignment, atom.max_var()).is_none() {
                        " unassigned".to_string()
                    } else {
                        let is_true =
                            evaluator.eval(&mut pm, &mut am, &assignment, atom, number(1) == 1)?;
                        format!(
                            "{}{}",
                            show_flag(is_true),
                            show_assignment(&mut am, &assignment, variable_count)
                        )
                    }
                }
                "inf" => {
                    let set = evaluator.infeasible_intervals(
                        &mut pm,
                        &mut am,
                        &assignment,
                        &atoms[number(1)],
                        number(2) == 1,
                        if number(3) == 1 { Some(&clause) } else { None },
                    )?;
                    set_at(&mut sets, number(0), set);
                    format!(
                        "{}{}",
                        show_set(&mut am, get_at(&sets, number(0))),
                        show_assignment(&mut am, &assignment, variable_count)
                    )
                }
                "union" => {
                    let union = evaluator.ism.mk_union(
                        &mut am,
                        get_at(&sets, number(1)),
                        get_at(&sets, number(2)),
                    )?;
                    let output = format!(
                        "{}{}{}",
                        show_set(&mut am, union.as_ref()),
                        show_set(&mut am, get_at(&sets, number(1))),
                        show_set(&mut am, get_at(&sets, number(2)))
                    );
                    set_at(&mut sets, number(0), union);
                    output
                }
                "subset" => {
                    let is_subset = evaluator.ism.subset(
                        &mut am,
                        get_at(&sets, number(0)),
                        get_at(&sets, number(1)),
                    )?;
                    format!(
                        "{}{}{}",
                        show_flag(is_subset),
                        show_set(&mut am, get_at(&sets, number(0))),
                        show_set(&mut am, get_at(&sets, number(1)))
                    )
                }
                "full" => show_flag(evaluator.ism.is_full(get_at(&sets, number(0)))),
                "just" => {
                    let justifications = evaluator.ism.get_justifications(get_at(&sets, number(0)));
                    let literals: Vec<String> = justifications
                        .literals
                        .iter()
                        .map(|literal| format!(" {literal}"))
                        .collect();
                    format!(
                        "{} clauses {}",
                        literals.join(""),
                        justifications.clauses.len()
                    )
                }
                "pick" => {
                    let set = get_at(&sets, number(0));
                    if evaluator.ism.is_full(set) {
                        " fullset".to_string()
                    } else {
                        // The picked number goes to register 7, for a later set.
                        let picked =
                            evaluator
                                .ism
                                .pick_in_complement(&mut am, set, number(2) == 1)?;
                        let output =
                            format!("{}{}", show_anum(&mut am, &picked), show_set(&mut am, set));
                        set_at(&mut registers, 7, Some(picked));
                        output
                    }
                }
                "pickmax" => {
                    let max = evaluator
                        .ism
                        .pick_max_in_complement(&mut am, get_at(&sets, number(0)))?;
                    let shown = match max {
                        None => " 0".to_string(),
                        Some(max) => format!(" 1{}", show_anum(&mut am, &max)),
                    };
                    format!("{shown}{}", show_set(&mut am, get_at(&sets, number(0))))
                }
                _ => {
                    let max = evaluator
                        .ism
                        .query_max_in_complement(&mut am, get_at(&sets, number(0)))?;
                    let shown = match max {
                        None => " 0".to_string(),
                        Some(max) => format!(
                            " 1{}{}",
                            show_anum(&mut am, &max.sup),
                            show_flag(max.is_attained)
                        ),
                    };
                    format!("{shown}{}", show_set(&mut am, get_at(&sets, number(0))))
                }
            };
            lines.push(format!("{}{output}", words[0]));
        }
        Ok(lines.join("\n"))
    }

    // Random programs with two or three variables, the top one unassigned until the end, as when
    // nlsat decides it. Unions drop the clauses of the intervals they copy, as Z3's do.
    #[test]
    fn nlsat_evaluator() {
        let mut failures = Vec::new();
        for (program, expected) in read_fixture("evaluator.json") {
            let actual = run_evaluator_program(&program, &expected);
            if actual.as_ref() != Ok(&expected) {
                failures.push(format!(
                    "program:\n{program}\nexpected:\n{expected}\nactual:\n{actual:?}"
                ));
            }
        }
        assert!(failures.is_empty(), "{}", failures.join("\n\n"));
    }
}
