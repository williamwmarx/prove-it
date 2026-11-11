//! The differential of `scripts/nlsat-differential.ts`: random small problems, each decided under
//! a step budget and checked at random rational points by the TypeScript solver, the oracle. The
//! port must make the same search: the same verdict, model, core, steps and statistics, and the
//! same lemmas. The script's header describes the problems' text.

use super::algebraic::Anum;
use super::polynomial::Var;
use super::solver::NlsatSolver;
use super::test_util::{
    parse_polynomial, parse_rational, read_fixture, show_anum, show_polynomial,
};
use super::types::{Atom, IneqKind, RootKind};
use super::{L_FALSE, L_TRUE, LBool, SmtError};

fn get_line<'input>(input: &'input str, name: &str) -> &'input str {
    input
        .split('\n')
        .find_map(|line| line.strip_prefix(name)?.strip_prefix(' '))
        .unwrap_or_else(|| panic!("a {name} line"))
}

fn show_error(error: &SmtError) -> String {
    match error {
        SmtError::Canceled => "error SmtCanceledError".to_string(),
        SmtError::Invariant(message) => format!("error SmtInvariantError: {message}"),
        SmtError::NlsatUnsupported(message) => {
            format!("error NlsatUnsupportedError: nlsat does not implement {message}")
        }
        other => format!("error {other:?}"),
    }
}

fn show_result(result: LBool) -> &'static str {
    if result == L_TRUE {
        "sat"
    } else if result == L_FALSE {
        "unsat"
    } else {
        "undef"
    }
}

fn show_atom(solver: &NlsatSolver, atom: Option<&Atom>) -> String {
    match atom {
        None => "none".to_string(),
        Some(Atom::Root(root)) => {
            let kind = match root.kind {
                RootKind::RootEq => "ROOT_EQ",
                RootKind::RootLt => "ROOT_LT",
                RootKind::RootGt => "ROOT_GT",
                RootKind::RootLe => "ROOT_LE",
                RootKind::RootGe => "ROOT_GE",
            };
            format!(
                "{kind} x{} #{} {}",
                root.max_var.get(),
                root.index,
                show_polynomial(&solver.pm, &root.polynomial)
            )
        }
        Some(Atom::Ineq(ineq)) => {
            let kind = match ineq.kind {
                IneqKind::Eq => "EQ",
                IneqKind::Lt => "LT",
                IneqKind::Gt => "GT",
            };
            let factors: Vec<String> = ineq
                .polynomials
                .iter()
                .zip(&ineq.is_even)
                .map(|(polynomial, &is_even)| {
                    format!(
                        "{}{}",
                        if is_even { "e" } else { "o" },
                        show_polynomial(&solver.pm, polynomial)
                    )
                })
                .collect();
            format!("{kind} {}", factors.join(" "))
        }
    }
}

// The solver of a problem's text, with its atoms and clauses, and the literal of each atom.
fn mk_solver(input: &str, budget: Option<u64>) -> (NlsatSolver, Vec<u32>) {
    let mut solver = NlsatSolver::new(budget);
    let mut literals: Vec<u32> = Vec::new();
    for line in input.split('\n') {
        let words: Vec<&str> = line.split(' ').collect();
        if words[0] == "int" {
            for flag in &words[1..] {
                solver.mk_var(*flag == "1");
            }
        }
        if words[0] == "a" {
            let rest = words[2..].join(" ");
            let factors: Vec<&str> = rest.split(" | ").collect();
            let polynomials: Vec<_> = factors
                .iter()
                .map(|factor| parse_polynomial(&mut solver.pm, &factor[2..]))
                .collect();
            let is_even: Vec<bool> = factors
                .iter()
                .map(|factor| factor.starts_with('e'))
                .collect();
            let kind = match words[1] {
                "EQ" => IneqKind::Eq,
                "LT" => IneqKind::Lt,
                _ => IneqKind::Gt,
            };
            literals.push(solver.mk_ineq_literal(kind, &polynomials, &is_even));
        }
        if words[0] != "cl" {
            continue;
        }
        let clause: Vec<u32> = words[2..]
            .iter()
            .map(|word| {
                let reference: i64 = word.parse().expect("a reference");
                if reference > 0 {
                    literals[(reference - 1) as usize]
                } else {
                    literals[(-reference - 1) as usize] ^ 1
                }
            })
            .collect();
        let assumption = (words[1] != "-1").then(|| words[1].parse().expect("an assumption"));
        solver.mk_external_clause(&clause, assumption);
    }
    (solver, literals)
}

fn run_check(input: &str) -> Vec<String> {
    let (mut solver, literals) = mk_solver(
        input,
        Some(get_line(input, "budget").parse().expect("a budget")),
    );
    let conflicts = get_line(input, "conflicts");
    if conflicts != "none" {
        solver.max_conflicts = Some(conflicts.parse().expect("max conflicts"));
    }
    let shown: Vec<String> = literals.iter().map(ToString::to_string).collect();
    let mut output = vec![format!("literals {}", shown.join(" "))];
    match solver.check(None) {
        Ok(result) => {
            output.push(format!("check {}", show_result(result)));
            if result == L_TRUE {
                let count: Var = get_line(input, "vars").parse().expect("a count");
                let mut model = String::new();
                for variable in 0..count {
                    let value = solver.get_value(variable);
                    model.push_str(&show_anum(&mut solver.am, &value));
                }
                output.push(format!("model{model}"));
            }
            if result == L_FALSE {
                let core: String = solver
                    .get_core()
                    .iter()
                    .map(|assumption| format!(" {assumption}"))
                    .collect();
                output.push(format!("core{core}"));
            }
        }
        Err(error) => output.push(format!("check {}", show_error(&error))),
    }
    let stats = &solver.stats;
    output.push(format!(
        "steps {} conflicts={} restarts={} propagations={} decisions={} stages={} \
         irrational_assignments={}",
        solver.steps,
        stats.conflicts,
        stats.restarts,
        stats.propagations,
        stats.decisions,
        stats.stages,
        stats.irrational_assignments
    ));
    output
}

// check_assignment at each point in turn, on one solver of the problem, until one fails.
fn run_check_assignment(input: &str) -> Vec<String> {
    let mut solver = mk_solver(input, None).0;
    let mut output = Vec::new();
    for line in input.split('\n').filter(|line| line.starts_with("point ")) {
        let values: Vec<Option<Anum>> = line
            .split(' ')
            .skip(1)
            .map(|text| (text != "_").then(|| Anum::new(parse_rational(text))))
            .collect();
        match solver.check_assignment(&values, None) {
            Ok((result, clause)) if result == L_FALSE => {
                let literals: String = clause
                    .iter()
                    .map(|&literal| {
                        let atom = solver.get_atom(literal);
                        format!(
                            " {literal} {}{}",
                            if literal & 1 == 1 { "!" } else { "+" },
                            show_atom(&solver, atom.as_deref())
                        )
                    })
                    .collect();
                output.push(format!("{line}: lemma{literals}"));
            }
            Ok((result, _clause)) => output.push(format!("{line}: {}", show_result(result))),
            Err(error) => {
                output.push(format!("{line}: {}", show_error(&error)));
                break;
            }
        }
    }
    output
}

fn run(input: &str) -> String {
    let mut output = run_check(input);
    output.extend(run_check_assignment(input));
    output.join("\n")
}

#[test]
fn searches_as_the_typescript_does() {
    let cases = read_fixture("differential.json");
    let failures: Vec<String> = cases
        .iter()
        .filter_map(|(input, expected)| {
            let actual = run(input);
            (actual != *expected)
                .then(|| format!("input:\n{input}\nexpected:\n{expected}\nactual:\n{actual}\n"))
        })
        .collect();
    assert!(
        failures.is_empty(),
        "{} of {} differ:\n{}",
        failures.len(),
        cases.len(),
        failures.join("\n")
    );
}
