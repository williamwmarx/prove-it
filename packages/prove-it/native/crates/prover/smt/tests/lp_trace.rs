//! Replays the `.lptrace` files that `scripts/lp-trace.ts` records from the TypeScript arithmetic
//! theory (`src/prover/smt/solver/lp-trace.ts` describes the format) against the Rust lp: the same
//! calls in the same order, the callbacks lp makes answered from the trace, and every result,
//! filled-in argument, field read and callback, with its arguments and its place among the calls,
//! checked against the trace.
//!
//! The traces are read from the directory `PROVE_IT_LP_TRACES` names, by default
//! `packages/prove-it/tests/conformance/.lp-traces`; without it the test only says so. A trace that
//! reaches what the Rust lp does not port yet is declined there, which the test reports and
//! allows.

#[path = "lp_trace/json.rs"]
mod json;

use std::cell::{Cell, RefCell};
use std::collections::VecDeque;
use std::fs;
use std::io::{BufRead, BufReader};
use std::panic::{self, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::rc::Rc;

use json::Value;
use prove_num::{Int, Rational};
use prove_smt::lp::bound_propagator::{BoundPropagator, BoundPropagatorHost, ImpliedBound};
use prove_smt::lp::constraints::ConstraintKind;
use prove_smt::lp::dependency::{Dependency, linearize};
use prove_smt::lp::explanation::Explanation;
use prove_smt::lp::int_solver::{IntSolver, Lia, LiaMove};
use prove_smt::lp::lar_solver::LarSolver;
use prove_smt::lp::lar_term::LarTerm;
use prove_smt::lp::numeric_pair::Impq;
use prove_smt::lp::random_updater::random_update;
use prove_smt::util::error::SmtError;

/// Why a trace stopped before its end.
enum Stop {
    Differs {
        line: usize,
        expected: String,
        got: String,
    },
    Declined {
        line: usize,
        reason: String,
    },
    Crash {
        line: usize,
        message: String,
    },
}

/// A callback line of the trace, which the call before it is to make.
struct ExpectedCallback {
    line: usize,
    name: String,
    args: Vec<Value>,
    result: Option<Value>,
    is_throwing: bool,
}

/// The callbacks the current call is to make, which the closures and hosts given to lp answer.
#[derive(Default)]
struct Callbacks {
    queue: RefCell<VecDeque<ExpectedCallback>>,
    call_line: Cell<usize>,
    stop: RefCell<Option<Stop>>,
}

impl Callbacks {
    fn set_stop(&self, stop: Stop) {
        let mut current = self.stop.borrow_mut();
        if current.is_none() {
            *current = Some(stop);
        }
    }

    /// The trace's answer to the callback, which must be the next one queued. After a mismatch it
    /// answers false, and the call's result is not looked at.
    fn answer(&self, name: &str, args: Vec<Value>) -> bool {
        if self.stop.borrow().is_some() {
            return false;
        }
        let got = format!("callback {name}{}", Value::Array(args.clone()));
        let Some(expected) = self.queue.borrow_mut().pop_front() else {
            self.set_stop(Stop::Differs {
                line: self.call_line.get(),
                expected: "no more callbacks".into(),
                got,
            });
            return false;
        };
        if expected.name != name || expected.args != args {
            self.set_stop(Stop::Differs {
                line: expected.line,
                expected: format!("callback {}{}", expected.name, Value::Array(expected.args)),
                got,
            });
            return false;
        }
        if expected.is_throwing {
            self.set_stop(Stop::Declined {
                line: expected.line,
                reason: format!("callback {name} throws"),
            });
            return false;
        }
        expected
            .result
            .and_then(|result| result.as_bool())
            .unwrap_or(false)
    }
}

/// BoundPropagator's host, the theory's columnIsInteresting, boundIsInteresting, isEqual and
/// addEq, answered from the trace.
struct TraceHost {
    callbacks: Rc<Callbacks>,
    name: String,
}

impl TraceHost {
    fn ask(&self, method: &str, args: Vec<Value>) -> bool {
        self.callbacks
            .answer(&format!("{}.{method}", self.name), args)
    }
}

impl BoundPropagatorHost for TraceHost {
    fn column_is_interesting(&mut self, _solver: &LarSolver<'_>, column: usize) -> bool {
        self.ask("columnIsInteresting", vec![get_number(column)])
    }

    fn bound_is_interesting(
        &mut self,
        _solver: &LarSolver<'_>,
        column: usize,
        kind: ConstraintKind,
        value: &Rational,
    ) -> bool {
        self.ask(
            "boundIsInteresting",
            vec![
                get_number(column),
                Value::Number(f64::from(kind)),
                get_rational(value),
            ],
        )
    }

    fn is_equal(&mut self, _solver: &LarSolver<'_>, first: usize, second: usize) -> bool {
        self.ask("isEqual", vec![get_number(first), get_number(second)])
    }

    fn add_eq(
        &mut self,
        _solver: &LarSolver<'_>,
        first: usize,
        second: usize,
        explanation: &Explanation,
        is_fixed: bool,
    ) -> bool {
        self.ask(
            "addEq",
            vec![
                get_number(first),
                get_number(second),
                get_explanation(explanation),
                Value::Bool(is_fixed),
            ],
        )
    }
}

// The trace's encoding of values (lp-trace.ts): -1 for NULL_LPVAR, Rationals as strings, ...

fn get_number(value: usize) -> Value {
    Value::Number(if value == usize::MAX {
        -1.0
    } else {
        value as f64
    })
}

fn get_rational(value: &Rational) -> Value {
    Value::String(value.to_string())
}

fn get_impq(value: &Impq) -> Value {
    Value::Array(vec![get_rational(&value.x), get_rational(&value.y)])
}

fn get_dependency(dep: &Dependency) -> Value {
    match dep {
        None => Value::Null,
        Some(_) => Value::Object(vec![(
            "dep".into(),
            Value::Array(
                linearize(std::slice::from_ref(dep))
                    .into_iter()
                    .map(|leaf| Value::Number(f64::from(leaf)))
                    .collect(),
            ),
        )]),
    }
}

fn get_explanation(explanation: &Explanation) -> Value {
    let mut fields = vec![(
        "expl".into(),
        Value::Array(explanation.iter().map(get_number).collect()),
    )];
    if !explanation.pairs().is_empty() {
        fields.push((
            "pairs".into(),
            Value::Array(
                explanation
                    .pairs()
                    .iter()
                    .map(|pair| Value::Array(vec![get_number(pair.0), get_rational(&pair.1)]))
                    .collect(),
            ),
        ));
    }
    Value::Object(fields)
}

fn get_term(term: &LarTerm) -> Value {
    Value::Object(vec![
        ("col".into(), get_number(term.column)),
        (
            "coeffs".into(),
            Value::Array(
                term.iter()
                    .map(|entry| Value::Array(vec![get_number(entry.0), get_rational(entry.1)]))
                    .collect(),
            ),
        ),
    ])
}

fn get_implied_bound(bound: &ImpliedBound) -> Value {
    Value::Object(vec![
        ("column".into(), get_number(bound.column)),
        ("bound".into(), get_rational(&bound.bound)),
        ("isLower".into(), Value::Bool(bound.is_lower)),
        ("isStrict".into(), Value::Bool(bound.is_strict)),
        (
            "explain".into(),
            Value::Object(vec![("fn".into(), Value::Bool(true))]),
        ),
    ])
}

/// A LiaMove as TypeScript's `{ kind, ... }`.
fn get_lia_move(lia_move: &LiaMove) -> Value {
    let kind = |name: &str| ("kind".to_string(), Value::String(name.into()));
    Value::Object(match lia_move {
        LiaMove::Sat => vec![kind("sat")],
        LiaMove::Undef => vec![kind("undef")],
        LiaMove::Conflict => vec![kind("conflict")],
        LiaMove::Continue => vec![kind("continue")],
        LiaMove::Cut { offset, is_upper } => vec![
            kind("cut"),
            ("offset".into(), get_rational(offset)),
            ("isUpper".into(), Value::Bool(*is_upper)),
        ],
        LiaMove::Branch { is_upper, offset } => vec![
            kind("branch"),
            ("isUpper".into(), Value::Bool(*is_upper)),
            ("offset".into(), get_rational(offset)),
        ],
    })
}

/// The `Name: message` of the TypeScript error an SmtError stands for.
fn get_error(error: &SmtError) -> String {
    match error {
        SmtError::Invariant(message) => format!("SmtInvariantError: {message}"),
        SmtError::Canceled => "SmtCanceledError".into(),
        other => format!("{other:?}"),
    }
}

/// What a call did: its result (None for undefined), its arguments after the call when lp fills
/// one in, or the error it threw.
#[derive(Default)]
struct Outcome {
    result: Option<Value>,
    out: Option<Vec<Value>>,
    error: Option<String>,
}

fn returning(value: Value) -> Outcome {
    Outcome {
        result: Some(value),
        ..Outcome::default()
    }
}

/// The arguments of a call line, read in the trace's encoding.
struct Args<'a> {
    values: &'a [Value],
    line: usize,
}

impl Args<'_> {
    fn bad(&self, index: usize, what: &str) -> Stop {
        Stop::Crash {
            line: self.line,
            message: format!(
                "argument {index} is not {what}: {}",
                self.values.get(index).unwrap_or(&Value::Null)
            ),
        }
    }

    fn get(&self, index: usize) -> Result<&Value, Stop> {
        self.values
            .get(index)
            .ok_or_else(|| self.bad(index, "there"))
    }

    fn index(&self, index: usize) -> Result<usize, Stop> {
        let number = self
            .get(index)?
            .as_f64()
            .ok_or_else(|| self.bad(index, "a number"))?;
        if number == -1.0 {
            return Ok(usize::MAX);
        }
        if number < 0.0 || number.fract() != 0.0 {
            return Err(self.bad(index, "an index"));
        }
        Ok(number as usize)
    }

    fn boolean(&self, index: usize) -> Result<bool, Stop> {
        self.get(index)?
            .as_bool()
            .ok_or_else(|| self.bad(index, "a boolean"))
    }

    fn kind(&self, index: usize) -> Result<ConstraintKind, Stop> {
        let number = self
            .get(index)?
            .as_f64()
            .ok_or_else(|| self.bad(index, "a kind"))?;
        Ok(number as ConstraintKind)
    }

    fn rational(&self, index: usize) -> Result<Rational, Stop> {
        parse_rational(self.get(index)?).ok_or_else(|| self.bad(index, "a rational"))
    }

    fn reference(&self, index: usize) -> Result<&str, Stop> {
        self.get(index)?
            .get("ref")
            .and_then(Value::as_str)
            .ok_or_else(|| self.bad(index, "an lp object"))
    }

    fn callback(&self, index: usize) -> Result<&str, Stop> {
        self.get(index)?
            .get("cb")
            .and_then(Value::as_str)
            .ok_or_else(|| self.bad(index, "a callback"))
    }

    fn indices(&self, index: usize) -> Result<Vec<usize>, Stop> {
        let items = self
            .get(index)?
            .as_array()
            .ok_or_else(|| self.bad(index, "an array"))?;
        let inner = Args {
            values: items,
            line: self.line,
        };
        (0..items.len()).map(|item| inner.index(item)).collect()
    }

    fn coeffs(&self, index: usize) -> Result<Vec<(usize, Rational)>, Stop> {
        let items = self
            .get(index)?
            .as_array()
            .ok_or_else(|| self.bad(index, "an array"))?;
        items
            .iter()
            .map(|item| {
                let pair = Args {
                    values: item.as_array().ok_or_else(|| self.bad(index, "pairs"))?,
                    line: self.line,
                };
                Ok((pair.index(0)?, pair.rational(1)?))
            })
            .collect()
    }

    fn explanation(&self, index: usize) -> Result<Explanation, Stop> {
        let value = self.get(index)?;
        let mut explanation = Explanation::new();
        if let Some(pairs) = value.get("pairs").and_then(Value::as_array) {
            for pair in pairs {
                let pair = Args {
                    values: pair.as_array().ok_or_else(|| self.bad(index, "pairs"))?,
                    line: self.line,
                };
                explanation.add_pair(pair.index(0)?, pair.rational(1)?);
            }
            return Ok(explanation);
        }
        let inner = Args {
            values: value
                .get("expl")
                .and_then(Value::as_array)
                .ok_or_else(|| self.bad(index, "an explanation"))?,
            line: self.line,
        };
        for item in 0..inner.values.len() {
            explanation.push(inner.index(item)?);
        }
        Ok(explanation)
    }
}

fn parse_rational(value: &Value) -> Option<Rational> {
    let text = value.as_str()?;
    let (num, den) = text.split_once('/').unwrap_or((text, "1"));
    Some(Rational::of(
        num.parse::<Int>().ok()?,
        den.parse::<Int>().ok()?,
    ))
}

/// An lp object's name, "lar#0", as its kind and number.
fn parse_name(name: &str) -> Option<(&str, usize)> {
    let (kind, number) = name.split_once('#')?;
    Some((kind, number.parse().ok()?))
}

struct Propagator {
    propagator: BoundPropagator,
    lar: usize,
    host: TraceHost,
}

struct IntegerSolver {
    solver: IntSolver,
    lar: usize,
}

/// The lp objects of a trace, by kind in order of creation, as the trace numbers them.
struct Replay {
    callbacks: Rc<Callbacks>,
    lars: Vec<LarSolver<'static>>,
    bps: Vec<Propagator>,
    lias: Vec<IntegerSolver>,
}

impl Replay {
    fn get_lar_index(&self, name: &str, line: usize) -> Result<usize, Stop> {
        match parse_name(name) {
            Some(("lar", index)) if index < self.lars.len() => Ok(index),
            _ => Err(Stop::Crash {
                line,
                message: format!("{name} is not a LarSolver of the trace"),
            }),
        }
    }

    fn decline(line: usize, owner: &str, method: &str) -> Stop {
        Stop::Declined {
            line,
            reason: format!("{owner}.{method}"),
        }
    }

    fn call(
        &mut self,
        owner: &str,
        method: &str,
        args: &Args<'_>,
        line: usize,
    ) -> Result<Outcome, Stop> {
        if owner == "lp" {
            return self.call_lp(method, args, line);
        }
        let (kind, index) = parse_name(owner).ok_or_else(|| Stop::Crash {
            line,
            message: format!("bad object {owner}"),
        })?;
        if method == "new" {
            return self.make(owner, kind, index, args, line);
        }
        match kind {
            "lar" => self.call_lar(index, method, args, line),
            "bp" => self.call_bp(index, method, args, line),
            "lia" => self.call_lia(index, method, args, line),
            "nla" => self.call_nla(index, method, args, line),
            _ => Err(Replay::decline(line, owner, method)),
        }
    }

    fn make(
        &mut self,
        owner: &str,
        kind: &str,
        index: usize,
        args: &Args<'_>,
        line: usize,
    ) -> Result<Outcome, Stop> {
        let count = match kind {
            "lar" => self.lars.len(),
            "bp" => self.bps.len(),
            "lia" => self.lias.len(),
            _ => return Err(Replay::decline(line, owner, "new")),
        };
        if index != count {
            return Err(Stop::Crash {
                line,
                message: format!("{owner} is made out of order"),
            });
        }
        match kind {
            "lar" => {
                let callbacks = Rc::clone(&self.callbacks);
                let name = args.callback(0)?.to_string();
                self.lars.push(LarSolver::new(Box::new(move || {
                    callbacks.answer(&name, Vec::new())
                })));
            }
            "bp" => {
                let lar = self.get_lar_index(args.reference(0)?, line)?;
                self.bps.push(Propagator {
                    propagator: BoundPropagator::new(),
                    lar,
                    host: TraceHost {
                        callbacks: Rc::clone(&self.callbacks),
                        name: args.callback(1)?.to_string(),
                    },
                });
            }
            _ => {
                let lar = self.get_lar_index(args.reference(0)?, line)?;
                self.lias.push(IntegerSolver {
                    solver: IntSolver::new(&mut self.lars[lar]),
                    lar,
                });
            }
        }
        Ok(Outcome::default())
    }

    // LarSolver's methods, as theory-lra*.ts calls them.
    fn call_lar(
        &mut self,
        index: usize,
        method: &str,
        args: &Args<'_>,
        line: usize,
    ) -> Result<Outcome, Stop> {
        let lar = self.lars.get_mut(index).ok_or_else(|| Stop::Crash {
            line,
            message: format!("no lar#{index}"),
        })?;
        Ok(match method {
            "activate" => {
                lar.activate(args.index(0)?);
                Outcome::default()
            }
            "activateCheckOnEqual" => {
                returning(get_number(lar.activate_check_on_equal(args.index(0)?)))
            }
            "addEquality" => returning(Value::Array(
                lar.add_equality(args.index(0)?, args.index(1)?)
                    .iter()
                    .map(|constraint| get_number(*constraint))
                    .collect(),
            )),
            "addTerm" => returning(get_number(lar.add_term(&args.coeffs(0)?, args.index(1)?))),
            "addVar" => returning(get_number(lar.add_var(args.index(0)?, args.boolean(1)?))),
            "collectMoreRowsForLpPropagation" => {
                lar.collect_more_rows_for_lp_propagation();
                Outcome::default()
            }
            "constraintIsRedundant" => {
                returning(Value::Bool(lar.constraint_is_redundant(args.index(0)?)))
            }
            "externalToLocalColumn" => {
                returning(get_number(lar.external_to_local_column(args.index(0)?)))
            }
            "findFeasibleSolution" => {
                returning(Value::Number(f64::from(lar.find_feasible_solution())))
            }
            "getBound" => Outcome {
                result: lar
                    .get_bound(args.index(0)?, args.boolean(1)?)
                    .map(|bound| {
                        Value::Object(vec![
                            ("dep".into(), get_dependency(&bound.dep)),
                            ("value".into(), get_rational(&bound.value)),
                            ("isStrict".into(), Value::Bool(bound.is_strict)),
                        ])
                    }),
                ..Outcome::default()
            },
            "getExactValue" => Outcome {
                result: lar
                    .get_exact_value(args.index(0)?)
                    .map(|value| get_rational(&value)),
                ..Outcome::default()
            },
            "getExternal" => returning(get_number(lar.get_external(args.index(0)?))),
            "getInfeasibilityExplanation" => {
                let mut explanation = args.explanation(0)?;
                lar.get_infeasibility_explanation(&mut explanation);
                Outcome {
                    out: Some(vec![get_explanation(&explanation)]),
                    ..Outcome::default()
                }
            }
            "getModelValue" => returning(get_rational(&lar.get_model_value(args.index(0)?))),
            "getTerm" => match lar.get_term(args.index(0)?) {
                Ok(term) => returning(get_term(term)),
                Err(error) => Outcome {
                    error: Some(get_error(&error)),
                    ..Outcome::default()
                },
            },
            "getValue" => returning(get_impq(lar.get_value(args.index(0)?))),
            "hasInfInt" => returning(Value::Bool(lar.has_inf_int())),
            "hasTerm" => returning(Value::Bool(lar.has_term(args.index(0)?))),
            "initModel" => returning(Value::Bool(lar.init_model())),
            "isFeasible" => returning(Value::Bool(lar.is_feasible())),
            "isFixed" => returning(Value::Bool(lar.is_fixed(args.index(0)?))),
            "mkVarBound" => returning(get_number(lar.mk_var_bound(
                args.index(0)?,
                args.kind(1)?,
                &args.rational(2)?,
            ))),
            "pop" => {
                lar.pop(args.index(0)?);
                Outcome::default()
            }
            "push" => {
                lar.push();
                Outcome::default()
            }
            "registerExistingTerms" => {
                lar.register_existing_terms();
                Outcome::default()
            }
            _ => return Err(Replay::decline(line, &format!("lar#{index}"), method)),
        })
    }

    // BoundPropagator's methods, and the explain of its implied bounds.
    fn call_bp(
        &mut self,
        index: usize,
        method: &str,
        _args: &Args<'_>,
        line: usize,
    ) -> Result<Outcome, Stop> {
        let propagator = self.bps.get_mut(index).ok_or_else(|| Stop::Crash {
            line,
            message: format!("no bp#{index}"),
        })?;
        let lar = &mut self.lars[propagator.lar];
        if let Some(bound) = get_implied_bound_index(method, "explain") {
            let bound = propagator
                .propagator
                .ibounds
                .get(bound)
                .ok_or_else(|| Stop::Differs {
                    line,
                    expected: format!("an implied bound {bound}"),
                    got: format!("{} implied bounds", propagator.propagator.ibounds.len()),
                })?;
            return Ok(returning(Value::Array(
                bound
                    .explain(lar)
                    .iter()
                    .map(|entry| {
                        Value::Array(vec![get_rational(&entry.0), get_dependency(&entry.1)])
                    })
                    .collect(),
            )));
        }
        Ok(match method {
            "init" => {
                propagator.propagator.init();
                Outcome::default()
            }
            "propagateBoundsForTouchedRows" => {
                propagator
                    .propagator
                    .propagate_bounds_for_touched_rows(lar, &mut propagator.host);
                Outcome::default()
            }
            _ => return Err(Replay::decline(line, &format!("bp#{index}"), method)),
        })
    }

    // IntSolver's check, through the Lia view.
    fn call_lia(
        &mut self,
        index: usize,
        method: &str,
        _args: &Args<'_>,
        line: usize,
    ) -> Result<Outcome, Stop> {
        let integer = self.lias.get_mut(index).ok_or_else(|| Stop::Crash {
            line,
            message: format!("no lia#{index}"),
        })?;
        if method != "check" {
            return Err(Replay::decline(line, &format!("lia#{index}"), method));
        }
        let result = Lia {
            lia: &mut integer.solver,
            lra: &mut self.lars[integer.lar],
        }
        .check();
        Ok(match result {
            Ok(lia_move) => returning(get_lia_move(&lia_move)),
            Err(error) => Outcome {
                error: Some(get_error(&error)),
                ..Outcome::default()
            },
        })
    }

    // TODO(nla): NlaCore through the Nla view once it lands.
    fn call_nla(
        &mut self,
        index: usize,
        method: &str,
        _args: &Args<'_>,
        line: usize,
    ) -> Result<Outcome, Stop> {
        Err(Replay::decline(line, &format!("nla#{index}"), method))
    }

    // lp's free functions.
    fn call_lp(&mut self, method: &str, args: &Args<'_>, line: usize) -> Result<Outcome, Stop> {
        match method {
            "randomUpdate" => {
                let lar = self.get_lar_index(args.reference(0)?, line)?;
                random_update(&mut self.lars[lar], &args.indices(1)?);
                Ok(Outcome::default())
            }
            _ => Err(Replay::decline(line, "lp", method)),
        }
    }

    // A field the theory reads, None for undefined.
    fn read(&self, owner: &str, path: &str, line: usize) -> Result<Option<Value>, Stop> {
        let declined = || Replay::decline(line, owner, path);
        let (kind, index) = parse_name(owner).ok_or_else(declined)?;
        match kind {
            "lar" => {
                let lar = &self.lars[self.get_lar_index(owner, line)?];
                Ok(Some(match path {
                    "status" => Value::Number(f64::from(lar.status)),
                    "columnsWithChangedBounds.size" => {
                        get_number(lar.columns_with_changed_bounds.size())
                    }
                    "constraints.constraints.length" => {
                        get_number(lar.constraints.constraints.len())
                    }
                    _ => return Err(declined()),
                }))
            }
            "lia" => {
                let solver = &self.lias.get(index).ok_or_else(declined)?.solver;
                Ok(Some(match path {
                    "term" => get_term(&solver.term),
                    "explanation" => get_explanation(&solver.explanation),
                    _ => return Err(declined()),
                }))
            }
            "bp" => {
                let ibounds = &self.bps.get(index).ok_or_else(declined)?.propagator.ibounds;
                if path == "ibounds" {
                    return Ok(Some(Value::Array(
                        ibounds.iter().map(get_implied_bound).collect(),
                    )));
                }
                let (bound, field) = path
                    .strip_prefix("ibounds.")
                    .and_then(|rest| rest.split_once('.'))
                    .ok_or_else(declined)?;
                let bound = bound.parse::<usize>().map_err(|_| declined())?;
                let Some(bound) = ibounds.get(bound) else {
                    return Ok(None);
                };
                get_implied_bound(bound)
                    .get(field)
                    .cloned()
                    .map(Some)
                    .ok_or_else(declined)
            }
            _ => Err(declined()),
        }
    }

    // A field the theory writes.
    fn write(&mut self, owner: &str, path: &str, value: &Value, line: usize) -> Result<(), Stop> {
        let lar = self.get_lar_index(owner, line);
        match (lar, path, value.as_bool()) {
            (Ok(lar), "constraints.isAuxiliaryMode", Some(value)) => {
                self.lars[lar].constraints.is_auxiliary_mode = value;
                Ok(())
            }
            _ => Err(Replay::decline(line, owner, path)),
        }
    }

    // One line of the trace that is not a callback, with the callbacks that follow it queued.
    fn step(&mut self, line: &Value, number: usize) -> Result<(), Stop> {
        self.callbacks.call_line.set(number);
        let differs = |expected: Option<&Value>, got: Option<&Value>| Stop::Differs {
            line: number,
            expected: expected.map_or("undefined".into(), Value::to_string),
            got: got.map_or("undefined".into(), Value::to_string),
        };
        if let Some(owner) = line.get("f").and_then(Value::as_str) {
            let path = line.get("p").and_then(Value::as_str).unwrap_or("");
            let got = self.read(owner, path, number)?;
            if got.as_ref() != line.get("r") {
                return Err(differs(line.get("r"), got.as_ref()));
            }
            return Ok(());
        }
        if let Some(owner) = line.get("w").and_then(Value::as_str) {
            let path = line.get("p").and_then(Value::as_str).unwrap_or("");
            return self.write(owner, path, line.get("v").unwrap_or(&Value::Null), number);
        }
        let (Some(owner), Some(method)) = (
            line.get("c").and_then(Value::as_str),
            line.get("m").and_then(Value::as_str),
        ) else {
            return Err(Stop::Crash {
                line: number,
                message: format!("not a trace line: {line}"),
            });
        };
        let args = Args {
            values: line.get("a").and_then(Value::as_array).unwrap_or(&[]),
            line: number,
        };
        let outcome = self.call(owner, method, &args, number)?;
        if let Some(stop) = self.callbacks.stop.borrow_mut().take() {
            return Err(stop);
        }
        if let Some(expected) = self.callbacks.queue.borrow_mut().pop_front() {
            return Err(Stop::Differs {
                line: expected.line,
                expected: format!("callback {}{}", expected.name, Value::Array(expected.args)),
                got: format!("no more callbacks of {owner}.{method}"),
            });
        }
        let expected_error = line.get("e").and_then(Value::as_str);
        if expected_error != outcome.error.as_deref() {
            return Err(Stop::Differs {
                line: number,
                expected: format!("error {expected_error:?}"),
                got: format!("error {:?}", outcome.error),
            });
        }
        if outcome.result.as_ref() != line.get("r") {
            return Err(differs(line.get("r"), outcome.result.as_ref()));
        }
        let got_out = outcome.out.map(Value::Array);
        if got_out.as_ref() != line.get("o") {
            return Err(differs(line.get("o"), got_out.as_ref()));
        }
        Ok(())
    }
}

/// `ibounds.<n>.<method>`'s n.
fn get_implied_bound_index(path: &str, method: &str) -> Option<usize> {
    path.strip_prefix("ibounds.")?
        .strip_suffix(method)?
        .strip_suffix('.')?
        .parse()
        .ok()
}

fn parse_line(text: &str, number: usize) -> Result<Value, Stop> {
    json::parse(text).map_err(|message| Stop::Crash {
        line: number,
        message: format!("bad JSON: {message}"),
    })
}

/// Replays one trace: None when it all matched, with the number of lines.
fn replay(path: &Path, current_line: &Cell<usize>) -> (usize, Option<Stop>) {
    let file = match fs::File::open(path) {
        Ok(file) => file,
        Err(error) => {
            return (
                0,
                Some(Stop::Crash {
                    line: 0,
                    message: error.to_string(),
                }),
            );
        }
    };
    let mut lines = BufReader::new(file)
        .lines()
        .map_while(Result::ok)
        .enumerate()
        .map(|(index, text)| (index + 1, text))
        .filter(|(_, text)| !text.is_empty())
        .peekable();
    let mut replay = Replay {
        callbacks: Rc::new(Callbacks::default()),
        lars: Vec::new(),
        bps: Vec::new(),
        lias: Vec::new(),
    };
    let mut count = 0;
    while let Some((number, text)) = lines.next() {
        count = number;
        current_line.set(number);
        let result = parse_line(&text, number).and_then(|line| {
            let mut queue = replay.callbacks.queue.borrow_mut();
            queue.clear();
            while let Some((callback_number, callback_text)) =
                lines.next_if(|(_, text)| text.starts_with("{\"cb\":"))
            {
                let callback = parse_line(&callback_text, callback_number)?;
                queue.push_back(ExpectedCallback {
                    line: callback_number,
                    name: callback
                        .get("cb")
                        .and_then(Value::as_str)
                        .unwrap_or("")
                        .to_string(),
                    args: callback
                        .get("a")
                        .and_then(Value::as_array)
                        .unwrap_or(&[])
                        .to_vec(),
                    result: callback.get("r").cloned(),
                    is_throwing: callback.get("e").is_some(),
                });
            }
            drop(queue);
            if line.get("cb").is_some() {
                return Err(Stop::Differs {
                    line: number,
                    expected: format!("{line}"),
                    got: "no call before the callback".into(),
                });
            }
            replay.step(&line, number)
        });
        if let Err(stop) = result {
            return (count, Some(stop));
        }
    }
    (count, None)
}

fn get_traces_directory() -> PathBuf {
    std::env::var_os("PROVE_IT_LP_TRACES").map_or_else(
        || Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../../tests/conformance/.lp-traces"),
        PathBuf::from,
    )
}

#[test]
fn lp_traces() {
    let directory = get_traces_directory();
    let Ok(entries) = fs::read_dir(&directory) else {
        println!(
            "no lp traces in {}: record them with `bun scripts/run.ts lp-trace`",
            directory.display()
        );
        return;
    };
    let mut paths: Vec<PathBuf> = entries
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "lptrace")
        })
        .collect();
    paths.sort();
    let mut same = 0;
    let mut differs = 0;
    let mut declined = 0;
    let mut crashes = 0;
    for path in &paths {
        let name = path.file_name().unwrap_or_default().to_string_lossy();
        let current_line = Cell::new(0);
        let outcome = panic::catch_unwind(AssertUnwindSafe(|| replay(path, &current_line)))
            .unwrap_or_else(|payload| {
                let message = payload
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| payload.downcast_ref::<&str>().map(ToString::to_string))
                    .unwrap_or_default();
                (
                    current_line.get(),
                    Some(Stop::Crash {
                        line: current_line.get(),
                        message: format!("panic: {message}"),
                    }),
                )
            });
        match outcome.1 {
            None => {
                same += 1;
                println!("same      {name} ({} lines)", outcome.0);
            }
            Some(Stop::Differs {
                line,
                expected,
                got,
            }) => {
                differs += 1;
                println!("differs   {name}:{line}\n  expected {expected}\n  got      {got}");
            }
            Some(Stop::Declined { line, reason }) => {
                declined += 1;
                println!("declined  {name}:{line} at {reason}");
            }
            Some(Stop::Crash { line, message }) => {
                crashes += 1;
                println!("crash     {name}:{line}: {message}");
            }
        }
    }
    println!(
        "{} lp traces in {}: {same} same, {differs} differ, {declined} declined, {crashes} crashed",
        paths.len(),
        directory.display()
    );
    assert!(
        differs == 0 && crashes == 0,
        "{differs} lp traces differ and {crashes} crashed"
    );
}
