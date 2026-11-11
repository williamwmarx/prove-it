//! TLC's states as it prints them in a violation: rebuilt by `tla-trace` from the initial predicate
//! along the engine's path, so each value prints as TLC built it, and written as `TLCState.toString`
//! (`formatState` in `values.ts`) writes them, a line per variable in TLC's order, as a conjunction
//! when there are several. What the spec printed as TLC rebuilt the trace comes with it.

use tla_engine::machine::Registers as EngineRegisters;
use tla_engine::search::{AcceptedTrace, ContinuedTrace, FinalRegisters, Violation, ViolationKind};
use tla_engine::symmetry::NamedGroup;
use tla_ir::Ir;
use tla_trace::{
    Alias, CounterExample, Ending, PostconditionInputs, Rebuilder, Registers, Stats, Unsupported,
    Value, Verdict, format_value,
};
use tla_values::{Id, Store};

use crate::dump_trace::{DumpedFile, TraceDumps};
use crate::plain::{Variable, to_plain};
use crate::stack::on_search_stack;
use tla_trace::pretty_print;

/// A trace's states as TLC prints them, each with what TLC printed before it, and what it prints
/// after the trace.
pub struct PrintedTrace {
    pub states: Vec<PrintedState>,
    pub trace_output: Vec<String>,
    /// What the postconditions found on the trace, when the caller asked for them.
    pub postconditions: Option<Postconditions>,
    /// The files -dumpTrace's postconditions write, which TLC checks before the configuration's.
    pub dumped: Vec<DumpedFile>,
    /// Under SYMMETRY or a VIEW, the action of a lasso's step back into its cycle, as TLC finds it
    /// from the last state it rebuilt, and the positions of the properties TLC finds the rebuilt
    /// lasso violates.
    pub loop_action: Option<u32>,
    pub violated: Option<Vec<usize>>,
    /// Whether TLC fails to find the violating successor of the initial state again, and so
    /// prints the initial state alone (`Trace::is_successor_lost`).
    pub is_successor_lost: bool,
}

/// What TLCGet reads after the search, for the postconditions.
pub struct PostconditionRun {
    /// Each `_POSSIBLE` predicate's name and count, -1 where TLC evaluated it on none.
    pub possible: Vec<(String, i64)>,
    pub stats: Stats,
}

/// The postconditions TLC checks on a violation's trace: -dumpTrace's first, then, where the
/// caller asks for them, the configuration's with what TLCGet reads.
#[derive(Clone, Copy)]
pub struct TraceChecks<'a> {
    pub dumps: &'a TraceDumps,
    pub run: Option<&'a PostconditionRun>,
}

/// What TLC printed as it evaluated the postconditions, each print as one line, and the first one
/// that doesn't hold, by its position in the model's postconditions, with what TLC found.
pub struct Postconditions {
    pub printed: Vec<String>,
    pub failure: Option<(usize, Verdict)>,
}

pub struct PrintedState {
    /// Each variable's text in TLC's order of the variables, as TLC records the state for its
    /// trace exploration spec, whatever the ALIAS prints.
    pub values: Vec<Option<String>>,
    /// The variables as TLC prints the state, through the ALIAS where the configuration has one.
    pub variables: Vec<Variable>,
    /// The position in the model's actions of the action that took the step to the state, as
    /// TLC finds it.
    pub action: Option<u32>,
    pub output: Vec<String>,
}

/// What a trace is rebuilt from besides its states, as the search left it: a violation's, or one
/// it went on past under -continue.
struct Recorded<'v> {
    store: &'v Store,
    startup: &'v [Id],
    chosen: &'v [(u32, Id)],
    startup_random: u64,
    random: Option<u64>,
    symmetry: Option<&'v NamedGroup>,
    registers: &'v EngineRegisters,
}

impl<'v> From<&'v Violation> for Recorded<'v> {
    fn from(violation: &'v Violation) -> Self {
        Recorded {
            store: &violation.store,
            startup: &violation.startup,
            chosen: &violation.chosen,
            startup_random: violation.startup_random,
            random: violation.random,
            symmetry: violation.symmetry.as_ref(),
            registers: &violation.registers,
        }
    }
}

/// How a rebuilt trace's states are written: with -tool's messages, and with plain data.
#[derive(Clone, Copy)]
pub struct Writing<'a> {
    pub is_tool: bool,
    pub is_plain: bool,
    /// Why a trace printed through the ALIAS declines, where it does.
    pub alias_decline: Option<&'a str>,
}

/// The violation's trace, or why `tla-trace` can't rebuild it. The evaluator recurses with the
/// expressions it evaluates, so it runs on a thread with the search's stack.
pub fn rebuild_trace(
    ir: &Ir,
    violation: &Violation,
    checks: TraceChecks,
    writing: Writing<'_>,
) -> Result<PrintedTrace, String> {
    rebuild(
        ir,
        &violation.into(),
        &violation.kind,
        &violation.states,
        violation.labels.clone(),
        Some(checks),
        writing,
    )
}

/// The trace of the tableau node a deadlocked state reaches, from the deadlock's store.
pub fn rebuild_accepted(
    ir: &Ir,
    violation: &Violation,
    accepted: &AcceptedTrace,
    writing: Writing<'_>,
) -> Result<PrintedTrace, String> {
    rebuild(
        ir,
        &violation.into(),
        &ViolationKind::Accepted {
            violated: accepted.violated.clone(),
        },
        &accepted.states,
        vec![None; accepted.states.len().saturating_sub(1)],
        None,
        writing,
    )
}

/// The trace of a violation the search went on past under -continue, which TLC labels as it
/// rebuilds it.
pub fn rebuild_continued(
    ir: &Ir,
    trace: &ContinuedTrace<'_>,
    kind: &ViolationKind,
    writing: Writing<'_>,
) -> Result<PrintedTrace, String> {
    let recorded = Recorded {
        store: trace.store,
        startup: trace.startup,
        chosen: trace.chosen,
        startup_random: trace.startup_random,
        random: trace.random,
        symmetry: None,
        registers: trace.registers,
    };
    let labels = vec![None; trace.states.len().saturating_sub(1)];
    rebuild(ir, &recorded, kind, &trace.states, labels, None, writing)
}

fn rebuild(
    ir: &Ir,
    recorded: &Recorded<'_>,
    kind: &ViolationKind,
    states: &[Vec<Id>],
    mut labels: Vec<Option<u32>>,
    checks: Option<TraceChecks>,
    writing: Writing<'_>,
) -> Result<PrintedTrace, String> {
    let dumps = checks.map(|checks| checks.dumps);
    let postconditions = checks.and_then(|checks| checks.run);
    on_search_stack(|| {
        let mut states: Vec<&[Id]> = states.iter().map(Vec::as_slice).collect();
        // Under SYMMETRY or a VIEW the lasso's states are the stored ones: TLC rebuilds
        // the states it prints, the step back into the cycle with them, to a state whose
        // key is the stored first state of the cycle's.
        let is_reduced = recorded.symmetry.is_some() || ir.model.view.is_some();
        // TLC names the properties a lasso violates from the states it rebuilt, which are those
        // it prints under SYMMETRY or a VIEW, and whose levels are their positions.
        let reduced_cycle = match *kind {
            ViolationKind::Lasso {
                loop_start,
                is_level_read,
                ..
            } if is_reduced || is_level_read => Some(loop_start),
            _ => None,
        };
        // A step back into the cycle the search didn't label, as under SYMMETRY or a VIEW, is
        // found as TLC finds it, from the last state, unless the cycle ends in its first state,
        // where TLC stutters.
        let closing = match *kind {
            ViolationKind::Lasso {
                loop_start,
                loop_label: None,
                ..
            } if loop_start + 1 < states.len() && states.last() != states.get(loop_start) => {
                Some(loop_start)
            }
            _ => None,
        };
        if let Some(loop_start) = closing {
            states.push(states[loop_start]);
            labels.push(None);
        }
        // TLC holds a violating state as it found it, and recovers a deadlocked one.
        let ending = match *kind {
            ViolationKind::Deadlock { .. } => Ending::Kept,
            ViolationKind::Invariant(_)
            | ViolationKind::ActionProperty(_)
            | ViolationKind::InitialInvariant(_)
            | ViolationKind::InitialPredicate(_) => Ending::Violation,
            ViolationKind::Lasso { .. } | ViolationKind::Accepted { .. } => Ending::Lasso,
            ViolationKind::NoNextState | ViolationKind::Error { .. } => {
                return Err("a stop with no trace".into());
            }
        };
        let cycle_start = match *kind {
            ViolationKind::Lasso { loop_start, .. } => Some(loop_start),
            _ => None,
        };
        // TLC prints each state through the ALIAS, when there is one.
        let rebuilt = Rebuilder::new(ir).and_then(|mut rebuilder| {
            rebuilder.set_startup(recorded.store, recorded.startup, recorded.startup_random)?;
            rebuilder.set_chosen(recorded.store, recorded.chosen);
            if let Some(random) = recorded.random {
                rebuilder.set_violation_random(random);
            }
            if let Some(group) = recorded.symmetry {
                rebuilder.set_symmetry(group);
            }
            // TLC fails as it prints a successor of an invariant violation it didn't find again,
            // having printed the initial state, before any ALIAS or postcondition reads it.
            if matches!(kind, ViolationKind::Invariant(_))
                && ir.model.alias.is_none()
                && postconditions.is_none()
            {
                rebuilder.keep_lost_successor();
            }
            rebuilder.set_registers(Registers::from_store(
                recorded.store,
                &recorded.registers.numbered,
                &recorded.registers.named,
            )?);
            let mut trace = rebuilder.rebuild(recorded.store, &states, &labels, ending)?;
            let loop_action = match closing {
                Some(_) => trace.states.pop().and_then(|state| state.action),
                None => None,
            };
            if closing.is_some() && loop_action.is_none() {
                return Err(Unsupported(
                    "a step back into the cycle the rebuilt lasso lacks".into(),
                ));
            }
            let violated = match reduced_cycle {
                Some(loop_start) => Some(name_violated(&mut rebuilder, ir, &trace, loop_start)?),
                None => None,
            };
            // TLC prints a deadlocked initial state as it is (`TLCTrace.printTrace`).
            let is_alone =
                matches!(kind, ViolationKind::Deadlock { .. }) && trace.states.len() == 1;
            // TLC binds the builtin Trace in the ALIAS to the states up to each it prints, that
            // one included (`TLCTrace.printTrace`), but to none for an initial state and the
            // successor that violates, and in a lasso to those before each state of the path to
            // its cycle (`LiveWorker.printTrace`). For a violating initial state, the Java method
            // gives the state alone (`TLCExt.getTrace`).
            let length = trace.states.len();
            let prefixes: Option<Vec<usize>> = match *kind {
                ViolationKind::Invariant(_) | ViolationKind::ActionProperty(_) if length == 2 => {
                    Some(vec![0; 2])
                }
                ViolationKind::Deadlock { .. }
                | ViolationKind::Invariant(_)
                | ViolationKind::ActionProperty(_)
                | ViolationKind::InitialInvariant(_)
                | ViolationKind::InitialPredicate(_) => Some((1..=length).collect()),
                ViolationKind::Lasso { loop_start, .. } => Some(
                    (0..length)
                        .map(|position| position + usize::from(position >= loop_start))
                        .collect(),
                ),
                _ => None,
            };
            // TLC computes again, as it prints each state, a name the IR holds the value of.
            if let Some(reason) = writing
                .alias_decline
                .filter(|_| !is_alone || postconditions.is_some())
            {
                return Err(Unsupported(reason.to_owned()));
            }
            let aliases = if is_alone {
                None
            } else {
                rebuilder.alias(&trace, cycle_start, prefixes.as_deref(), writing.is_tool)?
            };
            // CounterExample closes a lasso with its step back into the cycle. TLC's record of a
            // stuttering lasso, one whose cycle ends in its first state, closes it by the action
            // of its last step, as `getStepAction` gives it.
            let cycle = match *kind {
                ViolationKind::Lasso {
                    loop_start,
                    loop_label,
                    ..
                } => {
                    // The rebuilt step back into the cycle closes a lasso that doesn't.
                    let is_stuttering = closing.is_none()
                        && (loop_start + 1 == trace.states.len()
                            || states.last() == states.get(loop_start));
                    if is_stuttering {
                        trace.states.last().and_then(|state| state.action)
                    } else {
                        loop_label.or(loop_action)
                    }
                    .map(|label| (loop_start, Some(label)))
                    // TLC holds no action for a lasso that stutters at its initial
                    // state, whose TLCStateInfo it rebuilt from the initial predicate.
                    .or_else(|| (loop_start == 0 && trace.states.len() == 1).then_some((0, None)))
                }
                _ => None,
            };
            // TLC holds an invariant's violation for the postconditions as it found it, the
            // trace before it rebuilt again (`Worker.doPostCondition`).
            let dumped = match dumps.filter(|dumps| !dumps.is_empty()) {
                Some(dumps) => {
                    let held = match kind {
                        ViolationKind::Invariant(_)
                        | ViolationKind::ActionProperty(_)
                        | ViolationKind::InitialInvariant(_)
                        | ViolationKind::InitialPredicate(_) => Some(
                            rebuilder.rebuild_counter_example(recorded.store, &states, &labels)?,
                        ),
                        _ => None,
                    };
                    let counter_example = CounterExample {
                        trace: held.as_ref().unwrap_or(&trace),
                        cycle,
                    };
                    dumps.dump(ir, &mut rebuilder, &counter_example)?
                }
                None => Vec::new(),
            };
            let checked = postconditions
                .map(|run| {
                    check(
                        &mut rebuilder,
                        ir,
                        run,
                        Some(CounterExample {
                            trace: &trace,
                            cycle,
                        }),
                    )
                })
                .transpose()?;
            Ok((trace, aliases, checked, dumped, loop_action, violated))
        });
        rebuilt
            .map(
                |(trace, aliases, postconditions, dumped, loop_action, violated)| PrintedTrace {
                    postconditions,
                    dumped,
                    loop_action,
                    violated,
                    is_successor_lost: trace.is_successor_lost,
                    states: trace
                        .states
                        .iter()
                        .enumerate()
                        .map(|(position, state)| PrintedState {
                            variables: match aliases.as_ref().map(|aliases| &aliases[position]) {
                                Some(Alias::Record(fields)) => get_field_variables(
                                    fields
                                        .iter()
                                        .map(|(name, value)| (name.as_str(), Some(value))),
                                    writing.is_plain,
                                ),
                                _ => get_state_variables(ir, &state.values, writing.is_plain),
                            },
                            values: state_values(
                                ir,
                                &state.values.iter().map(Some).collect::<Vec<_>>(),
                            ),
                            action: state.action,
                            output: state
                                .printed
                                .iter()
                                .map(|print| format_print(print))
                                .collect(),
                        })
                        .collect(),
                    trace_output: trace
                        .trace_output
                        .iter()
                        .map(|print| format_print(print))
                        .collect(),
                },
            )
            .map_err(|Unsupported(reason)| reason)
    })
}

// The properties a rebuilt lasso violates, as TLC's `Liveness.findViolatedProperties` finds them:
// each evaluated on the lasso's states, with the cycle from `loop_start`.
fn name_violated(
    rebuilder: &mut Rebuilder<'_>,
    ir: &Ir,
    trace: &tla_trace::Trace,
    loop_start: usize,
) -> Result<Vec<usize>, Unsupported> {
    let properties: Vec<Vec<tla_live::Term>> = ir
        .model
        .live_properties
        .iter()
        .map(|property| property.formula.iter().map(|&term| to_term(term)).collect())
        .collect();
    let property_terms: Vec<&[tla_live::Term]> = properties.iter().map(Vec::as_slice).collect();
    let mut failure = None;
    let violated = tla_live::violated_on_lasso(
        &property_terms,
        trace.states.len(),
        loop_start,
        &mut |term, position, next| {
            let atom = match term {
                tla_live::Term::State(atom)
                | tla_live::Term::Enabled(atom)
                | tla_live::Term::Action { atom, .. } => atom,
                _ => return Err(tla_live::Declined::from("a term that isn't an atom")),
            };
            let states = &trace.states;
            // TLC rebuilt each state as a successor of the one before, so at its position's
            // level, and the cycle's step back reaches the state at the cycle's start.
            rebuilder
                .answer_atom(
                    atom,
                    (&states[position].values, position as i32 + 1),
                    (&states[next].values, next as i32 + 1),
                )
                .map_err(|Unsupported(reason)| {
                    failure = Some(reason);
                    tla_live::Declined::from("an atom the rebuilder can't answer")
                })
        },
    );
    violated.map_err(|declined| Unsupported(failure.unwrap_or(declined.0)))
}

fn to_term(term: tla_ir::LiveTerm) -> tla_live::Term {
    use tla_ir::LiveTerm;
    use tla_live::Term;
    match term {
        LiveTerm::Boolean(value) => Term::Boolean(value),
        LiveTerm::State(atom) => Term::State(atom),
        LiveTerm::Enabled(atom) => Term::Enabled(atom),
        LiveTerm::Action { atom, enabled } => Term::Action { atom, enabled },
        LiveTerm::Not => Term::Not,
        LiveTerm::Always => Term::Always,
        LiveTerm::Eventually => Term::Eventually,
        LiveTerm::Next => Term::Next,
        LiveTerm::And(count) => Term::And(count),
        LiveTerm::Or(count) => Term::Or(count),
    }
}

/// The postconditions of a search that completed, as TLC checks them, or why `tla-trace` can't.
pub fn check_postconditions(
    ir: &Ir,
    run: &PostconditionRun,
    registers: Option<&FinalRegisters>,
) -> Result<Postconditions, String> {
    on_search_stack(|| {
        Rebuilder::new(ir)
            .and_then(|mut rebuilder| {
                if let Some(stored) = registers {
                    rebuilder.set_registers(Registers::from_store(
                        &stored.store,
                        &stored.registers.numbered,
                        &stored.registers.named,
                    )?);
                }
                check(&mut rebuilder, ir, run, None)
            })
            .map_err(|Unsupported(reason)| reason)
    })
}

// Each postcondition in turn, up to the first that doesn't hold.
pub(crate) fn check(
    rebuilder: &mut Rebuilder<'_>,
    ir: &Ir,
    run: &PostconditionRun,
    counter_example: Option<CounterExample<'_>>,
) -> Result<Postconditions, Unsupported> {
    let mut printed = Vec::new();
    for index in 0..ir.model.postconditions.len() {
        let inputs = PostconditionInputs {
            possible: &run.possible,
            stats: run.stats,
            counter_example: counter_example.as_ref().map(|example| CounterExample {
                trace: example.trace,
                cycle: example.cycle,
            }),
        };
        let checked = rebuilder.postcondition(index, &inputs)?;
        printed.extend(checked.printed.iter().map(|print| format_print(print)));
        if checked.verdict != Verdict::Holds {
            return Ok(Postconditions {
                printed,
                failure: Some((index, checked.verdict)),
            });
        }
    }
    Ok(Postconditions {
        printed,
        failure: None,
    })
}

fn pretty(text: &str) -> String {
    pretty_print(&text.encode_utf16().collect::<Vec<_>>())
}

// What one Print or PrintT printed: each value pretty printed, two spaces apart.
pub(crate) fn format_print(texts: &[String]) -> String {
    texts
        .iter()
        .map(|text| pretty(text))
        .collect::<Vec<_>>()
        .join("  ")
}

/// A state's values, in the engine's order of the variables, as TLC prints the state, with their
/// plain data where `is_plain`.
pub(crate) fn get_state_variables(ir: &Ir, values: &[Value], is_plain: bool) -> Vec<Variable> {
    get_partial_variables(ir, &values.iter().map(Some).collect::<Vec<_>>(), is_plain)
}

/// A state's variables' texts in TLC's order of the variables, `None` for one unassigned.
pub(crate) fn state_values(ir: &Ir, values: &[Option<&Value>]) -> Vec<Option<String>> {
    ir.tlc_order
        .iter()
        .map(|&position| values[position as usize].map(format_value))
        .collect()
}

/// A state some of whose variables are unassigned, which TLC prints as null.
pub(crate) fn get_partial_variables(
    ir: &Ir,
    values: &[Option<&Value>],
    is_plain: bool,
) -> Vec<Variable> {
    get_field_variables(
        ir.tlc_order.iter().map(|&position| {
            (
                ir.texts[ir.variables[position as usize] as usize].as_ref(),
                values[position as usize],
            )
        }),
        is_plain,
    )
}

/// A state whose values are the texts TLC prints for them, in the IR's order of the variables.
pub(crate) fn format_texts(ir: &Ir, texts: &[String]) -> String {
    let is_conjunction = ir.tlc_order.len() > 1;
    let mut text = String::new();
    for &position in &ir.tlc_order {
        let conjunct = if is_conjunction { "/\\ " } else { "" };
        let name = &ir.texts[ir.variables[position as usize] as usize];
        text.push_str(&format!(
            "{conjunct}{name} = {}\n",
            pretty(&texts[position as usize])
        ));
    }
    text
}

/// Named values as TLC prints them in a state, null where unassigned, and their plain data, which
/// only the library's check asks for: else `null`, which nothing reads.
pub(crate) fn get_field_variables<'v>(
    fields: impl Iterator<Item = (&'v str, Option<&'v Value>)>,
    is_plain: bool,
) -> Vec<Variable> {
    fields
        .map(|(name, value)| Variable {
            name: name.to_string(),
            text: value.map_or_else(|| "null".to_string(), |value| pretty(&format_value(value))),
            data: value
                .filter(|_| is_plain)
                .map_or_else(|| "null".to_string(), to_plain),
        })
        .collect()
}

/// A state as TLC prints it (`TLCStateMut.toString`): a line per variable, as a conjunction when
/// there are several.
pub(crate) fn format_variables(variables: &[Variable]) -> String {
    let conjunct = if variables.len() > 1 { "/\\ " } else { "" };
    variables
        .iter()
        .map(|variable| format!("{conjunct}{} = {}\n", variable.name, variable.text))
        .collect()
}
