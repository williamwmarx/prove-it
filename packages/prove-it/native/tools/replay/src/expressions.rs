//! `replay expressions <ir> <state log> [states]`: compiles the roots of a model's engine IR, its
//! invariants, properties, constraints, action constraints, initial predicates and VIEW, and
//! evaluates each on the first states of a log, writing one line per root, then one per state and
//! root: TLC's fingerprint of the value, or why it stopped. `scripts/native-expressions.ts` writes
//! the same lines with the TypeScript engine's compiler and compares them, as they stream.

use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Write};

use tla_engine::compile::{DISTINCT_SLOT, LEVEL_SLOT, NEXT_LEVEL_SLOT};
use tla_engine::{CompileError, Compiled, Compiler, Machine, Options, Root, UNASSIGNED};
use tla_ir::{ConfigName, Ir};
use tla_values::fingerprint::Fingerprints;
use tla_values::transfer::decode_states;
use tla_values::{Id, Store};

use crate::get_encoded;
use crate::json::{Json, parse};

struct Entry {
    label: String,
    is_action: bool,
    compiled: Result<Compiled, String>,
}

fn config_root(ir: &Ir, kind: &str, name: &ConfigName) -> (String, Result<Root, String>) {
    let text = &ir.texts[name.name as usize];
    let root = name
        .definition
        .map(Root::Definition)
        .ok_or_else(|| format!("bail the {kind} {text} isn't defined"));
    (format!("{kind} {text}"), root)
}

fn describe(error: CompileError) -> String {
    match error {
        CompileError::Bail(reason) => format!("bail {reason}"),
        CompileError::Decline(reason) => format!("declined {reason}"),
    }
}

pub fn replay(arguments: &[String]) -> Result<String, String> {
    let [ir_path, log_path, rest @ ..] = arguments else {
        return Err("usage: replay expressions <ir> <state log> [states]".into());
    };
    let limit: usize = match rest.first() {
        Some(text) => text
            .parse()
            .map_err(|_| format!("a count of states {text}"))?,
        None => 1000,
    };
    let bytes = std::fs::read(ir_path).map_err(|error| format!("{ir_path}: {error}"))?;
    let ir = tla_ir::decode(&bytes).map_err(|error| format!("{ir_path}: {error:?}"))?;
    let ranked: Vec<Vec<u16>> = ir.texts[..ir.ranked_count as usize]
        .iter()
        .map(|text| text.encode_utf16().collect())
        .collect();
    let mut store = Store::new();
    store.reset(ranked.iter().map(Vec::as_slice));
    let environment = |name: &str| std::env::var(name).ok();
    let options = Options {
        is_memo_off: environment("PROVE_IT_MEMO").as_deref() == Some("off"),
        is_epoch_checked: environment("PROVE_IT_EPOCH_CHECK").as_deref() == Some("1"),
        ..Options::default()
    };
    let model = &ir.model;
    let mut roots: Vec<(String, bool, Result<Root, String>)> = Vec::new();
    for invariant in &model.invariants {
        let (label, root) = config_root(&ir, "invariant", &invariant.root);
        roots.push((label, false, root));
    }
    for (index, property) in model.property_invariants.iter().enumerate() {
        roots.push((
            format!("property {index}"),
            false,
            Ok(Root::Expression(property.root)),
        ));
    }
    for constraint in &model.constraints {
        let (label, root) = config_root(&ir, "constraint", constraint);
        roots.push((label, false, root));
    }
    for constraint in &model.action_constraints {
        let (label, root) = config_root(&ir, "action constraint", constraint);
        roots.push((label, true, root));
    }
    for (index, property) in model.action_properties.iter().enumerate() {
        roots.push((
            format!("action property {index}"),
            true,
            Ok(Root::Expression(property.action)),
        ));
        roots.push((
            format!("action property {index} subscript"),
            true,
            Ok(Root::Unchanged(property.subscript)),
        ));
    }
    for (index, &predicate) in model.initial_predicates.iter().enumerate() {
        roots.push((
            format!("initial predicate {index}"),
            false,
            Ok(Root::Expression(predicate)),
        ));
    }
    if let Some(view) = &model.view {
        let (label, root) = config_root(&ir, "view", view);
        roots.push((label, false, root));
    }
    let mut compiler = Compiler::new(&ir, &mut store, options);
    let entries: Vec<Entry> = roots
        .into_iter()
        .map(|(label, is_action, root)| Entry {
            label,
            is_action,
            compiled: root.and_then(|root| compiler.compile_root(root).map_err(describe)),
        })
        .collect();
    let program = compiler.finish();
    let mut out = BufWriter::new(std::io::stdout().lock());
    let write_error = |error: std::io::Error| error.to_string();
    for (index, entry) in entries.iter().enumerate() {
        let result = match &entry.compiled {
            Ok(_) => "ok",
            Err(reason) => reason,
        };
        writeln!(out, "root {index} {}: {result}", entry.label).map_err(write_error)?;
    }
    let width = ir.variables.len();
    let mut machine = Machine::new(&program, store);
    let mut fingerprints = Fingerprints::new();
    let mut states: Vec<Id> = Vec::new();
    let mut levels: Vec<i64> = Vec::new();
    let unassigned = vec![UNASSIGNED; width];
    let mut count = 0usize;
    let mut evaluations = 0u64;
    let file = File::open(log_path).map_err(|error| format!("{log_path}: {error}"))?;
    // The header, then only as many states as are evaluated.
    let lines = BufReader::with_capacity(1 << 20, file)
        .lines()
        .skip(1)
        .take(limit);
    let mut evaluate_line = |line: &str| -> Result<(), String> {
        if line.is_empty() {
            return Ok(());
        }
        let record: Json = parse(line)?;
        let fields = record.as_array().ok_or("not a state")?;
        let encoded = get_encoded(fields.get(4), fields.get(5))?;
        let state = decode_states(&mut machine.store, &encoded, width)
            .map_err(|error| format!("{error:?}"))?;
        let parent = fields.get(1).and_then(Json::as_number).ok_or("no parent")? as i64;
        let level = if parent < 0 {
            1
        } else {
            levels[parent as usize] + 1
        };
        states.extend_from_slice(&state);
        levels.push(level);
        let distinct = machine
            .store
            .int(count as i64 + 1)
            .map_err(|bail| bail.0.to_string())?;
        for (root, entry) in entries.iter().enumerate() {
            let Ok(compiled) = &entry.compiled else {
                continue;
            };
            let value = if entry.is_action {
                if parent < 0 {
                    writeln!(out, "{count} {root} -").map_err(write_error)?;
                    continue;
                }
                let parent = parent as usize;
                let from = states[parent * width..(parent + 1) * width].to_vec();
                let epoch = machine.next_epoch();
                machine.set_current(&from, epoch);
                machine.set_next(&state);
                set_levels(&mut machine, levels[parent], distinct)?;
                machine.evaluate(compiled.eval())
            } else {
                let epoch = machine.next_epoch();
                machine.set_current(&state, epoch);
                machine.set_next(&unassigned);
                set_levels(&mut machine, level, distinct)?;
                machine.evaluate(compiled.eval())
            };
            evaluations += 1;
            match value {
                Ok(id) => {
                    let fingerprint = fingerprints.get_state(&machine.store, &[id], &[0]);
                    writeln!(out, "{count} {root} fp {fingerprint:016x}").map_err(write_error)?
                }
                Err(bail) => {
                    writeln!(out, "{count} {root} bail {}", bail.0).map_err(write_error)?
                }
            }
        }
        count += 1;
        Ok(())
    };
    let result = lines
        .map(|line| line.map_err(|error| format!("{log_path}: {error}")))
        .try_for_each(|line| evaluate_line(&line?));
    out.flush().map_err(write_error)?;
    result?;
    Ok(format!(
        "{log_path}: evaluated {evaluations} expressions on {count} states"
    ))
}

fn set_levels(machine: &mut Machine<'_>, level: i64, distinct: Id) -> Result<(), String> {
    let current = machine
        .store
        .int(level)
        .map_err(|bail| bail.0.to_string())?;
    let next = machine
        .store
        .int(level + 1)
        .map_err(|bail| bail.0.to_string())?;
    machine.set_slot(LEVEL_SLOT, current);
    machine.set_slot(NEXT_LEVEL_SLOT, next);
    machine.set_slot(DISTINCT_SLOT, distinct);
    Ok(())
}
