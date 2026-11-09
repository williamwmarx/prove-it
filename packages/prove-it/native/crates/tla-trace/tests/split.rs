//! TLC's actions as the trace evaluator splits the next-state relation, against those `check.ts`
//! wrote into each golden IR of `tests/conformance/ir`: the same labels, expressions and values
//! bound, in the same order. `check.ts` writes none where the next-state relation may print, draw
//! or set a register anywhere, which the split labels as TLC does, so those IRs aren't compared.

use tla_ir::{Index, Ir, ScopeBinding, Value};
use tla_trace::add_actions;

// The golden IRs, or those of every corpus model where PROVE_IT_SPLIT_IRS names the directory
// `engine-ir` writes them to.
fn ir_directory() -> std::path::PathBuf {
    std::env::var_os("PROVE_IT_SPLIT_IRS").map_or_else(
        || std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../tests/conformance/ir"),
        std::path::PathBuf::from,
    )
}

fn golden_irs(directory: &std::path::Path, found: &mut Vec<std::path::PathBuf>) {
    let mut entries: Vec<_> = std::fs::read_dir(directory)
        .expect("the golden IRs")
        .map(|entry| entry.expect("an entry").path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            golden_irs(&path, found);
        } else if path.extension().is_some_and(|extension| extension == "ir") {
            found.push(path);
        }
    }
}

// A value as text, with its strings and model values by name.
fn describe_value(ir: &Ir, value: &Value) -> String {
    let all = |values: &[Value]| {
        values
            .iter()
            .map(|value| describe_value(ir, value))
            .collect::<Vec<_>>()
            .join(",")
    };
    let text = |index: u32| ir.texts[ir.values.strings[index as usize] as usize].to_string();
    match value {
        Value::Bool(value) => value.to_string(),
        Value::Int(value) => value.to_string(),
        Value::String(index) => format!("\"{}\"", text(*index)),
        Value::ModelValue(index) => text(*index),
        Value::Set(elements) => format!("{{{}}}", all(elements)),
        Value::Function {
            class,
            domain,
            range,
        } => format!("{class}[{}|{}]", all(domain), all(range)),
        Value::IntervalFunction { class, low, range } => format!("{class}<{low}|{}>", all(range)),
    }
}

// The values a scope and its parents bind, innermost first.
fn describe_scope(ir: &Ir, mut scope: Option<Index>) -> Vec<String> {
    let mut bound = Vec::new();
    while let Some(index) = scope {
        let entry = &ir.scopes[index as usize];
        if let ScopeBinding::Value(Some(value)) = entry.binding {
            bound.push(format!(
                "{}={}",
                ir.texts[entry.name as usize],
                describe_value(ir, &ir.values.list[value as usize])
            ));
        }
        scope = entry.parent;
    }
    bound
}

fn describe_actions(ir: &Ir) -> Vec<String> {
    ir.model
        .actions
        .iter()
        .map(|action| {
            format!(
                "{} @{} {:?} {} {:?} {:?}",
                ir.texts[action.label as usize],
                action.expression,
                describe_scope(ir, action.scope),
                ir.texts[action.name as usize],
                action.location.map(|range| (
                    ir.texts[range.module as usize].to_string(),
                    range.start_line,
                    range.start_column,
                    range.end_line,
                    range.end_column
                )),
                action
                    .definition
                    .map(|index| ir.definitions[index as usize])
            )
        })
        .collect()
}

#[test]
fn splits_the_next_state_relation_as_tlc_does() {
    let mut paths = Vec::new();
    golden_irs(&ir_directory(), &mut paths);
    let mut mismatches = Vec::new();
    let mut unsupported = Vec::new();
    let mut matched = 0;
    for path in &paths {
        let bytes = std::fs::read(path).expect("a golden IR");
        let ir = tla_ir::decode(&bytes).expect("an IR that decodes");
        if ir.model.is_labelled || ir.model.actions.is_empty() {
            continue;
        }
        let expected = describe_actions(&ir);
        let mut stripped = ir.clone();
        stripped.model.actions.clear();
        let split = tla_values::on_nesting_stack(|| add_actions(&stripped));
        match split {
            Ok(split) => {
                let actual = describe_actions(&split);
                if actual == expected {
                    matched += 1;
                } else {
                    mismatches.push(format!(
                        "{}:\n  expected {expected:?}\n  actual   {actual:?}",
                        path.display()
                    ));
                }
            }
            Err(reason) => unsupported.push(format!("{}: {}", path.display(), reason.0)),
        }
    }
    eprintln!("{matched} match, {} unsupported", unsupported.len());
    for line in &unsupported {
        eprintln!("unsupported {line}");
    }
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n"));
}
