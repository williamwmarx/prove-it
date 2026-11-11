//! `-dump dot`: the state graph TLC's `DotStateWriter` writes, from the states and the steps the
//! search hands over.

use std::collections::HashMap;

use tla_engine::search::DumpedSteps;
use tla_ir::Ir;
use tla_values::print::{is_printable_normalized, write_value};
use tla_values::{Id, Store};

use crate::trace::format_texts;

const UNNAMED_ACTION: &str = "UnnamedAction";

// The Graphviz color scheme of the edges' colors.
const COLOR_SCHEME: &str = "paired12";

/// The options TLC reads from the format of `-dump dot,...`: each is in it where its name is, in
/// any case (TLC.java).
#[derive(Clone, Copy, Debug)]
pub(crate) struct DotOptions {
    pub is_colorized: bool,
    pub is_action_labelled: bool,
    pub is_snapshot: bool,
    pub is_strict: bool,
}

impl DotOptions {
    pub(crate) fn parse(format: &str) -> Result<DotOptions, &'static str> {
        let format = format.to_lowercase();
        // TLC writes a step to a state the constraints exclude, and each step an action's guard
        // excludes, with the predicate that excluded it.
        if format.contains("constrained") {
            return Err("-dump dot,constrained");
        }
        // `stuttering` changes nothing here: TLC writes a stuttering step only where it checks
        // temporal properties, which the binary declines, since TLC then writes the behavior graph
        // to a file of its own too.
        Ok(DotOptions {
            is_colorized: format.contains("colorize"),
            is_action_labelled: format.contains("actionlabels"),
            is_snapshot: format.contains("snapshot"),
            is_strict: format.contains("strict"),
        })
    }

    /// What TLC writes as it opens the file, before it reads the configuration.
    pub(crate) fn header(&self) -> String {
        let colors = if self.is_colorized {
            format!("edge [colorscheme=\"{COLOR_SCHEME}\"]\n")
        } else {
            String::new()
        };
        format!(
            "strict digraph DiskGraph {{\nnode [shape=box,style=rounded]\n{colors}nodesep=0.35;\nsubgraph cluster_graph {{\ncolor=\"white\";\n"
        )
    }
}

/// The name of the file TLC copies the graph to after each state it writes (`snapshot`).
pub(crate) fn get_snapshot_path(path: &str) -> String {
    path.replace(".dot", "_snapshot.dot")
}

/// Writes what TLC writes after the header, as it writes each state and step and then closes the
/// file, in parts to `send`.
pub(crate) fn write_graph(
    ir: &Ir,
    options: DotOptions,
    store: &Store,
    states: &[Id],
    dumped: &DumpedSteps<'_>,
    send: &mut dyn FnMut(String),
) -> Result<(), &'static str> {
    let width = ir.variables.len();
    let count = dumped.fingerprints.len();
    // TLC finds no state of a spec without variables.
    if (width == 0 && count > 0) || states.len() != count * width || dumped.parents.len() != count {
        return Err("-dump dot of states other than the variables' values");
    }
    if dumped
        .steps
        .iter()
        .any(|step| step.from as usize >= count || step.to as usize >= count)
    {
        return Err("-dump dot of a step to a state the search didn't keep");
    }
    // Where TLC has one action, each step is its.
    let is_labelled = dumped.is_labelled || ir.model.actions.len() == 1;
    if (options.is_colorized || options.is_action_labelled) && !is_labelled {
        return Err("-dump dot by action, where the engine doesn't take TLC's actions apart");
    }
    let mut levels: Vec<u32> = Vec::with_capacity(count);
    for &parent in dumped.parents {
        levels.push(if parent < 0 {
            1
        } else {
            levels[parent as usize] + 1
        });
    }
    let mut writer = Writer {
        ir,
        options,
        store,
        states,
        fingerprints: dumped.fingerprints,
        levels,
        ranks: JavaHashSet::default(),
        rank_nodes: HashMap::new(),
        colors: JavaHashSet::default(),
        color_ids: HashMap::new(),
        strict: std::collections::HashSet::new(),
        text: String::new(),
        send,
    };
    let initial_count = dumped
        .parents
        .iter()
        .take_while(|&&parent| parent < 0)
        .count();
    for index in 0..initial_count {
        let label = writer.get_label(index)?;
        let fingerprint = writer.get_fingerprint(index);
        writer.push(&format!(
            "{fingerprint} [label=\"{label}\",style = filled]\n"
        ));
        writer.rank(index)?;
    }
    // The search finds the states in order, each in the first step to it.
    let mut found = initial_count;
    for step in dumped.steps {
        let (from, to) = (step.from as usize, step.to as usize);
        let is_new = to == found;
        found += usize::from(is_new);
        if !writer.is_written(from, to) {
            continue;
        }
        let (color, signature) = writer.get_edge(step.action)?;
        let (source, target) = (writer.get_fingerprint(from), writer.get_fingerprint(to));
        writer.push(&format!(
            "{source} -> {target} [label=\"{signature}\",color=\"{color}\",fontcolor=\"{color}\"];\n"
        ));
        if is_new {
            let label = writer.get_label(to)?;
            writer.push(&format!(
                "{target} [label=\"{label}\",tooltip=\"{label}\"];\n"
            ));
        }
        writer.rank(from)?;
    }
    writer.close()
}

struct Writer<'a, 's> {
    ir: &'a Ir,
    options: DotOptions,
    store: &'a Store,
    states: &'a [Id],
    fingerprints: &'a [u64],
    levels: Vec<u32>,
    // `rankToNodes`: the levels, and the fingerprints of each level's states, in the order TLC's
    // HashMap and HashSets iterate them. TLC adds a level with `computeIfAbsent`.
    ranks: JavaHashSet<u32>,
    rank_nodes: HashMap<u32, JavaHashSet<u64>>,
    // `actionToColors`: the actions' names, and the color of each.
    colors: JavaHashSet<String>,
    color_ids: HashMap<String, u32>,
    // Under `strict`, the xor of the fingerprints of each step's states.
    strict: std::collections::HashSet<u64>,
    text: String,
    send: &'s mut dyn FnMut(String),
}

// How much text the writer holds before it sends it.
const PART_BYTES: usize = 1 << 20;

impl Writer<'_, '_> {
    fn push(&mut self, text: &str) {
        self.text.push_str(text);
        if self.text.len() >= PART_BYTES {
            (self.send)(std::mem::take(&mut self.text));
        }
    }

    fn get_fingerprint(&self, index: usize) -> i64 {
        self.fingerprints[index] as i64
    }

    // Whether TLC writes a step: under `strict`, not where it wrote one whose states' fingerprints
    // have the same xor.
    fn is_written(&mut self, from: usize, to: usize) -> bool {
        !self.options.is_strict
            || self
                .strict
                .insert(self.fingerprints[from] ^ self.fingerprints[to])
    }

    // `maintainRanks`.
    fn rank(&mut self, index: usize) -> Result<(), &'static str> {
        let level = self.levels[index];
        self.ranks.compute_if_absent(level as i32, level)?;
        let fingerprint = self.fingerprints[index];
        self.rank_nodes
            .entry(level)
            .or_default()
            .insert((fingerprint ^ (fingerprint >> 32)) as i32, fingerprint)?;
        Ok(())
    }

    // `states2dot`: the state as TLC prints it, escaped.
    fn get_label(&self, index: usize) -> Result<String, &'static str> {
        let width = self.ir.variables.len();
        let texts = self.states[index * width..(index + 1) * width]
            .iter()
            .map(|&id| {
                let mut text = Vec::new();
                // TLC fingerprints a state, which normalizes it, before it writes it.
                is_printable_normalized(self.store, id)
                    .then(|| write_value(self.store, id, &mut text).ok())
                    .flatten()
                    .and_then(|()| String::from_utf16(&text).ok())
            })
            .collect::<Option<Vec<_>>>()
            .ok_or("dumping a value whose text depends on how TLC built it")?;
        Ok(escape(&format_texts(self.ir, &texts)).replace('\n', "\\n"))
    }

    // `dotTransitionLabel`: the step's color, and its action's signature where TLC labels steps.
    fn get_edge(&mut self, position: u32) -> Result<(String, String), &'static str> {
        let action = self.ir.model.actions.get(position as usize);
        let color = if self.options.is_colorized {
            let action = action.ok_or("-dump dot of a step of an action the IR lacks")?;
            let name = get_action_name(self.ir, action)?.to_string();
            let next = self.color_ids.len() as u32 + 2;
            let color = *self.color_ids.entry(name.clone()).or_insert(next);
            self.colors.insert(get_string_hash(&name), name)?;
            color.to_string()
        } else {
            "black".to_string()
        };
        let signature = match action {
            Some(action) if self.options.is_action_labelled => {
                escape(&get_signature(self.ir, action)?)
            }
            _ => String::new(),
        };
        Ok((color, signature))
    }

    fn close(mut self) -> Result<(), &'static str> {
        let mut text = String::new();
        for level in self.ranks.iter() {
            text.push_str("{rank = same; ");
            for fingerprint in self.rank_nodes[level].iter() {
                text.push_str(&format!("{};", *fingerprint as i64));
            }
            text.push_str("}\n");
        }
        text.push_str("}\n");
        if self.options.is_colorized && self.color_ids.len() > 1 {
            text.push_str(&format!(
                "subgraph cluster_legend {{graph[style=bold];label = \"Next State Actions\" style=\"solid\"\nnode [ labeljust=\"l\",colorscheme=\"{COLOR_SCHEME}\",style=filled,shape=record ]\n"
            ));
            for name in self.colors.iter() {
                text.push_str(&format!(
                    "{} [label=\"{name}\",fillcolor={}]\n",
                    name.replace('!', ":"),
                    self.color_ids[name]
                ));
            }
            text.push('}');
        }
        text.push('}');
        self.push(&text);
        let rest = std::mem::take(&mut self.text);
        (self.send)(rest);
        Ok(())
    }
}

// `Action.getInvocationSignature`: the action's name and the values of its parameters, which its
// label holds before its location.
fn get_signature(ir: &Ir, action: &tla_ir::Action) -> Result<String, &'static str> {
    let name = get_action_name(ir, action)?;
    let label = &ir.texts[action.label as usize];
    // TLC labels an action of no operator `Action`, and gives it no parameters.
    if name == UNNAMED_ACTION {
        return Ok(name.to_string());
    }
    // TLC keys an action's parameters by name (`Action.getParameters`), so a parameterised
    // INSTANCE's parameter and the operator's own of the same name are one.
    if name.contains('!') && label[name.len()..].starts_with('(') {
        return Err("-dump dot of an instance's action with parameters");
    }
    // TLC writes an operator its action takes as an argument (`<Operator P1>`), which the label
    // leaves out.
    let definition = action
        .definition
        .map(|index| &ir.nodes.arena[ir.definitions[index as usize] as usize].kind);
    if let Some(tla_ir::NodeKind::Definition(tla_ir::Definition {
        form: tla_ir::DefinitionForm::Operator(params),
        ..
    })) = definition
        && params.iter().any(|param| param.arity > 0)
    {
        return Err("-dump dot of an action that takes an operator");
    }
    let parameters = label
        .strip_prefix(name)
        .and_then(|rest| {
            let to = rest.rfind(" to line ")?;
            Some(&rest[..rest[..to].rfind(" line ")?])
        })
        .ok_or("-dump dot of an action whose label TLC writes otherwise")?;
    Ok(format!("{name}{parameters}"))
}

// `Action.getName`. The front end renames the definitions of a module an INSTANCE in a LET copies,
// which TLC names after the instance.
fn get_action_name<'a>(ir: &'a Ir, action: &tla_ir::Action) -> Result<&'a str, &'static str> {
    let name = &*ir.texts[action.name as usize];
    if !name
        .chars()
        .all(|character| character.is_ascii_alphanumeric() || character == '_' || character == '!')
    {
        return Err("-dump dot by action, of an action whose name the front end renamed");
    }
    Ok(name)
}

// Java's `replace("\\", "\\\\").replace("\"", "\\\"").trim()`.
fn escape(text: &str) -> String {
    text.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .trim_matches(|character| character <= ' ')
        .to_string()
}

// Java's `String.hashCode`, over the UTF-16 code units.
fn get_string_hash(text: &str) -> i32 {
    text.encode_utf16().fold(0i32, |hash, unit| {
        hash.wrapping_mul(31).wrapping_add(i32::from(unit))
    })
}

// Java's HashSet, as far as the order it iterates its elements in: a table of buckets that doubles
// past three quarters full, each bucket in the order its elements were added. A bucket of more than
// eight in a table of 64 or more TLC turns into a tree, whose order this doesn't follow.
struct JavaHashSet<T> {
    buckets: Vec<Vec<(u32, T)>>,
    len: usize,
}

impl<T> Default for JavaHashSet<T> {
    fn default() -> JavaHashSet<T> {
        JavaHashSet {
            buckets: Vec::new(),
            len: 0,
        }
    }
}

const TREEIFY_THRESHOLD: usize = 8;
const TREEIFIED: &str = "-dump dot of a graph whose ranks TLC orders as a tree";
const MINIMUM_TREEIFY_CAPACITY: usize = 64;

impl<T: PartialEq> JavaHashSet<T> {
    fn insert(&mut self, hash: i32, element: T) -> Result<(), &'static str> {
        let hash = (hash ^ ((hash as u32) >> 16) as i32) as u32;
        if self.buckets.is_empty() {
            self.resize();
        }
        let capacity = self.buckets.len();
        let bucket = &mut self.buckets[hash as usize & (capacity - 1)];
        if bucket
            .iter()
            .any(|(stored, value)| *stored == hash && *value == element)
        {
            return Ok(());
        }
        bucket.push((hash, element));
        if bucket.len() > TREEIFY_THRESHOLD {
            if capacity >= MINIMUM_TREEIFY_CAPACITY {
                return Err(TREEIFIED);
            }
            self.resize();
        }
        self.len += 1;
        if self.len > self.buckets.len() / 4 * 3 {
            self.resize();
        }
        Ok(())
    }

    // `HashMap.computeIfAbsent`, which grows a table past three quarters full as it is next called,
    // adds an element first in its bucket, and turns a bucket of more than seven into a tree.
    fn compute_if_absent(&mut self, hash: i32, element: T) -> Result<(), &'static str> {
        let hash = (hash ^ ((hash as u32) >> 16) as i32) as u32;
        if self.buckets.is_empty() || self.len > self.buckets.len() / 4 * 3 {
            self.resize();
        }
        let capacity = self.buckets.len();
        let bucket = &mut self.buckets[hash as usize & (capacity - 1)];
        if bucket
            .iter()
            .any(|(stored, value)| *stored == hash && *value == element)
        {
            return Ok(());
        }
        bucket.insert(0, (hash, element));
        if bucket.len() >= TREEIFY_THRESHOLD {
            if capacity >= MINIMUM_TREEIFY_CAPACITY {
                return Err(TREEIFIED);
            }
            self.resize();
        }
        self.len += 1;
        Ok(())
    }

    fn resize(&mut self) {
        let capacity = (self.buckets.len() * 2).max(16);
        let old = std::mem::replace(
            &mut self.buckets,
            (0..capacity).map(|_| Vec::new()).collect(),
        );
        for (hash, element) in old.into_iter().flatten() {
            self.buckets[hash as usize & (capacity - 1)].push((hash, element));
        }
    }

    fn iter(&self) -> impl Iterator<Item = &T> {
        self.buckets.iter().flatten().map(|(_, element)| element)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn iterates_as_java_hash_sets() {
        // new HashSet<>(List.of(...)) iterated in Java, for values that collide past the first
        // table and grow it.
        let mut set = JavaHashSet::default();
        for value in [17, 1, 33, 2, 49, 16, 0] {
            set.insert(value, value).expect("a list");
        }
        assert_eq!(
            set.iter().copied().collect::<Vec<_>>(),
            [16, 0, 17, 1, 33, 49, 2]
        );
    }

    #[test]
    fn iterates_as_java_hash_maps_computing_their_keys() {
        // computeIfAbsent of each key in a HashMap in Java: the thirteenth key, first in its
        // bucket, leaves the table to grow at the next call.
        let mut set = JavaHashSet::default();
        for key in (1..=12).chain([18]) {
            set.compute_if_absent(key, key).expect("a key");
        }
        let keys: Vec<i32> = set.iter().copied().collect();
        assert_eq!(keys, [1, 18, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]);
        set.compute_if_absent(1, 1).expect("a key");
        let keys: Vec<i32> = set.iter().copied().collect();
        assert_eq!(keys, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 18]);
    }

    #[test]
    fn hashes_strings_as_java() {
        assert_eq!(get_string_hash("Next"), 2424595);
        assert_eq!(get_string_hash(""), 0);
    }
}
