//! TLC's `-dump dot` (`DotStateWriter`): the state graph the model checker hands its writer as it
//! searches, which the search records (`tla_engine::search::DotLog`) and this module words as TLC
//! writes it, with the order of the Java hash maps TLC closes the graph from.

use tla_engine::search::{DotLog, DotWrite};
use tla_ir::{DefinitionForm, Ir, NodeId, NodeKind, Resolution};

/// The options of `-dump dot,...`, which TLC finds anywhere in the word it lowercases
/// (`TLC.handleParameters`).
#[derive(Clone, Copy)]
pub(crate) struct DotOptions {
    pub(crate) colorize: bool,
    pub(crate) action_labels: bool,
    pub(crate) snapshot: bool,
    pub(crate) constrained: bool,
    pub(crate) strict: bool,
}

impl DotOptions {
    pub(crate) fn parse(word: &str) -> DotOptions {
        let word = word.to_lowercase();
        DotOptions {
            colorize: word.contains("colorize"),
            action_labels: word.contains("actionlabels"),
            snapshot: word.contains("snapshot"),
            constrained: word.contains("constrained"),
            strict: word.contains("strict"),
        }
    }

    /// Whether the edges name or color the action that took them, for which the search takes its
    /// steps through TLC's actions.
    pub(crate) fn is_labelled(&self) -> bool {
        self.colorize || self.action_labels
    }
}

/// Why the binary declines a graph whose order it doesn't follow: a bucket of a Java `HashMap`
/// TLC turns into a tree, which it walks in another order than the bucket's list.
const TREE_BIN: &str = "-dump dot whose ranks TLC's HashMap keeps in a tree";

/// A Java `HashMap`, as far as the order it iterates in: its table of buckets, each a list in the
/// order `put` appends to and `computeIfAbsent` prepends to, which a resize splits in order.
struct JavaMap<K, V> {
    buckets: Vec<Vec<(i32, K, V)>>,
    size: usize,
}

impl<K: PartialEq + Clone, V> JavaMap<K, V> {
    fn new() -> JavaMap<K, V> {
        JavaMap {
            buckets: Vec::new(),
            size: 0,
        }
    }

    fn threshold(&self) -> usize {
        self.buckets.len() * 3 / 4
    }

    // `HashMap.hash`: the key's hash with its high half spread into the low one.
    fn index(&self, hash: i32) -> usize {
        let spread = (hash as u32) ^ ((hash as u32) >> 16);
        spread as usize & (self.buckets.len() - 1)
    }

    // `HashMap.resize`: 16 buckets first, then twice as many, each bucket's list split in order.
    fn resize(&mut self) {
        let capacity = if self.buckets.is_empty() {
            16
        } else {
            self.buckets.len() * 2
        };
        let old = std::mem::replace(
            &mut self.buckets,
            (0..capacity).map(|_| Vec::new()).collect(),
        );
        for (hash, key, value) in old.into_iter().flatten() {
            let index = self.index(hash);
            self.buckets[index].push((hash, key, value));
        }
    }

    // `HashMap.putVal` of a key not mapped yet, as `HashSet.add` and `put` reach it: appended to
    // its bucket, which TLC turns into a tree past 8 entries where the table holds 64 buckets,
    // and resizes otherwise.
    fn put(&mut self, hash: i32, key: K, value: V) -> Result<(), &'static str> {
        if self.buckets.is_empty() {
            self.resize();
        }
        let index = self.index(hash);
        if self.buckets[index]
            .iter()
            .any(|(_, other, _)| *other == key)
        {
            return Ok(());
        }
        let count = self.buckets[index].len();
        self.buckets[index].push((hash, key, value));
        if count >= 8 {
            if self.buckets.len() < 64 {
                self.resize();
            } else {
                return Err(TREE_BIN);
            }
        }
        self.size += 1;
        if self.size > self.threshold() {
            self.resize();
        }
        Ok(())
    }

    // `HashMap.computeIfAbsent`: a resize first where the map holds more than its threshold, and a
    // key not mapped yet prepended to its bucket, which TLC turns into a tree past 7 entries where
    // the table holds 64 buckets, and resizes otherwise (`treeifyBin`).
    fn compute_if_absent(
        &mut self,
        hash: i32,
        key: K,
        make: impl FnOnce() -> V,
    ) -> Result<&mut V, &'static str> {
        if self.buckets.is_empty() || self.size > self.threshold() {
            self.resize();
        }
        let index = self.index(hash);
        let probe = key.clone();
        if !self.buckets[index]
            .iter()
            .any(|(_, other, _)| *other == key)
        {
            let count = self.buckets[index].len();
            self.buckets[index].insert(0, (hash, key, make()));
            self.size += 1;
            if count >= 7 {
                if self.buckets.len() >= 64 {
                    return Err(TREE_BIN);
                }
                self.resize();
            }
        }
        let index = self.index(hash);
        let position = self.buckets[index]
            .iter()
            .position(|(_, other, _)| *other == probe)
            .expect("the key just mapped");
        Ok(&mut self.buckets[index][position].2)
    }

    fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.buckets
            .iter()
            .flatten()
            .map(|(_, key, value)| (key, value))
    }
}

fn long_hash(value: i64) -> i32 {
    (value ^ ((value as u64) >> 32) as i64) as i32
}

fn string_hash(text: &str) -> i32 {
    text.encode_utf16().fold(0i32, |hash, unit| {
        hash.wrapping_mul(31)
            .wrapping_add(i32::from(unit as i16) & 0xffff)
    })
}

/// A state's text in the graph (`DotStateWriter.states2dot`): TLC's text of the state with its
/// backslashes and quotes escaped, trimmed, and its line breaks written as `\n`.
fn states2dot(text: &str) -> String {
    text.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .trim()
        .replace('\n', "\\n")
}

/// The graph TLC writes, or why the binary doesn't follow it: `state_text` gives TLC's text of a
/// state (`TLCState.toString`), and `action_names` the name of each of TLC's actions
/// (`Action.getName`), which `-dump dot,actionlabels` writes as the action's signature, the name
/// alone for an action without parameters.
pub(crate) fn format(
    log: &DotLog,
    options: &DotOptions,
    action_names: &[String],
    state_text: &mut dyn FnMut(&[tla_values::Id]) -> Result<String, &'static str>,
) -> Result<String, &'static str> {
    let mut text = String::from("strict digraph DiskGraph {\n");
    text.push_str("node [shape=box,style=rounded]\n");
    if options.colorize {
        text.push_str("edge [colorscheme=\"paired12\"]\n");
    }
    text.push_str("nodesep=0.35;\n");
    text.push_str("subgraph cluster_graph {\n");
    text.push_str("color=\"white\";\n");
    let mut ranks: JavaMap<i32, JavaMap<i64, ()>> = JavaMap::new();
    let mut colors: JavaMap<String, i32> = JavaMap::new();
    let mut color_count = 1;
    let mut strict = std::collections::HashSet::new();
    let maintain_ranks =
        |ranks: &mut JavaMap<i32, JavaMap<i64, ()>>, level: u64, fingerprint: u64| {
            let level = i32::try_from(level).map_err(|_| "-dump dot of a level past 2^31")?;
            let fingerprint = fingerprint as i64;
            ranks.compute_if_absent(level, level, JavaMap::new)?.put(
                long_hash(fingerprint),
                fingerprint,
                (),
            )
        };
    for write in &log.writes {
        match write {
            DotWrite::Initial { fingerprint, state } => {
                text.push_str(&format!(
                    "{} [label=\"{}\",style = filled]\n",
                    *fingerprint as i64,
                    states2dot(&state_text(state)?)
                ));
                maintain_ranks(&mut ranks, 1, *fingerprint)?;
            }
            DotWrite::Step {
                from,
                level,
                to,
                state,
                action,
            } => {
                if options.strict && !strict.insert(from ^ to) {
                    continue;
                }
                let name = match action {
                    Some(action) => action_names
                        .get(*action as usize)
                        .ok_or("-dump dot of a step of no action of TLC's")?
                        .as_str(),
                    None if options.is_labelled() => {
                        return Err("-dump dot of a step the search didn't label");
                    }
                    None => "",
                };
                let color = if options.colorize {
                    let hash = string_hash(name);
                    let known = colors
                        .iter()
                        .find(|(known, _)| known.as_str() == name)
                        .map(|(_, color)| *color);
                    match known {
                        Some(color) => color.to_string(),
                        None => {
                            color_count += 1;
                            colors.put(hash, name.to_owned(), color_count)?;
                            color_count.to_string()
                        }
                    }
                } else {
                    "black".to_owned()
                };
                let label = if options.action_labels {
                    name.replace('\\', "\\\\")
                        .replace('"', "\\\"")
                        .trim()
                        .to_owned()
                } else {
                    String::new()
                };
                text.push_str(&format!(
                    "{} -> {} [label=\"{label}\",color=\"{color}\",fontcolor=\"{color}\"];\n",
                    *from as i64, *to as i64
                ));
                if let Some(state) = state {
                    let state = states2dot(&state_text(state)?);
                    text.push_str(&format!(
                        "{} [label=\"{state}\",tooltip=\"{state}\"];\n",
                        *to as i64
                    ));
                }
                maintain_ranks(&mut ranks, *level, *from)?;
            }
        }
    }
    for (_, nodes) in ranks.iter() {
        text.push_str("{rank = same; ");
        for (fingerprint, ()) in nodes.iter() {
            text.push_str(&format!("{fingerprint};"));
        }
        text.push_str("}\n");
    }
    text.push_str("}\n");
    if options.colorize && colors.size > 1 {
        text.push_str("subgraph cluster_legend {graph[style=bold];label = \"Next State Actions\" style=\"solid\"\n");
        text.push_str(
            "node [ labeljust=\"l\",colorscheme=\"paired12\",style=filled,shape=record ]\n",
        );
        for (name, color) in colors.iter() {
            text.push_str(&format!(
                "{} [label=\"{name}\",fillcolor={color}]\n",
                name.replace('!', ":")
            ));
        }
        text.push('}');
    }
    text.push('}');
    Ok(text)
}

/// Whether TLC's next-state relation, under `-dump dot,constrained`, writes no step to a state
/// it leaves out (`Tool.processUnsatisfied`): one made only of disjunctions and conjunctions of
/// `v' = e`, each conjunction of distinct variables, through definitions without parameters, has
/// no conjunct TLC evaluates false once every variable is assigned.
pub(crate) fn is_free_of_guards(ir: &Ir, node: NodeId) -> bool {
    is_free_of_guards_within(ir, node, 0)
}

fn is_free_of_guards_within(ir: &Ir, node: NodeId, depth: u32) -> bool {
    if depth > 64 {
        return false;
    }
    match &ir.nodes.arena[node as usize].kind {
        NodeKind::Reference(met) => is_free_of_guards_within(ir, *met, depth + 1),
        NodeKind::Or(disjuncts) => disjuncts
            .iter()
            .all(|&disjunct| is_free_of_guards_within(ir, disjunct, depth + 1)),
        NodeKind::And(conjuncts) => {
            let mut assigned = Vec::new();
            conjuncts
                .iter()
                .all(|&conjunct| match get_assigned(ir, conjunct, depth + 1) {
                    Some(variables) => variables.into_iter().all(|variable| {
                        let is_new = !assigned.contains(&variable);
                        assigned.push(variable);
                        is_new
                    }),
                    None => false,
                })
        }
        _ => get_assigned(ir, node, depth + 1).is_some(),
    }
}

// The variables a conjunction's conjunct assigns, where it only assigns them: `v' = e`, or a
// definition without parameters whose body is.
fn get_assigned(ir: &Ir, node: NodeId, depth: u32) -> Option<Vec<u32>> {
    if depth > 64 {
        return None;
    }
    match &ir.nodes.arena[node as usize].kind {
        NodeKind::Reference(met) => get_assigned(ir, *met, depth + 1),
        NodeKind::Apply { name, args }
            if !name.is_local
                && args.len() == 2
                && matches!(name.resolution, Resolution::Builtin(index)
                    if &*ir.texts[ir.builtins[index as usize].name as usize] == "=") =>
        {
            let NodeKind::Prime(primed) = &ir.nodes.arena[args[0] as usize].kind else {
                return None;
            };
            match &ir.nodes.arena[*primed as usize].kind {
                NodeKind::Identifier(variable) if !variable.is_local => match variable.resolution {
                    Resolution::Variable(slot) => Some(vec![slot]),
                    _ => None,
                },
                _ => None,
            }
        }
        NodeKind::Identifier(name) if !name.is_local => match name.resolution {
            Resolution::Definition(index) => {
                let definition = &ir.nodes.arena[ir.definitions[index as usize] as usize];
                let NodeKind::Definition(definition) = &definition.kind else {
                    return None;
                };
                match &definition.form {
                    DefinitionForm::Operator(params) if params.is_empty() => {
                        get_assigned(ir, definition.body, depth + 1)
                    }
                    _ => None,
                }
            }
            _ => None,
        },
        _ => None,
    }
}
