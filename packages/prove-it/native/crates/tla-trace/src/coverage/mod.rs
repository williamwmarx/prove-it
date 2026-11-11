//! TLC's coverage report (`-coverage`): how often TLC evaluated each expression of each action,
//! invariant and constraint, and how many distinct values each variable took (native/design
//! coverage notes in trace.md). The engine's compiled search memoizes and fuses expressions, so
//! its counts aren't TLC's: this pass runs TLC's breadth-first search again at one worker, with
//! a port of TLC's `Tool` ([`tool`]) over SANY's view of the IR ([`sem`]) that counts into TLC's
//! cost model ([`model`]) as TLC does, and prints the report as `CostModelCreator.report` does.
//! Where the port can't be sure of TLC's counts it declines.

mod hll;
mod model;
mod sem;
mod tool;

use std::collections::{HashMap, HashSet, VecDeque};

use tla_ir::{Index, NodeKind, Resolution, SourceRange};
use tla_values::fingerprint::{Fingerprints, Polynomial};

use self::model::{Cm, Creator, Model, Place, Printer, Relation, Root, describe, place};
use self::sem::{Code, DefId, Op, SId, SKind, Sem};
use self::tool::{Action, Ctx, Halt, St, Tool, no};
use crate::fingerprint::state_fingerprint;
use crate::rebuild::Rebuilder;
use crate::value::Value;
use crate::{Unsupported, value};

/// A message of TLC's coverage report: its code and its text, without `-tool`'s framing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoverageMessage {
    pub code: u32,
    pub text: String,
}

/// TLC's coverage report: what TLC prints between `The coverage statistics at ...` (2201) and
/// `End of statistics.` (2202), none where TLC prints no report, with the states the pass
/// generated and found distinct, which the caller holds against its search's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoverageReport {
    pub messages: Vec<CoverageMessage>,
    pub generated: u64,
    pub distinct: u64,
}

/// How many states `DiskStateQueue` holds in memory before it writes them out, which loses the
/// cost model their values carry.
const QUEUE_BUFFER: usize = 8192;

impl Rebuilder<'_> {
    /// TLC's coverage report for the model, as TLC's search at one worker counts it. `sources`
    /// reads a module's source by its name, which places the nodes SANY makes of parts of the
    /// IR's; `polynomial` is the index of TLC's fingerprint polynomial (`-fp`), which TLC's
    /// estimates of the variables' counts depend on. Runs on a thread with a deep stack, as the
    /// search does.
    pub fn coverage(
        &mut self,
        sources: &dyn Fn(&str) -> Option<String>,
        polynomial: usize,
    ) -> Result<CoverageReport, Unsupported> {
        let ir = self.evaluator().ir;
        decline_unported(ir)?;
        let old = std::mem::replace(self.evaluator(), crate::eval::Evaluator::new(ir));
        let mut sem = Sem::new(ir, sources);
        let result = Plan::new(&mut sem).and_then(|plan| {
            let mut tool = Tool::new(&sem, old, ir.model.is_warning_enabled);
            run(&mut tool, &plan, polynomial)
        });
        result.map_err(|halt| match halt {
            Halt::No(why) => Unsupported(why),
            Halt::Fail(why) => Unsupported(format!("a failure TLC reports: {why}")),
            Halt::Stop => Unsupported("a search the pass stopped early".into()),
        })
    }
}

/// FxHash's step, for the pass's maps of numbers, whose lookups SipHash would mostly spend.
#[derive(Default, Clone, Copy)]
pub(crate) struct FastHasher(u64);

impl std::hash::Hasher for FastHasher {
    fn write(&mut self, bytes: &[u8]) {
        for &byte in bytes {
            self.write_u64(u64::from(byte));
        }
    }

    fn write_u32(&mut self, word: u32) {
        self.write_u64(u64::from(word));
    }

    fn write_u64(&mut self, word: u64) {
        self.0 = (self.0.rotate_left(5) ^ word).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }

    fn write_usize(&mut self, word: usize) {
        self.write_u64(word as u64);
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

pub(crate) type FastMap<K, V> = HashMap<K, V, std::hash::BuildHasherDefault<FastHasher>>;

// What the port doesn't follow of TLC at all.
fn decline_unported(ir: &tla_ir::Ir) -> Result<(), Unsupported> {
    let model = &ir.model;
    let why = if model.view.is_some() {
        Some("a VIEW")
    } else if model.startup.symmetry.is_some() {
        Some("a SYMMETRY")
    } else if !model.live_formula.is_empty() || !model.atoms.is_empty() {
        Some("temporal properties")
    } else if !model.property_invariants.is_empty()
        || !model.action_properties.is_empty()
        || !model.initial_predicates.is_empty()
    {
        Some("properties TLC checks as invariants or actions")
    } else if !model.possible.is_empty() {
        Some("a _POSSIBLE predicate")
    } else if !model.postconditions.is_empty() {
        Some("a POSTCONDITION")
    } else if !model.startup.definitions.is_empty() {
        Some("a constant definition with effects")
    } else if model.scope.is_some() {
        Some("an INSTANCE's scope")
    } else if model.next.is_none() {
        Some("no next-state relation")
    } else if ir.variables.is_empty() {
        Some("no variables")
    } else {
        None
    };
    match why {
        Some(why) => Err(Unsupported(format!("coverage of a model with {why}"))),
        None => Ok(()),
    }
}

/// What the model asks of the search, translated: the initial predicates, TLC's actions, the
/// invariants and the constraints, each with its definition.
struct Plan {
    /// Each initial predicate, with how TLC names it.
    inits: Vec<(SId, String)>,
    next: SId,
    invariants: Vec<(SId, DefId)>,
    action_constraints: Vec<(SId, DefId)>,
    constraints: Vec<(SId, DefId)>,
    variables: Vec<SourceRange>,
}

impl Plan {
    fn new(sem: &mut Sem) -> Result<Plan, Halt> {
        let ir = sem.ir;
        let mut inits = Vec::new();
        init_definitions(sem, ir.model.init, &mut inits)?;
        let next = sem
            .expression(ir.model.next.expect("a next-state relation"))
            .map_err(unsupported)?;
        let named =
            |names: &[tla_ir::ConfigName], sem: &mut Sem| -> Result<Vec<(SId, DefId)>, Halt> {
                let mut list = Vec::new();
                for name in names {
                    let Some(index) = name.definition else {
                        return no("a configured name without a definition");
                    };
                    let def = sem.global(index).map_err(unsupported)?;
                    // TLC computes a constant one as it starts and checks nothing of it after.
                    if sem.def(def).is_constant {
                        continue;
                    }
                    list.push((sem.def(def).body.expect("a body"), def));
                }
                Ok(list)
            };
        let invariants: Vec<tla_ir::ConfigName> = ir
            .model
            .invariants
            .iter()
            .map(|invariant| invariant.root.clone())
            .collect();
        let invariants = named(&invariants, sem)?;
        let action_constraints = named(&ir.model.action_constraints, sem)?;
        let constraints = named(&ir.model.constraints, sem)?;
        let variables = sem.variable_places().map_err(unsupported)?;
        Ok(Plan {
            inits,
            next,
            invariants,
            action_constraints,
            constraints,
            variables,
        })
    }
}

fn unsupported(error: Unsupported) -> Halt {
    Halt::No(error.0)
}

// The initial predicates TLC takes from the INIT or SPECIFICATION: definitions, each the
// conjunct of one.
fn init_definitions(
    sem: &mut Sem,
    node: tla_ir::NodeId,
    inits: &mut Vec<(SId, String)>,
) -> Result<(), Halt> {
    let ir = sem.ir;
    let mut node = node;
    while let NodeKind::Reference(target) = ir.nodes.arena[node as usize].kind {
        node = target;
    }
    match &ir.nodes.arena[node as usize].kind {
        NodeKind::Identifier(name) if !name.is_local => match name.resolution {
            Resolution::Definition(index) => {
                let def = definition_named(sem, index, name.text)?;
                let body = sem.def(def).body.expect("a body");
                inits.push((body, label(sem, def, body)?));
                Ok(())
            }
            _ => no("an initial predicate that isn't a definition"),
        },
        NodeKind::And(operands) if ir.nodes.arena[node as usize].range.is_none() => {
            for &operand in operands {
                init_definitions(sem, operand, inits)?;
            }
            Ok(())
        }
        // A SPECIFICATION's conjunct, which the IR holds as the body of the definition TLC
        // names the initial predicate by, written right before it.
        _ => {
            let pred = sem.expression(node).map_err(unsupported)?;
            // TLC takes the body of an operator SPEC applies to arguments, with them bound.
            if let SKind::Appl {
                op: Op::Def(def), ..
            } = &sem.node(pred).kind
                && !sem.def(*def).params.is_empty()
            {
                return no("an initial predicate SPEC applies an operator to arguments for");
            }
            let Some(range) = sem.node(pred).range else {
                return no("an initial predicate without a place in the source");
            };
            // TLC names a predicate the SPECIFICATION writes out as `<Action place>`.
            let label = match (sem.definition_before(range), sem.ends_definition(range)) {
                (Some((name, declaration)), Some(true)) => {
                    format!("<{name} {}>", describe(sem, Some(declaration)))
                }
                (_, Some(_)) => format!("<Action {}>", describe(sem, Some(range))),
                (_, None) => return no("an initial predicate the port can't place"),
            };
            inits.push((pred, label));
            Ok(())
        }
    }
}

fn definition_named(sem: &mut Sem, index: Index, text: tla_ir::TextId) -> Result<DefId, Halt> {
    let def = sem.global(index).map_err(unsupported)?;
    if sem.def(def).name != text || !sem.def(def).params.is_empty() {
        return no("an initial predicate the configuration replaces");
    }
    Ok(def)
}

/// TLC's state queue at one worker, first in first out, with which states it wrote out.
struct Queue {
    taken: VecDeque<Queued>,
    written: VecDeque<Vec<Queued>>,
    added: Vec<Queued>,
}

struct Queued {
    state: St,
    /// The state's record in the trace.
    record: usize,
}

impl Queue {
    fn new() -> Queue {
        Queue {
            taken: VecDeque::new(),
            written: VecDeque::new(),
            added: Vec::new(),
        }
    }

    fn enqueue(&mut self, queued: Queued) {
        if self.added.len() == QUEUE_BUFFER {
            // The values TLC reads back hold no cost model.
            let written = std::mem::take(&mut self.added)
                .into_iter()
                .map(|queued| Queued {
                    state: queued
                        .state
                        .iter()
                        .map(|value| value.as_ref().map(copied))
                        .collect(),
                    record: queued.record,
                })
                .collect();
            self.written.push_back(written);
        }
        self.added.push(queued);
    }

    fn dequeue(&mut self) -> Option<Queued> {
        if self.taken.is_empty() {
            self.taken = match self.written.pop_front() {
                Some(written) => written.into(),
                None => std::mem::take(&mut self.added).into(),
            };
        }
        self.taken.pop_front()
    }
}

// A value with allocations of its own, as TLC reads it back from disk.
fn copied(value: &Value) -> Value {
    match value {
        Value::Set(elements) => Value::Set(std::rc::Rc::new(elements.iter().map(copied).collect())),
        Value::Function(function) => Value::Function(std::rc::Rc::new(value::Function {
            domain: function.domain.iter().map(copied).collect(),
            range: function.range.iter().map(copied).collect(),
            class: function.class.clone(),
            written: std::cell::RefCell::new(None),
            search: function.search.clone(),
            interval: function.interval,
        })),
        other => other.clone(),
    }
}

/// A state the search kept: its fingerprint and the state it came from.
struct Record {
    fingerprint: u64,
    parent: Option<usize>,
}

/// The states of TLC's actions, with a cost model each, and the other roots.
struct Roots {
    inits: Vec<Action>,
    actions: Vec<Action>,
    invariants: Vec<Action>,
    action_constraints: Vec<Action>,
    constraints: Vec<Action>,
    /// The roots in the order TLC reports them, after the variables.
    report: Vec<Cm>,
}

fn label(sem: &Sem, def: DefId, pred: SId) -> Result<String, Halt> {
    let declaration = sem.declaration(def).map_err(unsupported)?;
    let name = sem.text(sem.def(def).name);
    let body = sem.def(def).body.expect("a body");
    let place = describe(sem, Some(declaration));
    let actual = sem.node(pred).range;
    if sem.node(body).range == actual {
        return Ok(format!("<{name} {place}>"));
    }
    let Some(actual) = actual else {
        return no("an action without a place in the source");
    };
    Ok(format!(
        "<{name} {place} ({} {} {} {})>",
        actual.start_line, actual.start_column, actual.end_line, actual.end_column
    ))
}

fn run(tool: &mut Tool, plan: &Plan, polynomial: usize) -> Result<CoverageReport, Halt> {
    let sem = tool.sem;
    // TLC's actions, split as `Tool.getActions` splits the next-state relation.
    let mut split = Vec::new();
    split_actions(tool, plan.next, &Ctx::default(), None, &mut split)?;
    // The primed nodes of the next-state relation (`getPrimedLocs`).
    let mut primed = HashSet::new();
    collect_primed(tool, plan.next, &Ctx::default(), &mut primed)?;
    let mut model = Model::new();
    let make = |model: &mut Model, pred: SId, def: DefId, relation: Relation| -> Result<Cm, Halt> {
        let label = label(sem, def, pred)?;
        Creator::create(model, sem, &primed, pred, Root { relation, label }).map_err(unsupported)
    };
    let root = |pred: SId, cm: Cm| Action {
        pred,
        ctx: Ctx::default(),
        cm,
    };
    let mut roots = Roots {
        inits: Vec::new(),
        actions: Vec::new(),
        invariants: Vec::new(),
        action_constraints: Vec::new(),
        constraints: Vec::new(),
        report: Vec::new(),
    };
    for (pred, label) in &plan.inits {
        let cm = Creator::create(
            &mut model,
            sem,
            &primed,
            *pred,
            Root {
                relation: Relation::Init,
                label: label.clone(),
            },
        )
        .map_err(unsupported)?;
        roots.inits.push(Action {
            pred: *pred,
            ctx: Ctx::default(),
            cm,
        });
    }
    let mut by_pred: FastMap<SId, Cm> = FastMap::default();
    for (pred, ctx, def) in split {
        let cm = match by_pred.get(&pred) {
            Some(&cm) => cm,
            None => {
                let cm = match def {
                    Some(def) => make(&mut model, pred, def, Relation::Next)?,
                    // An action of no operator, which TLC names by where it is.
                    None => {
                        let Some(range) = sem.node(pred).range else {
                            return no("an action without a place in the source");
                        };
                        let label = format!("<Action {}>", describe(sem, Some(range)));
                        let root = Root {
                            relation: Relation::Next,
                            label,
                        };
                        Creator::create(&mut model, sem, &primed, pred, root)
                            .map_err(unsupported)?
                    }
                };
                by_pred.insert(pred, cm);
                cm
            }
        };
        roots.actions.push(Action { pred, ctx, cm });
    }
    for &(pred, def) in &plan.invariants {
        let cm = make(&mut model, pred, def, Relation::Prop)?;
        roots.invariants.push(root(pred, cm));
    }
    for &(pred, def) in &plan.action_constraints {
        let cm = make(&mut model, pred, def, Relation::Constraint)?;
        roots.action_constraints.push(root(pred, cm));
    }
    for &(pred, def) in &plan.constraints {
        let cm = make(&mut model, pred, def, Relation::Constraint)?;
        roots.constraints.push(root(pred, cm));
    }
    // The order of the report: the initial predicates, the actions by their place, each once,
    // the invariants, the action constraints and the state constraints.
    roots
        .report
        .extend(roots.inits.iter().map(|action| action.cm));
    let mut sorted: Vec<&Action> = Vec::new();
    for action in &roots.actions {
        let range = sem.node(action.pred).range;
        if !sorted
            .iter()
            .any(|known| sem.node(known.pred).range == range)
        {
            sorted.push(action);
        }
    }
    let ranges: Option<Vec<SourceRange>> = sorted
        .iter()
        .map(|action| sem.node(action.pred).range)
        .collect();
    let Some(ranges) = ranges else {
        return no("an action without a place in the source");
    };
    if ranges.iter().any(|range| range.module != ranges[0].module) {
        return no("actions in several modules, which TLC orders by when it read their names");
    }
    let mut order: Vec<usize> = (0..sorted.len()).collect();
    order.sort_by_key(|&index| {
        let range = ranges[index];
        (
            range.start_line,
            range.start_column,
            range.end_line,
            range.end_column,
        )
    });
    let mut reported = HashSet::new();
    for index in order {
        if reported.insert(sorted[index].cm) {
            roots.report.push(sorted[index].cm);
        }
    }
    roots
        .report
        .extend(roots.invariants.iter().map(|action| action.cm));
    roots
        .report
        .extend(roots.action_constraints.iter().map(|action| action.cm));
    roots
        .report
        .extend(roots.constraints.iter().map(|action| action.cm));
    tool.model = model;
    let mut search = Search {
        roots: &roots,
        queue: Queue::new(),
        records: Vec::new(),
        seen: HashSet::default(),
        fingerprints: Fingerprints::new(Polynomial::get(polynomial)),
        generated: 0,
        distinct: hll::Distinct::new(tool.width, polynomial),
        order: tlc_order(sem.ir),
        check_deadlock: sem.ir.model.check_deadlock,
    };
    let ending = search.run(tool)?;
    let generated = search.generated;
    let distinct = search.seen.len() as u64;
    // TLC prints no report where an initial state violates an invariant, or there are no
    // actions.
    if matches!(ending, Ending::InitialViolation) || roots.actions.is_empty() {
        return Ok(CoverageReport {
            messages: Vec::new(),
            generated,
            distinct,
        });
    }
    tool.mismatch_check()?;
    let counts = search.distinct.counts();
    let mut messages = Vec::new();
    for &position in &search.order {
        let place = describe(sem, Some(plan.variables[position]));
        let name = sem.text(sem.ir.variables[position]);
        messages.push(CoverageMessage {
            code: 2779,
            text: format!("<{name} {place}>: {}", counts[position]),
        });
    }
    let mut printer = Printer {
        model: &tool.model,
        sem,
        lines: Vec::new(),
        is_unplaced: false,
    };
    for &root in &roots.report {
        printer.report_root(root);
    }
    if printer.is_unplaced {
        return no("an expression the IR holds without a place");
    }
    messages.extend(
        printer
            .lines
            .into_iter()
            .map(|(code, text)| CoverageMessage { code, text }),
    );
    Ok(CoverageReport {
        messages,
        generated,
        distinct,
    })
}

/// TLC's order of the variables, as positions in the IR's.
fn tlc_order(ir: &tla_ir::Ir) -> Vec<usize> {
    if ir.tlc_order.len() == ir.variables.len() {
        ir.tlc_order
            .iter()
            .map(|&position| position as usize)
            .collect()
    } else {
        (0..ir.variables.len()).collect()
    }
}

/// `Tool.getActions`: the next-state relation split at disjunctions, at `\E` over a constant set,
/// and into the bodies of operators applied to constant arguments.
fn split_actions(
    tool: &mut Tool,
    node: SId,
    ctx: &Ctx,
    name: Option<DefId>,
    out: &mut Vec<(SId, Ctx, Option<DefId>)>,
) -> Result<(), Halt> {
    let sem = tool.sem;
    let SKind::Appl {
        op, args, bounds, ..
    } = &sem.node(node).kind
    else {
        return match &sem.node(node).kind {
            SKind::Let { body, .. } => split_actions(tool, *body, ctx, name, out),
            _ => no("a next-state relation that isn't a boolean expression"),
        };
    };
    match *op {
        Op::Code(Code::DisjList | Code::Lor) => {
            for arg in args.iter().flatten() {
                split_actions(tool, *arg, ctx, name, out)?;
            }
            Ok(())
        }
        Op::Code(Code::BoundedExists) => {
            let count = out.len();
            let empty: St = vec![None; tool.width];
            let mut bindings = Vec::new();
            let enumerated = (|| -> Result<(), Halt> {
                let mut contexts =
                    tool.contexts(bounds, ctx, &empty, Some(&empty), 0, model::NO_CM)?;
                while let Some(binding) = tool.next_context(&mut contexts)? {
                    bindings.push(binding);
                }
                Ok(())
            })();
            match enumerated {
                Ok(()) if bindings.is_empty() => {
                    out.push((node, ctx.clone(), name));
                    Ok(())
                }
                Ok(()) => {
                    for binding in bindings {
                        match split_actions(tool, args[0].expect("a body"), &binding, name, out) {
                            Err(Halt::Fail(_)) => {
                                out.truncate(count);
                                out.push((node, ctx.clone(), name));
                                return Ok(());
                            }
                            result => result?,
                        }
                    }
                    Ok(())
                }
                Err(Halt::Fail(_)) => {
                    out.truncate(count);
                    out.push((node, ctx.clone(), name));
                    Ok(())
                }
                Err(halt) => Err(halt),
            }
        }
        Op::Code(_) => {
            out.push((node, ctx.clone(), name));
            Ok(())
        }
        Op::Def(def) | Op::Substituted(def)
            if matches!(op, Op::Substituted(_))
                || !tool.is_bound(ctx, def) && !tool.is_constant(def)? =>
        {
            let is_constant = args
                .iter()
                .flatten()
                .all(|&arg| level(sem, arg, &mut Vec::new()) == 0);
            if is_constant {
                let empty: St = vec![None; tool.width];
                let mut ctx1 = ctx.clone();
                let mut failed = false;
                for (index, arg) in args.iter().flatten().enumerate() {
                    match tool.eval(*arg, ctx, &empty, Some(&empty), 0, model::NO_CM) {
                        Ok(value) => ctx1 = ctx1.bind_value(sem.def(def).params[index], value),
                        Err(Halt::Fail(_)) => {
                            failed = true;
                            break;
                        }
                        Err(halt) => return Err(halt),
                    }
                }
                if !failed {
                    let body = sem.def(def).body.expect("a body");
                    return split_actions(tool, body, &ctx1, Some(def), out);
                }
            }
            if matches!(op, Op::Substituted(_)) {
                return no("an action of a constant operator the configuration replaces");
            }
            out.push((node, ctx.clone(), Some(def)));
            Ok(())
        }
        Op::Def(def) => {
            out.push((node, ctx.clone(), Some(def)));
            Ok(())
        }
        _ => no("an action TLC names by an operator that isn't a definition"),
    }
}

/// SANY's level of an expression, as far as `getActions` asks: 0 where it reads no variable.
fn level(sem: &Sem, node: SId, visiting: &mut Vec<DefId>) -> u8 {
    match &sem.node(node).kind {
        SKind::Num(_) | SKind::Str(_) | SKind::At => 0,
        SKind::Let { defs, body } => {
            let mut result = level(sem, *body, visiting);
            for &def in defs {
                if let Some(body) = sem.def(def).body {
                    result = result.max(level(sem, body, visiting));
                }
            }
            result
        }
        SKind::Appl {
            op, args, bounds, ..
        } => {
            let mut result = match op {
                Op::Var(_) => 1,
                Op::Code(Code::Prime | Code::Unchanged | Code::SquareAct | Code::AngleAct) => 2,
                Op::Def(def) | Op::Substituted(def) => {
                    if visiting.contains(def) {
                        0
                    } else {
                        visiting.push(*def);
                        let result = sem
                            .def(*def)
                            .body
                            .map_or(0, |body| level(sem, body, visiting));
                        visiting.pop();
                        result
                    }
                }
                _ => 0,
            };
            for arg in args.iter().flatten() {
                result = result.max(level(sem, *arg, visiting));
            }
            for bound in bounds {
                result = result.max(level(sem, bound.set, visiting));
            }
            result
        }
    }
}

/// `collectPrimedLocs`: the places of `x' = e` and `x' \in S` for a variable x, of the variables
/// of an UNCHANGED, and of the subscript of `[A]_v`, through the operators the relation applies.
fn collect_primed(
    tool: &mut Tool,
    node: SId,
    ctx: &Ctx,
    out: &mut HashSet<Place>,
) -> Result<(), Halt> {
    let sem = tool.sem;
    let (op, args) = match &sem.node(node).kind {
        SKind::Appl { op, args, .. } => (*op, args),
        SKind::Let { body, .. } => return collect_primed(tool, *body, ctx, out),
        _ => return Ok(()),
    };
    let arg = |index: usize| args[index].expect("an operand");
    match op {
        Op::Code(Code::FcnApply) => collect_primed(tool, arg(0), ctx, out),
        Op::Code(Code::IfThenElse) => {
            collect_primed(tool, arg(1), ctx, out)?;
            collect_primed(tool, arg(2), ctx, out)
        }
        Op::Code(Code::Case) => {
            for pair in args.iter().flatten() {
                if let SKind::Appl {
                    args: pair_args, ..
                } = &sem.node(*pair).kind
                {
                    collect_primed(tool, pair_args[1].expect("a value"), ctx, out)?;
                }
            }
            Ok(())
        }
        Op::Code(Code::Eq | Code::In) => {
            if tool.primed_variable(arg(0), ctx)?.is_some()
                && let Some(range) = sem.node(node).range
            {
                out.insert(place(range));
            }
            Ok(())
        }
        Op::Code(
            Code::ConjList
            | Code::DisjList
            | Code::BoundedExists
            | Code::BoundedForall
            | Code::Land
            | Code::Lor
            | Code::Implies,
        ) => {
            for operand in args.iter().flatten() {
                collect_primed(tool, *operand, ctx, out)?;
            }
            Ok(())
        }
        Op::Code(Code::Unchanged) => collect_unchanged(tool, arg(0), ctx, out),
        Op::Code(Code::AngleAct) => collect_primed(tool, arg(0), ctx, out),
        Op::Code(Code::SquareAct) => {
            collect_primed(tool, arg(0), ctx, out)?;
            if !sem.node(arg(1)).is_appl() {
                return no("a subscript that is no application");
            }
            if let Some(range) = sem.node(arg(1)).range {
                out.insert(place(range));
            }
            Ok(())
        }
        Op::Code(_) => Ok(()),
        _ => match tool.walked_into(node, ctx)? {
            Some((body, inner)) => collect_primed(tool, body, &inner, out),
            None => Ok(()),
        },
    }
}

fn collect_unchanged(
    tool: &mut Tool,
    node: SId,
    ctx: &Ctx,
    out: &mut HashSet<Place>,
) -> Result<(), Halt> {
    let sem = tool.sem;
    let SKind::Appl { op, args, .. } = &sem.node(node).kind else {
        return Ok(());
    };
    match op {
        Op::Var(_) => {
            if let Some(range) = sem.node(node).range {
                out.insert(place(range));
            }
            Ok(())
        }
        Op::Code(Code::Tuple) => {
            for item in args.iter().flatten() {
                collect_unchanged(tool, *item, ctx, out)?;
            }
            Ok(())
        }
        Op::Def(def)
            if args.is_empty() && !tool.is_bound(ctx, *def) && !tool.is_constant(*def)? =>
        {
            let body = sem.def(*def).body.expect("a body");
            collect_unchanged(tool, body, ctx, out)
        }
        _ => Ok(()),
    }
}

enum Ending {
    Done,
    InitialViolation,
    Stopped,
}

/// TLC's `ModelChecker` and `Worker` at one worker.
struct Search<'r> {
    roots: &'r Roots,
    queue: Queue,
    records: Vec<Record>,
    seen: HashSet<u64, std::hash::BuildHasherDefault<FastHasher>>,
    fingerprints: Fingerprints,
    generated: u64,
    distinct: hll::Distinct,
    order: Vec<usize>,
    check_deadlock: bool,
}

/// What a successor did to the search.
enum Successor {
    Kept,
    Violation { state: St, record: Option<usize> },
}

impl Search<'_> {
    fn fingerprint(&mut self, state: &St) -> Result<u64, Halt> {
        let values: Option<Vec<&Value>> = self
            .order
            .iter()
            .map(|&position| state[position].as_ref())
            .collect();
        let Some(values) = values else {
            return no("a state TLC finds incomplete");
        };
        // TLC fingerprints a lazy set by converting it, which counts into its cost model.
        if values.iter().any(|value| holds_lazy(value)) {
            return no("a state that holds a set TLC keeps lazy");
        }
        state_fingerprint(&mut self.fingerprints, &values)
            .ok_or_else(|| Halt::No("a state the port can't fingerprint as TLC does".into()))
    }

    fn run(&mut self, tool: &mut Tool) -> Result<Ending, Halt> {
        // `doInit`: each initial state checked as `DoInitFunctor` checks it.
        let inits = self.roots.inits.clone();
        let mut violation = false;
        {
            let search = &mut *self;
            let mut functor = |tool: &mut Tool, state: &St| -> Result<(), Halt> {
                search.generated += 1;
                if state.iter().any(Option::is_none) {
                    return no("an initial state TLC finds incomplete");
                }
                let mut is_in = true;
                for constraint in &search.roots.constraints {
                    if !tool.is_in(constraint, state, None)? {
                        is_in = false;
                        break;
                    }
                }
                let mut seen = false;
                if is_in {
                    let fingerprint = search.fingerprint(state)?;
                    seen = !search.seen.insert(fingerprint);
                    if !seen {
                        search.records.push(Record {
                            fingerprint,
                            parent: None,
                        });
                        let record = search.records.len() - 1;
                        search.queue.enqueue(Queued {
                            state: state.clone(),
                            record,
                        });
                    }
                }
                if !seen {
                    for invariant in &search.roots.invariants {
                        if !tool.is_valid(invariant, state, Some(&vec![None; state.len()]))? {
                            return Err(Halt::Stop);
                        }
                    }
                }
                Ok(())
            };
            match tool.init_states(&inits, &mut functor) {
                Ok(()) => {}
                Err(Halt::Stop) => violation = true,
                Err(halt) => return Err(halt),
            }
        }
        if violation {
            return Ok(Ending::InitialViolation);
        }
        // The workers: each state in turn, through each action.
        while let Some(current) = self.queue.dequeue() {
            let before = self.generated;
            let actions = self.roots.actions.clone();
            let mut stop = None;
            for action in &actions {
                let search = &mut *self;
                let current_ref = &current;
                let mut functor = |tool: &mut Tool, next: &St| -> Result<(), Halt> {
                    match search.successor(tool, action, current_ref, next)? {
                        Successor::Kept => Ok(()),
                        Successor::Violation { state, record } => {
                            stop = Some((state, record));
                            Err(Halt::Stop)
                        }
                    }
                };
                match tool.next_states(action, &current.state, &mut functor) {
                    Ok(_) => {}
                    Err(Halt::Stop) => break,
                    Err(halt) => return Err(halt),
                }
            }
            if let Some((state, record)) = stop {
                self.violation_traces(tool, &current, &state, record)?;
                return Ok(Ending::Stopped);
            }
            if self.check_deadlock && self.generated == before {
                self.deadlock_traces(tool, &current)?;
                return Ok(Ending::Stopped);
            }
        }
        Ok(Ending::Done)
    }

    /// `Worker.addElement`.
    fn successor(
        &mut self,
        tool: &mut Tool,
        action: &Action,
        current: &Queued,
        next: &St,
    ) -> Result<Successor, Halt> {
        tool.count_root(action.cm);
        self.generated += 1;
        if next.iter().any(Option::is_none) {
            return no("a successor TLC finds incomplete");
        }
        let mut is_in = true;
        for constraint in &self.roots.constraints {
            if !tool.is_in(constraint, next, None)? {
                is_in = false;
                break;
            }
        }
        if is_in {
            for constraint in &self.roots.action_constraints {
                if !tool.is_in(constraint, &current.state, Some(next))? {
                    is_in = false;
                    break;
                }
            }
        }
        let mut unseen = true;
        let mut record = None;
        if is_in {
            let fingerprint = self.fingerprint(next)?;
            unseen = self.seen.insert(fingerprint);
            if unseen {
                self.records.push(Record {
                    fingerprint,
                    parent: Some(current.record),
                });
                record = Some(self.records.len() - 1);
                tool.count_distinct(action.cm);
            }
        }
        if unseen {
            for invariant in &self.roots.invariants {
                if !tool.is_valid(invariant, next, Some(&vec![None; next.len()]))? {
                    return Ok(Successor::Violation {
                        state: next.clone(),
                        record,
                    });
                }
            }
        }
        if let Some(record) = record {
            self.distinct.add(next).ok_or_else(|| {
                Halt::No("a value whose fingerprint the port doesn't compute".into())
            })?;
            self.queue.enqueue(Queued {
                state: next.clone(),
                record,
            });
        }
        Ok(Successor::Kept)
    }

    // The path of records from an initial state to `record`, the initial state first.
    fn path(&self, record: usize) -> Vec<u64> {
        let mut path = Vec::new();
        let mut at = Some(record);
        while let Some(index) = at {
            path.push(self.records[index].fingerprint);
            at = self.records[index].parent;
        }
        path.reverse();
        path
    }

    /// `getTrace` of the state at `record`: its states from the initial one to the one before
    /// it, rebuilt; none for an initial state.
    fn trace(&mut self, tool: &mut Tool, record: usize) -> Result<Vec<St>, Halt> {
        let path = self.path(record);
        if path.len() < 2 {
            return Ok(Vec::new());
        }
        let mut states = vec![self.initial_state(tool, path[0])?];
        for &fingerprint in &path[1..path.len() - 1] {
            let last = states.last().expect("a state").clone();
            states.push(self.step(tool, &last, Target::Fingerprint(fingerprint))?);
        }
        Ok(states)
    }

    /// `Tool.getState(fp)`: the first initial state of the fingerprint, all of them computed.
    fn initial_state(&mut self, tool: &mut Tool, fingerprint: u64) -> Result<St, Halt> {
        let inits = self.roots.inits.clone();
        let mut found = None;
        let search = &mut *self;
        let mut functor = |_: &mut Tool, state: &St| -> Result<(), Halt> {
            if found.is_none() && search.fingerprint(state)? == fingerprint {
                found = Some(state.clone());
            }
            Ok(())
        };
        tool.init_states(&inits, &mut functor)?;
        found.ok_or_else(|| Halt::No("an initial state TLC doesn't find again".into()))
    }

    /// `Tool.getState(fp, s)` or `getState(s1, s)`: the successor of `state`, by the first action
    /// whose successors, each computed, hold it.
    fn step(&mut self, tool: &mut Tool, state: &St, target: Target) -> Result<St, Halt> {
        let actions = self.roots.actions.clone();
        for action in &actions {
            let mut successors = Vec::new();
            let mut functor = |_: &mut Tool, next: &St| -> Result<(), Halt> {
                successors.push(next.clone());
                Ok(())
            };
            tool.next_states(action, state, &mut functor)?;
            tool.count_roots(action.cm, successors.len() as u64);
            for successor in successors {
                let is_it = match &target {
                    Target::Fingerprint(fingerprint) => {
                        self.fingerprint(&successor)? == *fingerprint
                    }
                    Target::State(wanted) => tool.states_equal(&successor, wanted)?,
                };
                if is_it {
                    return Ok(successor);
                }
            }
        }
        no("a successor TLC doesn't find again")
    }

    // The rebuilds of a trace TLC prints after an invariant fails on a successor of `current`
    // (`TLCTrace.printTrace`), and again for the postconditions (`Worker.doPostCondition`).
    fn violation_traces(
        &mut self,
        tool: &mut Tool,
        current: &Queued,
        next: &St,
        record: Option<usize>,
    ) -> Result<(), Halt> {
        let is_initial = self.records[current.record].parent.is_none();
        let fingerprint = self.records[current.record].fingerprint;
        if !is_initial {
            let prefix = self.trace(tool, current.record)?;
            self.step(
                tool,
                prefix.last().expect("a state"),
                Target::Fingerprint(fingerprint),
            )?;
        }
        self.step(tool, &current.state, Target::State(next.clone()))?;
        match record {
            // The successor TLC kept: its trace up to `current`, then the successor.
            Some(record) => {
                self.trace(tool, record)?;
            }
            // A successor outside the constraints, which TLC didn't keep.
            None if is_initial => {
                self.initial_state(tool, fingerprint)?;
            }
            None => {
                let prefix = self.trace(tool, current.record)?;
                let last = prefix.last().expect("a state").clone();
                self.step(tool, &last, Target::State(current.state.clone()))?;
            }
        }
        self.step(tool, &current.state, Target::State(next.clone()))?;
        Ok(())
    }

    // The rebuilds of a deadlock's trace, as printed and for the postconditions.
    fn deadlock_traces(&mut self, tool: &mut Tool, current: &Queued) -> Result<(), Halt> {
        let fingerprint = self.records[current.record].fingerprint;
        if self.records[current.record].parent.is_none() {
            self.initial_state(tool, fingerprint)?;
            return Ok(());
        }
        let prefix = self.trace(tool, current.record)?;
        self.step(
            tool,
            prefix.last().expect("a state"),
            Target::Fingerprint(fingerprint),
        )?;
        let prefix = self.trace(tool, current.record)?;
        self.step(
            tool,
            prefix.last().expect("a state"),
            Target::State(current.state.clone()),
        )?;
        Ok(())
    }
}

fn holds_lazy(value: &Value) -> bool {
    match value {
        Value::Lazy(_) | Value::Lambda(_) | Value::Unsorted(_) => true,
        Value::Set(elements) => elements.iter().any(holds_lazy),
        Value::Function(function) => function.range.iter().any(holds_lazy),
        _ => false,
    }
}

enum Target {
    Fingerprint(u64),
    State(St),
}

/// Where the coverage pass streams a lazy set in TLC's order: the sets whose own enumeration
/// is the normalized order of their elements.
pub(crate) fn is_streamed_in_order(set: &Value) -> bool {
    let Value::Lazy(lazy) = set else {
        return matches!(set, Value::Set(_) | Value::Interval(..));
    };
    match &**lazy {
        value::Lazy::Subset(base) => matches!(base, Value::Set(_) | Value::Interval(..)),
        value::Lazy::FunctionSet(domain, range) => {
            matches!(domain, Value::Set(_) | Value::Interval(..)) && is_streamed_in_order(range)
        }
        value::Lazy::RecordSet(fields, _) => {
            fields.iter().all(|(_, part)| is_streamed_in_order(part))
        }
        value::Lazy::Product(parts) => parts.iter().all(is_streamed_in_order),
        _ => false,
    }
}
