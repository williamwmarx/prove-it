//! Where the search stopped on an error, evaluated again as TLC's `CallStackTool` evaluates it:
//! TLC's message for the error, and the nested expressions it was in, as `tlc/replay.ts` and the
//! tracing evaluator of `evaluate.ts` record them and `getFailureMessage` and `formatCallStack` in
//! TypeScript print them.

use tla_ir::{NodeId, NodeKind, SourceRange};
use tla_values::{Id, Store};

use crate::eval::{CallStack, Evaluator, StackFrame};
use crate::rebuild::Rebuilder;
use crate::value::TlcMessage;
use crate::{Ending, Unsupported};

/// Where the search failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Site {
    /// Computing the initial states.
    Init,
    /// Computing the successors of the path's last state.
    Next,
}

/// TLC's report of an error: the code of the message, its text and its text in -tool output, and
/// the nested expressions it was evaluating, which TLC prints as message 2103 where there are any.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Failure {
    pub code: u32,
    pub message: String,
    pub tool_message: String,
    pub call_stack: Vec<SourceRange>,
}

const GENERAL: u32 = 1000;

const UNEXPECTED_EXCEPTION: &str = "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: ";

// A coded message in -tool output, which TLC marks inside the message that holds it.
fn nested(message: &TlcMessage) -> String {
    match message.code {
        Some(code) => format!(
            "@!@!@STARTMSG {code}:0 @!@!@\n{}\n@!@!@ENDMSG {code} @!@!@",
            message.text
        ),
        None => message.text.clone(),
    }
}

// `getFailureMessage`: an EvalException that escapes the computation of the next states keeps its
// own code; any other error there is an unexpected exception.
fn report(message: &TlcMessage, is_next_state: bool) -> (u32, String, String) {
    if is_next_state && message.is_eval_exception {
        let code = message.code.unwrap_or(GENERAL);
        return (code, message.text.clone(), message.text.clone());
    }
    let prefix = if is_next_state {
        UNEXPECTED_EXCEPTION
    } else {
        ""
    };
    (
        GENERAL,
        format!("{prefix}{}", message.text),
        format!("{prefix}{}", nested(message)),
    )
}

impl<'ir> Rebuilder<'ir> {
    /// Evaluates again where the search failed, at `site`, after the path `states` (as for
    /// `rebuild`; none for the initial predicate), and returns TLC's report of the error.
    /// `Unsupported` where the evaluator doesn't give TLC's message for the error, or where the
    /// evaluation doesn't fail again.
    pub fn evaluate_failure(
        &mut self,
        store: &Store,
        states: &[&[Id]],
        actions: &[Option<u32>],
        site: Site,
    ) -> Result<Failure, Unsupported> {
        let last = match states {
            [] => None,
            _ => Some(self.rebuild(store, states, actions, Ending::Kept)?.states),
        };
        let evaluator = self.evaluator();
        let ir = evaluator.ir;
        evaluator.printed.clear();
        evaluator.call_stack = Some(CallStack::default());
        let width = ir.variables.len();
        let level = states.len() as i32;
        let current: Vec<Option<_>> = last
            .and_then(|states| states.last().map(|state| state.values.clone()))
            .map(|values| values.into_iter().map(Some).collect())
            .unwrap_or_else(|| vec![None; width]);
        let result = match site {
            Site::Init => {
                evaluator.current = vec![None; width];
                evaluator.level = 0;
                let context = evaluator.scope_context(ir.model.scope);
                context.and_then(|context| {
                    evaluator.walk_action(ir.model.init, &context, true, &mut |_| Ok(true))
                })
            }
            Site::Next => {
                evaluator.current = current;
                evaluator.level = level;
                let actions: Vec<(NodeId, Option<u32>)> = if ir.model.actions.is_empty() {
                    vec![(ir.model.next, ir.model.scope)]
                } else {
                    ir.model
                        .actions
                        .iter()
                        .map(|action| (action.expression, action.scope))
                        .collect()
                };
                actions
                    .into_iter()
                    .try_for_each(|(expression, scope)| {
                        evaluator.next = vec![None; width];
                        let context = evaluator.scope_context(scope)?;
                        evaluator
                            .walk_action(expression, &context, false, &mut |_| Ok(true))
                            .map(|_| ())
                    })
                    .map(|()| true)
            }
        };
        let call_stack = evaluator.call_stack.take().unwrap_or_default();
        evaluator.printed.clear();
        let Err(error) = result else {
            return Err(Unsupported(
                "evaluating the failure again: it didn't fail".into(),
            ));
        };
        let Some(message) = error.message else {
            return Err(Unsupported(format!(
                "evaluating the failure again: {}",
                error.reason
            )));
        };
        let (code, text, tool_text) = report(&message, site == Site::Next);
        Ok(Failure {
            code,
            message: text,
            tool_message: tool_text,
            call_stack: ranges(evaluator, &call_stack),
        })
    }
}

// The ranges of the call stack's nodes, as `CallStack.toString` prints them: a node TLC evaluates
// again right inside itself once, and nothing for a node without a range.
fn ranges(evaluator: &Evaluator<'_>, call_stack: &CallStack) -> Vec<SourceRange> {
    let mut ranges = Vec::new();
    let mut previous = None;
    for &frame in &call_stack.frames {
        if previous == Some(frame) {
            continue;
        }
        previous = Some(frame);
        let range = match frame {
            StackFrame::Node(node) => evaluator.ir.nodes.arena[node as usize].range,
            StackFrame::Prefix(node, count) => prefix_range(evaluator, node, count),
        };
        ranges.extend(range);
    }
    ranges
}

// The range of SANY's node of the first `count` operands of an infix chain: from the chain's
// start to the end of its last operand there, as `getPrefix` in `tlc/replay.ts` takes it.
fn prefix_range(evaluator: &Evaluator<'_>, node: NodeId, count: usize) -> Option<SourceRange> {
    let range = evaluator.ir.nodes.arena[node as usize].range?;
    let junction = evaluator.ir.nodes.junctions.get(&node)?;
    let &(end_line, end_column) = junction.prefix_ends.get(count.checked_sub(2)?)?;
    debug_assert!(matches!(
        evaluator.ir.nodes.arena[node as usize].kind,
        NodeKind::And(_) | NodeKind::Or(_)
    ));
    Some(SourceRange {
        end_line,
        end_column,
        ..range
    })
}

/// TLC's `CallStack.toString`, with the line it ends with.
pub fn format_call_stack(ir: &tla_ir::Ir, call_stack: &[SourceRange]) -> String {
    if call_stack.is_empty() {
        return "    The error call stack is empty.\n".to_string();
    }
    let mut text = String::new();
    for (position, range) in call_stack.iter().enumerate() {
        text.push_str(&format!(
            "{position}. Line {}, column {} to line {}, column {} in {}\n",
            range.start_line,
            range.start_column,
            range.end_line,
            range.end_column,
            ir.texts[range.module as usize]
        ));
    }
    text.push('\n');
    text
}
