//! Pco.resolve: tlapm's parser lets an operator take in every later infix operator that is not
//! entirely below it, so SUBSET S \ T is SUBSET (S \ T) to tlapm though SANY reads (SUBSET S) \ T.
//! This regroups an infix application the way tlapm does. A port of `src/obligations/regroup.ts`.

use std::rc::Rc;

use tla_front::ast::{Expr, Expression, ExpressionKind, Position};

use crate::operators::{Fixity, Operator, lookup_operator};

enum Grouping {
    Attached(Expr),
    Reduced { is_final: bool },
}

/// The operator an expression leaves open on tlapm's parse stack, with the operand after it.
struct OpenOperator {
    operator: Operator,
    is_infix: bool,
    operand: Expr,
}

fn is_same_position(left: Option<Position>, right: Option<Position>) -> bool {
    matches!((left, right), (Some(left), Some(right)) if left.line == right.line && left.column == right.column)
}

fn get_start(expression: &Expression) -> Option<Position> {
    expression.location.range.as_ref().map(|range| range.start)
}

fn get_end(expression: &Expression) -> Option<Position> {
    expression.location.range.as_ref().map(|range| range.end)
}

fn with_end(expression: Expr, end: Option<Position>) -> Expr {
    match (&expression.location.range, end) {
        (Some(range), Some(end)) => {
            let mut changed = (*expression).clone();
            changed.location.range = Some(tla_front::ast::SourceRange {
                end,
                ..range.clone()
            });
            Rc::new(changed)
        }
        _ => expression,
    }
}

fn is_infix_fixity(fixity: Fixity) -> bool {
    matches!(
        fixity,
        Fixity::InfixLeft | Fixity::InfixNon | Fixity::InfixRight
    )
}

fn get_open_operator(expression: &Expression) -> Option<OpenOperator> {
    let (keyword, operand) = match &expression.kind {
        ExpressionKind::Apply { operator, args, .. } => {
            let operator = lookup_operator(operator);
            let is_infix = args.len() == 2 && is_infix_fixity(operator.fixity);
            let is_prefix = args.len() == 1 && operator.fixity == Fixity::Prefix;
            if !is_infix && !is_prefix {
                return None;
            }
            return Some(OpenOperator {
                operator,
                is_infix,
                operand: args.last()?.clone(),
            });
        }
        ExpressionKind::Always(inner) => ("[]", inner),
        ExpressionKind::Eventually(inner) => ("<>", inner),
        ExpressionKind::Enabled(inner) => ("ENABLED", inner),
        ExpressionKind::Unchanged(inner) => ("UNCHANGED", inner),
        _ => return None,
    };
    Some(OpenOperator {
        operator: lookup_operator(keyword),
        is_infix: false,
        operand: operand.clone(),
    })
}

/// The open operator's node with its last operand replaced.
fn replace_operand(expression: &Expression, operand: Expr) -> Expr {
    let mut changed = expression.clone();
    match &mut changed.kind {
        ExpressionKind::Apply { args, .. } => {
            if let Some(last) = args.last_mut() {
                *last = operand;
            }
        }
        ExpressionKind::Always(inner)
        | ExpressionKind::Eventually(inner)
        | ExpressionKind::Enabled(inner)
        | ExpressionKind::Unchanged(inner) => *inner = operand,
        _ => {}
    }
    Rc::new(changed)
}

fn is_below(left: &Operator, right: &Operator) -> bool {
    left.high < right.low
}

/// The infix application being regrouped.
struct Regrouping<'a> {
    expression: &'a Expr,
    operator: Operator,
    right: Expr,
    end: Option<Position>,
}

impl Regrouping<'_> {
    fn get_infix(&self, operand: Expr) -> Expr {
        let mut changed = (**self.expression).clone();
        let start = get_start(&operand);
        if let ExpressionKind::Apply { args, .. } = &mut changed.kind {
            *args = vec![operand, self.right.clone()];
        }
        if let (Some(range), Some(start)) = (&self.expression.location.range, start) {
            changed.location.range = Some(tla_front::ast::SourceRange {
                start,
                ..range.clone()
            });
        }
        Rc::new(changed)
    }

    fn attach(&self, node: &Expr, is_open: bool) -> Grouping {
        let open = if is_open {
            get_open_operator(node)
        } else {
            None
        };
        let Some(open) = open else {
            return Grouping::Reduced { is_final: false };
        };
        let inner = self.attach(
            &open.operand,
            is_same_position(get_end(&open.operand), get_end(node)),
        );
        let is_final = match inner {
            Grouping::Attached(expression) => {
                return Grouping::Attached(with_end(replace_operand(node, expression), self.end));
            }
            Grouping::Reduced { is_final } => is_final,
        };
        let operator = &self.operator;
        let is_reduced = !is_final
            && (is_below(operator, &open.operator)
                || (open.is_infix
                    && operator.fixity == Fixity::InfixLeft
                    && open.operator.fixity == Fixity::InfixLeft
                    && !is_below(&open.operator, operator)));
        if is_reduced {
            return Grouping::Reduced {
                is_final: !is_below(operator, &open.operator),
            };
        }
        Grouping::Attached(with_end(
            replace_operand(node, self.get_infix(open.operand.clone())),
            self.end,
        ))
    }
}

/// Regroups an infix application of two operands; anything else, or an application tlapm groups
/// as SANY does, comes back as itself.
pub fn regroup(expression: &Expr) -> Expr {
    let ExpressionKind::Apply { operator, args, .. } = &expression.kind else {
        return expression.clone();
    };
    let [left, right] = args.as_slice() else {
        return expression.clone();
    };
    let regrouping = Regrouping {
        expression,
        operator: lookup_operator(operator),
        right: right.clone(),
        end: get_end(expression),
    };
    match regrouping.attach(
        left,
        is_same_position(get_start(left), get_start(expression)),
    ) {
        Grouping::Attached(regrouped) => regrouped,
        Grouping::Reduced { .. } => expression.clone(),
    }
}

#[cfg(test)]
mod tests {
    // Each case regroups the body of `X == <text>` as tla-front parses it, and expects what
    // `regroup.ts` gives under Bun for the TypeScript parser's body.
    use super::*;
    use tla_front::ast::ModuleUnit;
    use tla_front::parser::parse_tlapm_module;

    fn show(expression: &Expression) -> String {
        let at = expression
            .location
            .range
            .as_ref()
            .map_or_else(String::new, |range| {
                format!(
                    "@{}:{}-{}:{}",
                    range.start.line, range.start.column, range.end.line, range.end.column
                )
            });
        let (name, operands) = match &expression.kind {
            ExpressionKind::Apply { operator, args, .. } => (operator.to_string(), args.clone()),
            ExpressionKind::Identifier { name, .. } => return name.to_string(),
            ExpressionKind::Always(inner) => ("Always".to_owned(), vec![inner.clone()]),
            ExpressionKind::Eventually(inner) => ("Eventually".to_owned(), vec![inner.clone()]),
            ExpressionKind::Enabled(inner) => ("Enabled".to_owned(), vec![inner.clone()]),
            ExpressionKind::Unchanged(inner) => ("Unchanged".to_owned(), vec![inner.clone()]),
            ExpressionKind::Prime(inner) => ("Prime".to_owned(), vec![inner.clone()]),
            _ => return "?".to_owned(),
        };
        let operands: Vec<String> = operands.iter().map(|operand| show(operand)).collect();
        format!("({name} {}){at}", operands.join(" "))
    }

    #[test]
    fn regroups_as_the_typescript_does() {
        let cases = [
            (
                r"SUBSET S \ T",
                r"(\ (SUBSET S)@2:6-2:13 T)@2:6-2:17",
                r"(SUBSET (\ S T)@2:13-2:17)@2:6-2:17",
            ),
            (
                r"SUBSET S \cup T",
                r"(\cup (SUBSET S)@2:6-2:13 T)@2:6-2:20",
                r"(SUBSET (\cup S T)@2:13-2:20)@2:6-2:20",
            ),
            (
                r"UNION S \cup T",
                r"(\cup (UNION S)@2:6-2:12 T)@2:6-2:19",
                r"(UNION (\cup S T)@2:12-2:19)@2:6-2:19",
            ),
            (
                r"DOMAIN f \cup g",
                r"(\cup (DOMAIN f)@2:6-2:13 g)@2:6-2:20",
                "same",
            ),
            ("-a + b", "(+ (-. a)@2:6-2:7 b)@2:6-2:11", "same"),
            ("~a = b", "(~ (= a b)@2:7-2:11)@2:6-2:11", "-"),
            ("[]P => Q", "(=> (Always P)@2:6-2:8 Q)@2:6-2:13", "same"),
            ("<>P ~> Q", "(~> (Eventually P)@2:6-2:8 Q)@2:6-2:13", "same"),
            (
                r"ENABLED A \cdot B",
                r"(\cdot (Enabled A)@2:6-2:14 B)@2:6-2:22",
                r"(Enabled (\cdot A B)@2:14-2:22)@2:6-2:22",
            ),
            (
                r"UNCHANGED x \cup y",
                r"(\cup (Unchanged x)@2:6-2:16 y)@2:6-2:23",
                r"(Unchanged (\cup x y)@2:16-2:23)@2:6-2:23",
            ),
            (
                r"a \cup b \cup c",
                r"(\cup (\cup a b)@2:6-2:13 c)@2:6-2:20",
                "same",
            ),
            ("a + b * c", "(+ a (* b c)@2:10-2:14)@2:6-2:14", "same"),
            ("a * b + c", "(+ (* a b)@2:6-2:10 c)@2:6-2:14", "same"),
            (
                r"SUBSET SUBSET S \ T",
                r"(\ (SUBSET (SUBSET S)@2:13-2:20)@2:6-2:20 T)@2:6-2:24",
                r"(SUBSET (SUBSET (\ S T)@2:20-2:24)@2:13-2:24)@2:6-2:24",
            ),
            (
                r"(SUBSET S) \ T",
                r"(\ (SUBSET S)@2:7-2:14 T)@2:6-2:19",
                "same",
            ),
            (
                r"SUBSET (S) \ T",
                r"(\ (SUBSET S)@2:6-2:15 T)@2:6-2:19",
                r"(SUBSET (\ S T)@2:14-2:19)@2:6-2:19",
            ),
            (r"x' \cup y", r"(\cup (Prime x)@2:6-2:7 y)@2:6-2:14", "same"),
            ("a = b", "(= a b)@2:6-2:10", "same"),
        ];
        for (text, parsed, regrouped) in cases {
            let source = format!("---- MODULE M ----\nX == {text}\n====");
            let module = parse_tlapm_module(&source, None).expect("parses");
            let Some(ModuleUnit::Definition(definition)) = module.units.first() else {
                panic!("{text} is not a definition");
            };
            let body = &definition.body;
            assert_eq!(show(body), parsed, "{text}");
            let is_binary =
                matches!(&body.kind, ExpressionKind::Apply { args, .. } if args.len() == 2);
            let result = regroup(body);
            let shown = if !is_binary {
                assert!(Rc::ptr_eq(&result, body), "{text}");
                "-".to_owned()
            } else if Rc::ptr_eq(&result, body) {
                "same".to_owned()
            } else {
                show(&result)
            };
            assert_eq!(shown, regrouped, "{text}");
        }
    }
}
