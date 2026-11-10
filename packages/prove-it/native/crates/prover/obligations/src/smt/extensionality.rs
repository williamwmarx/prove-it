//! Standardize.set_extensionality_visitor: an equality of sets where it may need proving triggers
//! the set extensionality axiom, through TrigEq. A port of `src/prover/smt/extensionality.ts`.

use crate::expression::is_js_space;
use crate::smt::format::{
    CAP, CUP, FUN_SET, INT_RANGE, SEQ, SET_MINUS, SUBSET, TRIG_EQ, UNION, get_closing, slice,
    step_over,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Polarity {
    Positive,
    Negative,
    Neither,
}

// The head of a set equality whose polarity keeps it from triggering set extensionality unless a
// cast encloses it: (?trigger triggered kept).
const UNRESOLVED_TRIGGER: &str = "?trigger";

const SET_HEADS: [&str; 8] = [UNION, SUBSET, CUP, CAP, SET_MINUS, INT_RANGE, FUN_SET, SEQ];

/// Where `prefix\d+` ends when it matches at the start of `text`.
fn has_numbered(text: &str, prefix: &str) -> Option<usize> {
    let rest = text.strip_prefix(prefix)?;
    let digits = rest.len()
        - rest
            .trim_start_matches(|other: char| other.is_ascii_digit())
            .len();
    (digits > 0).then_some(prefix.len() + digits)
}

// Standardize.is_set: the applications of constructors whose values are sets. Standardize leaves
// BOOLEAN, STRING, Int, and Nat as bare symbols, which is_set doesn't match.
fn is_set_term(text: &str) -> bool {
    let is_head_end = |other: char| is_js_space(other) || other == '(' || other == ')';
    let unparenthesized = text.strip_prefix('(').unwrap_or(text);
    let head_length = unparenthesized
        .find(is_head_end)
        .unwrap_or(unparenthesized.len());
    // `^\(?([^\s()]+)`: without a head after the parenthesis, the parenthesis can't be the head.
    let head = if head_length > 0 {
        &unparenthesized[..head_length]
    } else {
        ""
    };
    if SET_HEADS.contains(&head) {
        return true;
    }
    let Some(rest) = head.strip_prefix("smt__TLA____") else {
        return false;
    };
    has_numbered(rest, "SetEnum__").is_some()
        || has_numbered(rest, "SetSt__flatnd__").is_some()
        || has_numbered(rest, "SetOf__")
            .is_some_and(|end| has_numbered(&rest[end..], "__flatnd__").is_some())
        || has_numbered(rest, "Product__").is_some()
        || rest.starts_with("RecordSet__")
}

// Picks the triggered or the kept form of each unresolved set equality in text.
pub fn resolve_triggers(text: &str, is_triggered: bool) -> String {
    let opening = format!("({UNRESOLVED_TRIGGER} ");
    let mut resolved = String::with_capacity(text.len());
    let mut text = text;
    while let Some(start) = text.find(&opening) {
        let triggered_start = start + opening.len();
        let triggered_end = step_over(text, get_closing(text, triggered_start));
        let kept_start = step_over(text, triggered_end);
        let kept_end = step_over(text, get_closing(text, kept_start));
        let chosen = if is_triggered {
            slice(text, triggered_start, triggered_end)
        } else {
            slice(text, kept_start, kept_end)
        };
        resolved.push_str(slice(text, 0, start));
        resolved.push_str(chosen);
        text = slice(text, step_over(text, kept_end), text.len());
    }
    resolved.push_str(text);
    resolved
}

// The equality, or disequality, of two Idv terms at a polarity.
pub fn get_equality(left: &str, right: &str, polarity: Polarity, is_negated: bool) -> String {
    let triggered = format!("({TRIG_EQ} {left} {right})");
    let kept = if is_negated {
        format!("(distinct {left} {right})")
    } else {
        format!("(= {left} {right})")
    };
    if !is_set_term(left) && !is_set_term(right) {
        return kept;
    }
    let text = if is_negated {
        format!("(not {triggered})")
    } else {
        triggered
    };
    // A cast around the equality may still trigger it, so both forms wait for resolveTriggers.
    let unresolved = if is_negated {
        Polarity::Positive
    } else {
        Polarity::Negative
    };
    if polarity == unresolved {
        format!("({UNRESOLVED_TRIGGER} {text} {kept})")
    } else {
        text
    }
}

// Expected values from running the TypeScript.
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resolves_triggers() {
        assert_eq!(resolve_triggers("(?trigger (a) (b))", true), "(a)");
        assert_eq!(resolve_triggers("(?trigger (a) (b))", false), "(b)");
        assert_eq!(
            resolve_triggers(
                "pre (?trigger (not (T a b)) (distinct a b)) mid (?trigger (T c d) (= c d)) post",
                true
            ),
            "pre (not (T a b)) mid (T c d) post"
        );
        assert_eq!(
            resolve_triggers(
                "pre (?trigger (not (T a b)) (distinct a b)) mid (?trigger (T c d) (= c d)) post",
                false
            ),
            "pre (distinct a b) mid (= c d) post"
        );
        assert_eq!(
            resolve_triggers("(f (?trigger (T (?trigger (U) (V)) x) (= y z)))", true),
            "(f (T (?trigger (U) (V)) x))"
        );
        assert_eq!(
            resolve_triggers("(f (?trigger (T (?trigger (U) (V)) x) (= y z)))", false),
            "(f (= y z))"
        );
        assert_eq!(resolve_triggers("(?trigger x y)", true), "x");
        assert_eq!(resolve_triggers("(?trigger x y)", false), "y");
        assert_eq!(resolve_triggers("(?trigger \u{e9} y) z", true), "\u{e9} z");
        assert_eq!(resolve_triggers("(?trigger \u{e9} y) z", false), "y z");
        assert_eq!(resolve_triggers("(?trigger (a)", true), "(a)");
        assert_eq!(resolve_triggers("(?trigger (a)", false), "");
        assert_eq!(
            resolve_triggers("\u{e9} (?trigger (\u{e9}) (\u{fc}))\u{e9}", true),
            "\u{e9} (\u{e9})\u{e9}"
        );
        assert_eq!(
            resolve_triggers("\u{e9} (?trigger (\u{e9}) (\u{fc}))\u{e9}", false),
            "\u{e9} (\u{fc})\u{e9}"
        );
        assert_eq!(resolve_triggers("none", true), "none");
        assert_eq!(resolve_triggers("none", false), "none");
    }

    #[test]
    fn builds_equalities() {
        assert_eq!(
            get_equality("(smt__TLA____Cup a b)", "y", Polarity::Positive, false),
            "(smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____Cup a b) y)"
        );
        assert_eq!(
            get_equality("(smt__TLA____Cup a b)", "y", Polarity::Positive, true),
            "(?trigger (not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____Cup a b) y)) (distinct (smt__TLA____Cup a b) y))"
        );
        assert_eq!(
            get_equality("(smt__TLA____Cup a b)", "y", Polarity::Negative, false),
            "(?trigger (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____Cup a b) y) (= (smt__TLA____Cup a b) y))"
        );
        assert_eq!(
            get_equality("(smt__TLA____Cup a b)", "y", Polarity::Negative, true),
            "(not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____Cup a b) y))"
        );
        assert_eq!(
            get_equality("(smt__TLA____Cup a b)", "y", Polarity::Neither, false),
            "(smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____Cup a b) y)"
        );
        assert_eq!(
            get_equality("(smt__TLA____Cup a b)", "y", Polarity::Neither, true),
            "(not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____Cup a b) y))"
        );
        assert_eq!(get_equality("x", "y", Polarity::Positive, false), "(= x y)");
        assert_eq!(
            get_equality("x", "y", Polarity::Positive, true),
            "(distinct x y)"
        );
        assert_eq!(get_equality("x", "y", Polarity::Negative, false), "(= x y)");
        assert_eq!(
            get_equality("x", "y", Polarity::Negative, true),
            "(distinct x y)"
        );
        assert_eq!(get_equality("x", "y", Polarity::Neither, false), "(= x y)");
        assert_eq!(
            get_equality("x", "y", Polarity::Neither, true),
            "(distinct x y)"
        );
        assert_eq!(
            get_equality("smt__TLA____SetEnum__0", "y", Polarity::Positive, false),
            "(smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__TLA____SetEnum__0 y)"
        );
        assert_eq!(
            get_equality("smt__TLA____SetEnum__0", "y", Polarity::Positive, true),
            "(?trigger (not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__TLA____SetEnum__0 y)) (distinct smt__TLA____SetEnum__0 y))"
        );
        assert_eq!(
            get_equality("smt__TLA____SetEnum__0", "y", Polarity::Negative, false),
            "(?trigger (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__TLA____SetEnum__0 y) (= smt__TLA____SetEnum__0 y))"
        );
        assert_eq!(
            get_equality("smt__TLA____SetEnum__0", "y", Polarity::Negative, true),
            "(not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__TLA____SetEnum__0 y))"
        );
        assert_eq!(
            get_equality("smt__TLA____SetEnum__0", "y", Polarity::Neither, false),
            "(smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__TLA____SetEnum__0 y)"
        );
        assert_eq!(
            get_equality("smt__TLA____SetEnum__0", "y", Polarity::Neither, true),
            "(not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__TLA____SetEnum__0 y))"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____SetOf__2__flatnd__3 a b)",
                "y",
                Polarity::Positive,
                false
            ),
            "(smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____SetOf__2__flatnd__3 a b) y)"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____SetOf__2__flatnd__3 a b)",
                "y",
                Polarity::Positive,
                true
            ),
            "(?trigger (not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____SetOf__2__flatnd__3 a b) y)) (distinct (smt__TLA____SetOf__2__flatnd__3 a b) y))"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____SetOf__2__flatnd__3 a b)",
                "y",
                Polarity::Negative,
                false
            ),
            "(?trigger (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____SetOf__2__flatnd__3 a b) y) (= (smt__TLA____SetOf__2__flatnd__3 a b) y))"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____SetOf__2__flatnd__3 a b)",
                "y",
                Polarity::Negative,
                true
            ),
            "(not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____SetOf__2__flatnd__3 a b) y))"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____SetOf__2__flatnd__3 a b)",
                "y",
                Polarity::Neither,
                false
            ),
            "(smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____SetOf__2__flatnd__3 a b) y)"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____SetOf__2__flatnd__3 a b)",
                "y",
                Polarity::Neither,
                true
            ),
            "(not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____SetOf__2__flatnd__3 a b) y))"
        );
        assert_eq!(
            get_equality("(smt__TLA____SetOf__x)", "y", Polarity::Positive, false),
            "(= (smt__TLA____SetOf__x) y)"
        );
        assert_eq!(
            get_equality("(smt__TLA____SetOf__x)", "y", Polarity::Positive, true),
            "(distinct (smt__TLA____SetOf__x) y)"
        );
        assert_eq!(
            get_equality("(smt__TLA____SetOf__x)", "y", Polarity::Negative, false),
            "(= (smt__TLA____SetOf__x) y)"
        );
        assert_eq!(
            get_equality("(smt__TLA____SetOf__x)", "y", Polarity::Negative, true),
            "(distinct (smt__TLA____SetOf__x) y)"
        );
        assert_eq!(
            get_equality("(smt__TLA____SetOf__x)", "y", Polarity::Neither, false),
            "(= (smt__TLA____SetOf__x) y)"
        );
        assert_eq!(
            get_equality("(smt__TLA____SetOf__x)", "y", Polarity::Neither, true),
            "(distinct (smt__TLA____SetOf__x) y)"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____RecordSet__a__b x)",
                "y",
                Polarity::Positive,
                false
            ),
            "(smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____RecordSet__a__b x) y)"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____RecordSet__a__b x)",
                "y",
                Polarity::Positive,
                true
            ),
            "(?trigger (not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____RecordSet__a__b x) y)) (distinct (smt__TLA____RecordSet__a__b x) y))"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____RecordSet__a__b x)",
                "y",
                Polarity::Negative,
                false
            ),
            "(?trigger (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____RecordSet__a__b x) y) (= (smt__TLA____RecordSet__a__b x) y))"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____RecordSet__a__b x)",
                "y",
                Polarity::Negative,
                true
            ),
            "(not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____RecordSet__a__b x) y))"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____RecordSet__a__b x)",
                "y",
                Polarity::Neither,
                false
            ),
            "(smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____RecordSet__a__b x) y)"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____RecordSet__a__b x)",
                "y",
                Polarity::Neither,
                true
            ),
            "(not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____RecordSet__a__b x) y))"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____Product__2 a b)",
                "y",
                Polarity::Positive,
                false
            ),
            "(smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____Product__2 a b) y)"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____Product__2 a b)",
                "y",
                Polarity::Positive,
                true
            ),
            "(?trigger (not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____Product__2 a b) y)) (distinct (smt__TLA____Product__2 a b) y))"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____Product__2 a b)",
                "y",
                Polarity::Negative,
                false
            ),
            "(?trigger (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____Product__2 a b) y) (= (smt__TLA____Product__2 a b) y))"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____Product__2 a b)",
                "y",
                Polarity::Negative,
                true
            ),
            "(not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____Product__2 a b) y))"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____Product__2 a b)",
                "y",
                Polarity::Neither,
                false
            ),
            "(smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____Product__2 a b) y)"
        );
        assert_eq!(
            get_equality("(smt__TLA____Product__2 a b)", "y", Polarity::Neither, true),
            "(not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____Product__2 a b) y))"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____SetSt__flatnd__1 a)",
                "y",
                Polarity::Positive,
                false
            ),
            "(smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____SetSt__flatnd__1 a) y)"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____SetSt__flatnd__1 a)",
                "y",
                Polarity::Positive,
                true
            ),
            "(?trigger (not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____SetSt__flatnd__1 a) y)) (distinct (smt__TLA____SetSt__flatnd__1 a) y))"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____SetSt__flatnd__1 a)",
                "y",
                Polarity::Negative,
                false
            ),
            "(?trigger (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____SetSt__flatnd__1 a) y) (= (smt__TLA____SetSt__flatnd__1 a) y))"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____SetSt__flatnd__1 a)",
                "y",
                Polarity::Negative,
                true
            ),
            "(not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____SetSt__flatnd__1 a) y))"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____SetSt__flatnd__1 a)",
                "y",
                Polarity::Neither,
                false
            ),
            "(smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____SetSt__flatnd__1 a) y)"
        );
        assert_eq!(
            get_equality(
                "(smt__TLA____SetSt__flatnd__1 a)",
                "y",
                Polarity::Neither,
                true
            ),
            "(not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____SetSt__flatnd__1 a) y))"
        );
        assert_eq!(
            get_equality("( x)", "y", Polarity::Positive, false),
            "(= ( x) y)"
        );
        assert_eq!(
            get_equality("( x)", "y", Polarity::Positive, true),
            "(distinct ( x) y)"
        );
        assert_eq!(
            get_equality("( x)", "y", Polarity::Negative, false),
            "(= ( x) y)"
        );
        assert_eq!(
            get_equality("( x)", "y", Polarity::Negative, true),
            "(distinct ( x) y)"
        );
        assert_eq!(
            get_equality("( x)", "y", Polarity::Neither, false),
            "(= ( x) y)"
        );
        assert_eq!(
            get_equality("( x)", "y", Polarity::Neither, true),
            "(distinct ( x) y)"
        );
        assert_eq!(
            get_equality("smt__TLA____Seq", "y", Polarity::Positive, false),
            "(smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__TLA____Seq y)"
        );
        assert_eq!(
            get_equality("smt__TLA____Seq", "y", Polarity::Positive, true),
            "(?trigger (not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__TLA____Seq y)) (distinct smt__TLA____Seq y))"
        );
        assert_eq!(
            get_equality("smt__TLA____Seq", "y", Polarity::Negative, false),
            "(?trigger (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__TLA____Seq y) (= smt__TLA____Seq y))"
        );
        assert_eq!(
            get_equality("smt__TLA____Seq", "y", Polarity::Negative, true),
            "(not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__TLA____Seq y))"
        );
        assert_eq!(
            get_equality("smt__TLA____Seq", "y", Polarity::Neither, false),
            "(smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__TLA____Seq y)"
        );
        assert_eq!(
            get_equality("smt__TLA____Seq", "y", Polarity::Neither, true),
            "(not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__TLA____Seq y))"
        );
        assert_eq!(
            get_equality("(smt__TLA____SetEnum__ a)", "y", Polarity::Positive, false),
            "(= (smt__TLA____SetEnum__ a) y)"
        );
        assert_eq!(
            get_equality("(smt__TLA____SetEnum__ a)", "y", Polarity::Positive, true),
            "(distinct (smt__TLA____SetEnum__ a) y)"
        );
        assert_eq!(
            get_equality("(smt__TLA____SetEnum__ a)", "y", Polarity::Negative, false),
            "(= (smt__TLA____SetEnum__ a) y)"
        );
        assert_eq!(
            get_equality("(smt__TLA____SetEnum__ a)", "y", Polarity::Negative, true),
            "(distinct (smt__TLA____SetEnum__ a) y)"
        );
        assert_eq!(
            get_equality("(smt__TLA____SetEnum__ a)", "y", Polarity::Neither, false),
            "(= (smt__TLA____SetEnum__ a) y)"
        );
        assert_eq!(
            get_equality("(smt__TLA____SetEnum__ a)", "y", Polarity::Neither, true),
            "(distinct (smt__TLA____SetEnum__ a) y)"
        );
        assert_eq!(
            get_equality("((smt__TLA____Cup a b))", "y", Polarity::Positive, false),
            "(= ((smt__TLA____Cup a b)) y)"
        );
        assert_eq!(
            get_equality("((smt__TLA____Cup a b))", "y", Polarity::Positive, true),
            "(distinct ((smt__TLA____Cup a b)) y)"
        );
        assert_eq!(
            get_equality("((smt__TLA____Cup a b))", "y", Polarity::Negative, false),
            "(= ((smt__TLA____Cup a b)) y)"
        );
        assert_eq!(
            get_equality("((smt__TLA____Cup a b))", "y", Polarity::Negative, true),
            "(distinct ((smt__TLA____Cup a b)) y)"
        );
        assert_eq!(
            get_equality("((smt__TLA____Cup a b))", "y", Polarity::Neither, false),
            "(= ((smt__TLA____Cup a b)) y)"
        );
        assert_eq!(
            get_equality("((smt__TLA____Cup a b))", "y", Polarity::Neither, true),
            "(distinct ((smt__TLA____Cup a b)) y)"
        );
        assert_eq!(
            get_equality("(smt__TLA____Cupx a)", "y", Polarity::Positive, false),
            "(= (smt__TLA____Cupx a) y)"
        );
        assert_eq!(
            get_equality("(smt__TLA____Cupx a)", "y", Polarity::Positive, true),
            "(distinct (smt__TLA____Cupx a) y)"
        );
        assert_eq!(
            get_equality("(smt__TLA____Cupx a)", "y", Polarity::Negative, false),
            "(= (smt__TLA____Cupx a) y)"
        );
        assert_eq!(
            get_equality("(smt__TLA____Cupx a)", "y", Polarity::Negative, true),
            "(distinct (smt__TLA____Cupx a) y)"
        );
        assert_eq!(
            get_equality("(smt__TLA____Cupx a)", "y", Polarity::Neither, false),
            "(= (smt__TLA____Cupx a) y)"
        );
        assert_eq!(
            get_equality("(smt__TLA____Cupx a)", "y", Polarity::Neither, true),
            "(distinct (smt__TLA____Cupx a) y)"
        );
    }
}
