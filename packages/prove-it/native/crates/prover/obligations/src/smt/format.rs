//! backend/smtlib.ml's names and the SMT-LIB terms the encoding builds. A port of
//! `src/prover/smt/format.ts`.
//!
//! Text positions here are byte offsets into the Rust string, where the TypeScript counts UTF-16
//! code units; each offset only slices the text it was found in, so the slices are the same.

use crate::expression::Builtin;

// Smtlib.format_smt: spells out each special character, then doubles each underscore.
const SPELLED: [(char, &str); 22] = [
    ('\\', "backslash_"),
    ('+', "plussign_"),
    ('-', "hyphen_"),
    ('*', "asterisk_"),
    ('/', "slash_"),
    ('%', "percentsign_"),
    ('^', "circumflexaccent_"),
    ('&', "ampersand_"),
    ('@', "atsign_"),
    ('#', "pound_"),
    ('$', "dollarsign_"),
    ('(', "leftparenthesis_"),
    (')', "rightparenthesis_"),
    ('|', "verticalbar_"),
    ('.', "period_"),
    (':', "colon_"),
    ('?', "questionmark_"),
    ('!', "exclamationmark_"),
    ('<', "lessthansign_"),
    ('>', "greaterthansign_"),
    ('=', "equalsign_"),
    (' ', "space_"),
];

pub fn format_name(name: &str) -> String {
    let mut spelled = String::with_capacity(name.len());
    for character in name.chars() {
        match SPELLED.iter().find(|entry| entry.0 == character) {
            Some(entry) => spelled.push_str(entry.1),
            None => spelled.push(character),
        }
    }
    format!("smt__{}", spelled.replace('_', "__"))
}

/// `formatName("TLA__")`.
const TLA_PREFIX: &str = "smt__TLA____";

pub fn tla(name: &str) -> String {
    format_name(&format!("TLA__{name}"))
}

// The builtin a symbol that tla names stands for, or undefined for any other symbol.
pub fn get_tla_name(symbol: &str) -> Option<String> {
    let rest = symbol.strip_prefix(TLA_PREFIX)?.replace("__", "_");
    // The spelled words, tried in order at each position as the regular expression's alternatives.
    let mut unspelled = String::with_capacity(rest.len());
    let mut index = 0;
    while let Some(tail) = rest.get(index..).filter(|tail| !tail.is_empty()) {
        match SPELLED.iter().find(|entry| tail.starts_with(entry.1)) {
            Some(entry) => {
                unspelled.push(entry.0);
                index += entry.1.len();
            }
            None => {
                let character = tail.chars().next()?;
                unspelled.push(character);
                index += character.len_utf8();
            }
        }
    }
    Some(unspelled)
}

pub const MEM: &str = "smt__TLA____Mem";
pub const SET_EXT_TRIGGER: &str = "smt__TLA____SetExtTrigger";
pub const SUBSET_EQ: &str = "smt__TLA____SubsetEq";
pub const CUP: &str = "smt__TLA____Cup";
pub const CAP: &str = "smt__TLA____Cap";
pub const SET_MINUS: &str = "smt__TLA____SetMinus";
pub const SUBSET: &str = "smt__TLA____Subset";
pub const UNION: &str = "smt__TLA____Union";
pub const TT_IDV: &str = "smt__TLA____Tt__Idv";
pub const CAST_BOOL: &str = "smt__TLA____Cast__Bool";
pub const BOOL_SET: &str = "smt__TLA____BoolSet";
pub const STR_SET: &str = "smt__TLA____StrSet";
pub const INT_SET: &str = "smt__TLA____IntSet";
pub const NAT_SET: &str = "smt__TLA____NatSet";
pub const CAST_INT: &str = "smt__TLA____Cast__Int";
pub const PROJ_INT: &str = "smt__TLA____Proj__Int";
pub const INT_LTEQ: &str = "smt__TLA____IntLteq";
pub const INT_RANGE: &str = "smt__TLA____IntRange";
pub const FUN_APP: &str = "smt__TLA____FunApp";
pub const FUN_DOM: &str = "smt__TLA____FunDom";
pub const FUN_ISAFCN: &str = "smt__TLA____FunIsafcn";
pub const FUN_SET: &str = "smt__TLA____FunSet";
pub const FUN_EXCEPT: &str = "smt__TLA____FunExcept";
pub const TRIG_EQ: &str = "smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__";
pub const IS_SET_OF: &str = "smt__TLA____IsSetOf";
pub const SEQ: &str = "smt__TLA____Seq";
pub const LEN: &str = "smt__TLA____Len";
pub const CAT: &str = "smt__TLA____Cat";
pub const APPEND: &str = "smt__TLA____Append";
pub const HEAD: &str = "smt__TLA____Head";
pub const TAIL: &str = "smt__TLA____Tail";
pub const SUB_SEQ: &str = "smt__TLA____SubSeq";
pub const TUPLE_0: &str = "smt__TLA____Tuple__0";

/// The SMT symbol of each builtin that has one, in the TypeScript's order.
pub const BUILTIN_SYMBOLS: [(Builtin, &str); 22] = [
    (Builtin::Cup, CUP),
    (Builtin::Cap, CAP),
    (Builtin::Setminus, SET_MINUS),
    (Builtin::SUBSET, SUBSET),
    (Builtin::UNION, UNION),
    (Builtin::DOMAIN, FUN_DOM),
    (Builtin::Plus, "smt__TLA____IntPlus"),
    (Builtin::Minus, "smt__TLA____IntMinus"),
    (Builtin::Times, "smt__TLA____IntTimes"),
    (Builtin::Exp, "smt__TLA____IntExp"),
    (Builtin::Quotient, "smt__TLA____IntQuotient"),
    (Builtin::Remainder, "smt__TLA____IntRemainder"),
    (Builtin::Uminus, "smt__TLA____IntUminus"),
    (Builtin::Range, INT_RANGE),
    (Builtin::Seq, SEQ),
    (Builtin::Len, LEN),
    (Builtin::BSeq, "smt__TLA____BSeq"),
    (Builtin::Cat, CAT),
    (Builtin::Append, APPEND),
    (Builtin::Head, HEAD),
    (Builtin::Tail, TAIL),
    (Builtin::SubSeq, SUB_SEQ),
];

pub fn get_names(prefix: &str, count: usize) -> Vec<String> {
    (0..count)
        .map(|index| format!("{prefix}{}", index + 1))
        .collect()
}

/// `getBinders`; the TypeScript's default sort is `Idv`.
pub fn get_binders(variables: &[String], sort: &str) -> String {
    variables
        .iter()
        .map(|variable| format!("({variable} {sort})"))
        .collect::<Vec<_>>()
        .join(" ")
}

/// `forall`; the TypeScript's defaults are no patterns and the sort `Idv`.
pub fn forall(variables: &[String], body: &str, patterns: &[Vec<String>], sort: &str) -> String {
    if variables.is_empty() {
        return body.to_string();
    }
    let annotated = if patterns.is_empty() {
        body.to_string()
    } else {
        let patterns = patterns
            .iter()
            .map(|pattern| format!(":pattern ({})", pattern.join(" ")))
            .collect::<Vec<_>>()
            .join(" ");
        format!("(! {body} {patterns})")
    };
    format!("(forall ({}) {annotated})", get_binders(variables, sort))
}

pub fn conjoin(items: &[String]) -> String {
    match items {
        [] => "true".to_string(),
        [item] => item.clone(),
        _ => format!("(and {})", items.join(" ")),
    }
}

pub fn disjoin(items: &[String]) -> String {
    match items {
        [] => "false".to_string(),
        [item] => item.clone(),
        _ => format!("(or {})", items.join(" ")),
    }
}

pub fn call(symbol: &str, args: &[String]) -> String {
    if args.is_empty() {
        symbol.to_string()
    } else {
        format!("({symbol} {})", args.join(" "))
    }
}

/// `declare`; the TypeScript's default sorts are `Idv`.
pub fn declare(symbol: &str, arity: usize, sort: &str, arg_sort: &str) -> String {
    format!(
        "(declare-fun {symbol} ({}) {sort})",
        vec![arg_sort; arity].join(" ")
    )
}

// The index of the parenthesis that closes the one at from.
pub fn get_closing(text: &str, from: usize) -> usize {
    let mut depth = 0i64;
    for (index, byte) in text.bytes().enumerate().skip(from) {
        if byte == b'(' {
            depth += 1;
        }
        if byte == b')' {
            depth -= 1;
        }
        if depth == 0 {
            return index;
        }
    }
    text.len()
}

pub fn replace_token(text: &str, token: &str, replacement: &str) -> String {
    let mut replaced = String::with_capacity(text.len());
    let mut run = String::new();
    for character in text.chars() {
        if is_js_space(character) || character == '(' || character == ')' {
            replaced.push_str(if run == token { replacement } else { &run });
            run.clear();
            replaced.push(character);
        } else {
            run.push(character);
        }
    }
    replaced.push_str(if run == token { replacement } else { &run });
    replaced
}

/// JavaScript's `\s`: the characters a regular expression's `\s` matches.
pub(crate) fn is_js_space(character: char) -> bool {
    matches!(
        character,
        '\t' | '\n' | '\u{b}' | '\u{c}' | '\r' | ' ' | '\u{a0}' | '\u{1680}' | '\u{2000}'
            ..='\u{200a}'
                | '\u{2028}'
                | '\u{2029}'
                | '\u{202f}'
                | '\u{205f}'
                | '\u{3000}'
                | '\u{feff}'
    )
}

/// The offset just past the character at `index`, as the TypeScript's `index + 1` steps over one
/// code unit; past the end it is `index + 1`.
pub(crate) fn step_over(text: &str, index: usize) -> usize {
    text.get(index..)
        .and_then(|tail| tail.chars().next())
        .map_or(index + 1, |character| index + character.len_utf8())
}

/// The owned strings of a literal list, for the term builders that take `&[String]`.
pub(crate) fn to_strings(items: &[&str]) -> Vec<String> {
    items.iter().map(|item| item.to_string()).collect()
}

/// `text.slice(start, end)`, which clamps both offsets to the text.
pub(crate) fn slice(text: &str, start: usize, end: usize) -> &str {
    let end = end.min(text.len());
    let start = start.min(end);
    text.get(start..end).unwrap_or("")
}

// Expected values from running the TypeScript.
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn formats_names() {
        assert_eq!(format_name("x"), "smt__x");
        assert_eq!(format_name("TLA__Mem"), "smt__TLA____Mem");
        assert_eq!(
            format_name("a+b-c*d/e%f^g&h@i#j$k(l)m|n.o:p?q!r<s>t=u v\\w"),
            "smt__aplussign__bhyphen__casterisk__dslash__epercentsign__fcircumflexaccent__gampersand__hatsign__ipound__jdollarsign__kleftparenthesis__lrightparenthesis__mverticalbar__nperiod__ocolon__pquestionmark__qexclamationmark__rlessthansign__sgreaterthansign__tequalsign__uspace__vbackslash__w"
        );
        assert_eq!(format_name("\u{e9}_\u{fc}"), "smt__\u{e9}__\u{fc}");
        assert_eq!(format_name("\u{540d}\u{524d}"), "smt__\u{540d}\u{524d}");
        assert_eq!(format_name(""), "smt__");
        assert_eq!(format_name("__"), "smt______");
        assert_eq!(tla("SetEnum_3"), "smt__TLA____SetEnum__3");
        assert_eq!(
            tla("TrigEq_Set$Idv$"),
            "smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__"
        );
    }

    #[test]
    fn reads_tla_names() {
        assert_eq!(
            get_tla_name("smt__TLA____Mem").unwrap_or_else(|| "<none>".to_string()),
            "Mem"
        );
        assert_eq!(
            get_tla_name("smt__TLA____aplussign__b").unwrap_or_else(|| "<none>".to_string()),
            "a+b"
        );
        assert_eq!(
            get_tla_name("smt__TLA____Tuple__0").unwrap_or_else(|| "<none>".to_string()),
            "Tuple_0"
        );
        assert_eq!(
            get_tla_name("smt__TLA____x__y").unwrap_or_else(|| "<none>".to_string()),
            "x_y"
        );
        assert_eq!(
            get_tla_name("smt__x").unwrap_or_else(|| "<none>".to_string()),
            "<none>"
        );
        assert_eq!(
            get_tla_name("smt__TLA____\u{e9}pound__1").unwrap_or_else(|| "<none>".to_string()),
            "\u{e9}#1"
        );
        assert_eq!(
            get_tla_name("smt__TLA____plussign__x").unwrap_or_else(|| "<none>".to_string()),
            "+x"
        );
        assert_eq!(
            get_tla_name("smt__TLA____").unwrap_or_else(|| "<none>".to_string()),
            ""
        );
        assert_eq!(
            get_tla_name("smt__TLA____hyphen__x").unwrap_or_else(|| "<none>".to_string()),
            "-x"
        );
        assert_eq!(
            get_tla_name("smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__")
                .unwrap_or_else(|| "<none>".to_string()),
            "TrigEq_Set$Idv$"
        );
        assert_eq!(
            get_tla_name("smt__TLA____a___b").unwrap_or_else(|| "<none>".to_string()),
            "a__b"
        );
    }

    #[test]
    fn spells_the_constants() {
        assert_eq!(MEM, "smt__TLA____Mem");
        assert_eq!(SET_EXT_TRIGGER, "smt__TLA____SetExtTrigger");
        assert_eq!(SUBSET_EQ, "smt__TLA____SubsetEq");
        assert_eq!(CUP, "smt__TLA____Cup");
        assert_eq!(CAP, "smt__TLA____Cap");
        assert_eq!(SET_MINUS, "smt__TLA____SetMinus");
        assert_eq!(SUBSET, "smt__TLA____Subset");
        assert_eq!(UNION, "smt__TLA____Union");
        assert_eq!(TT_IDV, "smt__TLA____Tt__Idv");
        assert_eq!(CAST_BOOL, "smt__TLA____Cast__Bool");
        assert_eq!(BOOL_SET, "smt__TLA____BoolSet");
        assert_eq!(STR_SET, "smt__TLA____StrSet");
        assert_eq!(INT_SET, "smt__TLA____IntSet");
        assert_eq!(NAT_SET, "smt__TLA____NatSet");
        assert_eq!(CAST_INT, "smt__TLA____Cast__Int");
        assert_eq!(PROJ_INT, "smt__TLA____Proj__Int");
        assert_eq!(INT_LTEQ, "smt__TLA____IntLteq");
        assert_eq!(INT_RANGE, "smt__TLA____IntRange");
        assert_eq!(FUN_APP, "smt__TLA____FunApp");
        assert_eq!(FUN_DOM, "smt__TLA____FunDom");
        assert_eq!(FUN_ISAFCN, "smt__TLA____FunIsafcn");
        assert_eq!(FUN_SET, "smt__TLA____FunSet");
        assert_eq!(FUN_EXCEPT, "smt__TLA____FunExcept");
        assert_eq!(
            TRIG_EQ,
            "smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__"
        );
        assert_eq!(IS_SET_OF, "smt__TLA____IsSetOf");
        assert_eq!(SEQ, "smt__TLA____Seq");
        assert_eq!(LEN, "smt__TLA____Len");
        assert_eq!(CAT, "smt__TLA____Cat");
        assert_eq!(APPEND, "smt__TLA____Append");
        assert_eq!(HEAD, "smt__TLA____Head");
        assert_eq!(TAIL, "smt__TLA____Tail");
        assert_eq!(SUB_SEQ, "smt__TLA____SubSeq");
        assert_eq!(TUPLE_0, "smt__TLA____Tuple__0");
    }

    #[test]
    fn maps_builtins() {
        assert_eq!(
            BUILTIN_SYMBOLS
                .iter()
                .map(|entry| format!("{}={}", entry.0.name(), entry.1))
                .collect::<Vec<_>>()
                .join(";"),
            "Cup=smt__TLA____Cup;Cap=smt__TLA____Cap;Setminus=smt__TLA____SetMinus;SUBSET=smt__TLA____Subset;UNION=smt__TLA____Union;DOMAIN=smt__TLA____FunDom;Plus=smt__TLA____IntPlus;Minus=smt__TLA____IntMinus;Times=smt__TLA____IntTimes;Exp=smt__TLA____IntExp;Quotient=smt__TLA____IntQuotient;Remainder=smt__TLA____IntRemainder;Uminus=smt__TLA____IntUminus;Range=smt__TLA____IntRange;Seq=smt__TLA____Seq;Len=smt__TLA____Len;BSeq=smt__TLA____BSeq;Cat=smt__TLA____Cat;Append=smt__TLA____Append;Head=smt__TLA____Head;Tail=smt__TLA____Tail;SubSeq=smt__TLA____SubSeq"
        );
    }

    #[test]
    fn builds_terms() {
        assert_eq!(get_names("a", 0).join(","), "");
        assert_eq!(get_names("x", 3).join(","), "x1,x2,x3");
        assert_eq!(
            get_binders(&to_strings(&["a", "b"]), "Idv"),
            "(a Idv) (b Idv)"
        );
        assert_eq!(get_binders(&to_strings(&["i"]), "Int"), "(i Int)");
        assert_eq!(get_binders(&to_strings(&[]), "Idv"), "");
        assert_eq!(
            forall(&to_strings(&[]), "(p x)", &[to_strings(&["x"])], "Idv"),
            "(p x)"
        );
        assert_eq!(
            forall(&to_strings(&["x", "y"]), "(p x y)", &[], "Idv"),
            "(forall ((x Idv) (y Idv)) (p x y))"
        );
        assert_eq!(
            forall(
                &to_strings(&["x", "y"]),
                "(p x y)",
                &[to_strings(&["(f x)", "(g y)"]), to_strings(&["(h x y)"])],
                "Int"
            ),
            "(forall ((x Int) (y Int)) (! (p x y) :pattern ((f x) (g y)) :pattern ((h x y))))"
        );
        assert_eq!(conjoin(&to_strings(&[])), "true");
        assert_eq!(conjoin(&to_strings(&["a"])), "a");
        assert_eq!(conjoin(&to_strings(&["a", "b", "c"])), "(and a b c)");
        assert_eq!(disjoin(&to_strings(&[])), "false");
        assert_eq!(disjoin(&to_strings(&["a"])), "a");
        assert_eq!(disjoin(&to_strings(&["a", "b"])), "(or a b)");
        assert_eq!(call("f", &to_strings(&[])), "f");
        assert_eq!(call("f", &to_strings(&["a", "(g b)"])), "(f a (g b))");
        assert_eq!(declare("f", 0, "Idv", "Idv"), "(declare-fun f () Idv)");
        assert_eq!(
            declare("f", 2, "Bool", "Idv"),
            "(declare-fun f (Idv Idv) Bool)"
        );
        assert_eq!(declare("f", 1, "Idv", "Int"), "(declare-fun f (Int) Idv)");
    }

    #[test]
    fn finds_closings() {
        assert_eq!(get_closing("(a (b) c) d", 0), 8);
        assert_eq!(get_closing("(a (b", 0), 5);
        assert_eq!(get_closing("x(a)", 0), 0);
        assert_eq!(get_closing("(a)", 5), 3);
        assert_eq!(get_closing("x (a (b)) c", 2), 8);
        assert_eq!(get_closing("", 0), 0);
        assert_eq!(
            {
                let text = "(é (b)) x";
                slice(text, 0, get_closing(text, 0) + 1).to_string()
            },
            "(\u{e9} (b))"
        );
    }

    #[test]
    fn replaces_tokens() {
        assert_eq!(replace_token("(f x (g x) xx)", "x", "y"), "(f y (g y) xx)");
        assert_eq!(
            replace_token("\u{a0}x\u{2003}x\u{feff}x", "x", "(z w)"),
            "\u{a0}(z w)\u{2003}(z w)\u{feff}(z w)"
        );
        assert_eq!(replace_token("x", "x", "y"), "y");
        assert_eq!(replace_token("", "x", "y"), "");
        assert_eq!(replace_token("x\u{85}x", "x", "y"), "x\u{85}x");
        assert_eq!(replace_token("x\u{85}x", "x\u{85}x", "y"), "y");
        assert_eq!(replace_token("a#1 (a#1) a#12", "a#1", "q"), "q (q) a#12");
    }
}
