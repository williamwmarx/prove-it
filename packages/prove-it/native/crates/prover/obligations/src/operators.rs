//! tlapm's Optable: each operator's precedence range and fixity, by every spelling it has.
//! A port of `src/obligations/operators.ts`.

use crate::expression::Builtin;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fixity {
    Nonfix,
    Prefix,
    Postfix,
    InfixLeft,
    InfixNon,
    InfixRight,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Operator {
    pub name: String,
    pub low: i32,
    pub high: i32,
    pub fixity: Fixity,
}

/// A row of the table: the name, the precedence range, the fixity and the other spellings.
type OperatorRow = (&'static str, i32, i32, Fixity, &'static [&'static str]);

const OPERATORS: &[OperatorRow] = &[
    ("=>", 1, 1, Fixity::InfixNon, &[]),
    ("<=>", 2, 2, Fixity::InfixNon, &["\\equiv"]),
    ("/\\", 3, 3, Fixity::InfixLeft, &["\\land"]),
    ("\\/", 3, 3, Fixity::InfixLeft, &["\\lor"]),
    ("~", 4, 4, Fixity::Prefix, &["\\neg", "\\lnot"]),
    ("=", 5, 5, Fixity::InfixNon, &[]),
    ("#", 5, 5, Fixity::InfixNon, &["/="]),
    ("SUBSET", 8, 8, Fixity::Prefix, &[]),
    ("UNION", 8, 8, Fixity::Prefix, &[]),
    ("DOMAIN", 9, 9, Fixity::Prefix, &[]),
    ("\\subseteq", 5, 5, Fixity::InfixNon, &[]),
    ("\\in", 5, 5, Fixity::InfixNon, &[]),
    ("\\notin", 5, 5, Fixity::InfixNon, &[]),
    ("\\", 8, 8, Fixity::InfixNon, &[]),
    ("\\cap", 8, 8, Fixity::InfixLeft, &["\\intersect"]),
    ("\\cup", 8, 8, Fixity::InfixLeft, &["\\union"]),
    ("\\X", 10, 13, Fixity::Prefix, &["\\times"]),
    ("'", 15, 15, Fixity::Postfix, &[]),
    ("~>", 2, 2, Fixity::InfixNon, &["\\leadsto"]),
    ("ENABLED", 4, 15, Fixity::Prefix, &[]),
    ("UNCHANGED", 4, 15, Fixity::Prefix, &[]),
    ("\\cdot", 5, 14, Fixity::InfixLeft, &[]),
    ("-+->", 2, 2, Fixity::InfixNon, &[]),
    ("[]", 4, 15, Fixity::Prefix, &[]),
    ("<>", 4, 15, Fixity::Prefix, &[]),
    ("^", 14, 14, Fixity::InfixNon, &[]),
    ("/", 13, 13, Fixity::InfixNon, &[]),
    ("*", 13, 13, Fixity::InfixLeft, &[]),
    ("-.", 12, 12, Fixity::Prefix, &["-"]),
    ("-", 11, 11, Fixity::InfixLeft, &[]),
    ("+", 10, 10, Fixity::InfixLeft, &[]),
    ("^+", 15, 15, Fixity::Postfix, &[]),
    ("^*", 15, 15, Fixity::Postfix, &[]),
    ("^#", 15, 15, Fixity::Postfix, &[]),
    ("<", 5, 5, Fixity::InfixNon, &[]),
    ("=<", 5, 5, Fixity::InfixNon, &["<=", "\\leq"]),
    (">", 5, 5, Fixity::InfixNon, &[]),
    (">=", 5, 5, Fixity::InfixNon, &["\\geq"]),
    ("...", 9, 9, Fixity::InfixNon, &[]),
    ("..", 9, 9, Fixity::InfixNon, &[]),
    ("|", 10, 11, Fixity::InfixLeft, &[]),
    ("||", 10, 11, Fixity::InfixLeft, &[]),
    ("&&", 13, 13, Fixity::InfixLeft, &[]),
    ("&", 13, 13, Fixity::InfixLeft, &[]),
    ("$$", 9, 13, Fixity::InfixLeft, &[]),
    ("$", 9, 13, Fixity::InfixLeft, &[]),
    ("??", 9, 13, Fixity::InfixLeft, &[]),
    ("%%", 10, 11, Fixity::InfixLeft, &[]),
    ("%", 10, 11, Fixity::InfixLeft, &["\\mod"]),
    ("##", 9, 13, Fixity::InfixLeft, &[]),
    ("++", 10, 10, Fixity::InfixLeft, &[]),
    ("--", 11, 11, Fixity::InfixLeft, &[]),
    ("**", 13, 13, Fixity::InfixLeft, &[]),
    ("//", 13, 13, Fixity::InfixNon, &[]),
    ("^^", 14, 14, Fixity::InfixNon, &[]),
    ("@@", 6, 6, Fixity::InfixLeft, &[]),
    ("!!", 9, 13, Fixity::InfixNon, &[]),
    ("|-", 5, 5, Fixity::InfixNon, &[]),
    ("|=", 5, 5, Fixity::InfixNon, &[]),
    ("-|", 5, 5, Fixity::InfixNon, &[]),
    ("=|", 5, 5, Fixity::InfixNon, &[]),
    ("<:", 7, 7, Fixity::InfixNon, &[]),
    (":>", 7, 7, Fixity::InfixNon, &[]),
    (":=", 5, 5, Fixity::InfixNon, &[]),
    ("::=", 5, 5, Fixity::InfixNon, &[]),
    ("(+)", 10, 10, Fixity::InfixLeft, &["\\oplus"]),
    ("(-)", 11, 11, Fixity::InfixLeft, &["\\ominus"]),
    ("(.)", 13, 13, Fixity::InfixLeft, &["\\odot"]),
    ("(/)", 13, 13, Fixity::InfixNon, &["\\oslash"]),
    ("(\\X)", 13, 13, Fixity::InfixLeft, &["\\otimes"]),
    ("\\uplus", 9, 13, Fixity::InfixLeft, &[]),
    ("\\sqcap", 9, 13, Fixity::InfixLeft, &[]),
    ("\\sqcup", 9, 13, Fixity::InfixLeft, &[]),
    ("\\div", 13, 13, Fixity::InfixNon, &[]),
    ("\\wr", 9, 14, Fixity::InfixNon, &[]),
    ("\\star", 13, 13, Fixity::InfixLeft, &[]),
    ("\\o", 13, 13, Fixity::InfixLeft, &["\\circ"]),
    ("\\bigcirc", 13, 13, Fixity::InfixLeft, &[]),
    ("\\bullet", 13, 13, Fixity::InfixLeft, &[]),
    ("\\prec", 5, 5, Fixity::InfixNon, &[]),
    ("\\succ", 5, 5, Fixity::InfixNon, &[]),
    ("\\preceq", 5, 5, Fixity::InfixNon, &[]),
    ("\\succeq", 5, 5, Fixity::InfixNon, &[]),
    ("\\sim", 5, 5, Fixity::InfixNon, &[]),
    ("\\simeq", 5, 5, Fixity::InfixNon, &[]),
    ("\\ll", 5, 5, Fixity::InfixNon, &[]),
    ("\\gg", 5, 5, Fixity::InfixNon, &[]),
    ("\\asymp", 5, 5, Fixity::InfixNon, &[]),
    ("\\subset", 5, 5, Fixity::InfixNon, &[]),
    ("\\supset", 5, 5, Fixity::InfixNon, &[]),
    ("\\supseteq", 5, 5, Fixity::InfixNon, &[]),
    ("\\approx", 5, 5, Fixity::InfixNon, &[]),
    ("\\cong", 5, 5, Fixity::InfixNon, &[]),
    ("\\sqsubset", 5, 5, Fixity::InfixNon, &[]),
    ("\\sqsubseteq", 5, 5, Fixity::InfixNon, &[]),
    ("\\sqsupset", 5, 5, Fixity::InfixNon, &[]),
    ("\\sqsupseteq", 5, 5, Fixity::InfixNon, &[]),
    ("\\doteq", 5, 5, Fixity::InfixNon, &[]),
    ("\\propto", 5, 5, Fixity::InfixNon, &[]),
];

fn get_nonfix(name: &str) -> Operator {
    Operator {
        name: name.to_owned(),
        low: -1,
        high: -1,
        fixity: Fixity::Nonfix,
    }
}

/// OCaml's Hashtbl.find returns the most recent binding, so later aliases win over earlier names:
/// the last row with the spelling is the one.
pub fn lookup_operator(name: &str) -> Operator {
    OPERATORS
        .iter()
        .rev()
        .find(|row| row.0 == name || row.4.contains(&name))
        .map_or_else(
            || get_nonfix(name),
            |&(row_name, low, high, fixity, _)| Operator {
                name: row_name.to_owned(),
                low,
                high,
                fixity,
            },
        )
}

fn get_standard_name(builtin: Builtin) -> Option<&'static str> {
    Some(match builtin {
        Builtin::Implies => "=>",
        Builtin::Equiv => "<=>",
        Builtin::Conj => "/\\",
        Builtin::Disj => "\\/",
        Builtin::Neg => "~",
        Builtin::Eq => "=",
        Builtin::Neq => "#",
        Builtin::SUBSET => "SUBSET",
        Builtin::UNION => "UNION",
        Builtin::DOMAIN => "DOMAIN",
        Builtin::Subseteq => "\\subseteq",
        Builtin::Mem => "\\in",
        Builtin::Notmem => "\\notin",
        Builtin::Setminus => "\\",
        Builtin::Cap => "\\cap",
        Builtin::Cup => "\\cup",
        Builtin::Prime | Builtin::StrongPrime => "'",
        Builtin::Leadsto => "~>",
        Builtin::ENABLED => "ENABLED",
        Builtin::UNCHANGED => "UNCHANGED",
        Builtin::Cdot => "\\cdot",
        Builtin::Actplus => "-+->",
        Builtin::BoxTrue | Builtin::BoxFalse => "[]",
        Builtin::Diamond => "<>",
        Builtin::Plus => "+",
        Builtin::Minus => "-",
        Builtin::Times => "*",
        Builtin::Ratio => "/",
        Builtin::Quotient => "\\div",
        Builtin::Remainder => "%",
        Builtin::Exp => "^",
        Builtin::Lteq => "=<",
        Builtin::Lt => "<",
        Builtin::Gteq => ">=",
        Builtin::Gt => ">",
        Builtin::Range => "..",
        Builtin::Cat => "\\o",
        Builtin::OneArg => ":>",
        Builtin::Extend => "@@",
        _ => return None,
    })
}

pub fn get_standard_form(builtin: Builtin) -> Operator {
    if builtin == Builtin::Divides {
        return Operator {
            name: "?|".to_owned(),
            low: 10,
            high: 11,
            fixity: Fixity::InfixNon,
        };
    }
    if builtin == Builtin::Uminus {
        return Operator {
            name: "-".to_owned(),
            ..lookup_operator("-.")
        };
    }
    get_standard_name(builtin).map_or_else(|| get_nonfix(builtin.name()), lookup_operator)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn show(operator: &Operator) -> String {
        format!(
            "{} {} {} {:?}",
            operator.name, operator.low, operator.high, operator.fixity
        )
    }

    #[test]
    fn looks_up_spellings_as_the_typescript_does() {
        let cases = [
            ("-", "- 11 11 InfixLeft"),
            ("-.", "-. 12 12 Prefix"),
            ("<=", "=< 5 5 InfixNon"),
            ("\\leq", "=< 5 5 InfixNon"),
            ("=<", "=< 5 5 InfixNon"),
            ("\\o", "\\o 13 13 InfixLeft"),
            ("\\circ", "\\o 13 13 InfixLeft"),
            ("\\X", "\\X 10 13 Prefix"),
            ("\\times", "\\X 10 13 Prefix"),
            ("\\land", "/\\ 3 3 InfixLeft"),
            ("/=", "# 5 5 InfixNon"),
            ("\\mod", "% 10 11 InfixLeft"),
            ("(\\X)", "(\\X) 13 13 InfixLeft"),
            ("\\otimes", "(\\X) 13 13 InfixLeft"),
            ("foo", "foo -1 -1 Nonfix"),
            ("", " -1 -1 Nonfix"),
            ("\\propto", "\\propto 5 5 InfixNon"),
            ("=>", "=> 1 1 InfixNon"),
        ];
        for (name, expected) in cases {
            assert_eq!(show(&lookup_operator(name)), expected, "{name}");
        }
    }

    #[test]
    fn gives_standard_forms_as_the_typescript_does() {
        let cases = [
            (Builtin::Divides, "?| 10 11 InfixNon"),
            (Builtin::Uminus, "- 12 12 Prefix"),
            (Builtin::Minus, "- 11 11 InfixLeft"),
            (Builtin::Implies, "=> 1 1 InfixNon"),
            (Builtin::Prime, "' 15 15 Postfix"),
            (Builtin::StrongPrime, "' 15 15 Postfix"),
            (Builtin::BoxFalse, "[] 4 15 Prefix"),
            (Builtin::Cat, "\\o 13 13 InfixLeft"),
            (Builtin::Lteq, "=< 5 5 InfixNon"),
            (Builtin::Setminus, "\\ 8 8 InfixNon"),
            (Builtin::Nat, "Nat -1 -1 Nonfix"),
            (Builtin::TRUE, "TRUE -1 -1 Nonfix"),
            (Builtin::Seq, "Seq -1 -1 Nonfix"),
            (Builtin::Extend, "@@ 6 6 InfixLeft"),
            (Builtin::OneArg, ":> 7 7 InfixNon"),
            (Builtin::Remainder, "% 10 11 InfixLeft"),
            (Builtin::Quotient, "\\div 13 13 InfixNon"),
        ];
        for (builtin, expected) in cases {
            assert_eq!(show(&get_standard_form(builtin)), expected, "{builtin:?}");
        }
    }
}
