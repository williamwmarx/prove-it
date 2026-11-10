//! Ported from Isabelle2025's Pure/name.ML and the name bumping of Pure/General/symbol.ML.
//! Copyright (c) 1986-2025 University of Cambridge, Technische Universitaet Muenchen, and
//! contributors, see LICENSE.

use super::table::{Table, empty_table, fast_string_ord, has_key, lookup_table, update_table};
use super::term::Name;

/// Symbol.explode: \<name> symbols count as one symbol.
fn explode_symbols(text: &str) -> Vec<&str> {
    let mut symbols = Vec::new();
    let mut rest = text;
    while let Some(first) = rest.chars().next() {
        let length = rest
            .strip_prefix("\\<")
            .and_then(|after| {
                let name = after.strip_prefix('^').unwrap_or(after);
                let end = name
                    .find(|symbol: char| {
                        !(symbol.is_ascii_alphanumeric() || symbol == '_' || symbol == '\'')
                    })
                    .unwrap_or(name.len());
                name[end..]
                    .starts_with('>')
                    .then(|| rest.len() - name.len() + end + 1)
            })
            .unwrap_or(first.len_utf8());
        symbols.push(&rest[..length]);
        rest = &rest[length..];
    }
    symbols
}

fn is_raw_symbolic(symbol: &str) -> bool {
    symbol.starts_with("\\<") && !symbol.starts_with("\\<^")
}

fn is_quasi(symbol: &str) -> bool {
    symbol == "_" || symbol == "'"
}

fn is_symbolic_end(reversed: &[&str]) -> bool {
    if reversed.is_empty() {
        return false;
    }
    if reversed.len() > 1 && reversed[1] == "\\<^sub>" {
        return true;
    }
    if reversed[0] == "'" {
        return is_symbolic_end(&reversed[1..]);
    }
    is_raw_symbolic(reversed[0])
}

pub fn bump_init(text: &str) -> String {
    let mut reversed = explode_symbols(text);
    reversed.reverse();
    if is_symbolic_end(&reversed) {
        format!("{text}'")
    } else {
        format!("{text}a")
    }
}

const LETTERS: [&str; 26] = [
    "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s",
    "t", "u", "v", "w", "x", "y", "z",
];

pub fn bump_string(text: &str) -> String {
    let symbols = explode_symbols(text);
    let mut suffix_start = symbols.len();
    while suffix_start > 0 && is_quasi(symbols[suffix_start - 1]) {
        suffix_start -= 1;
    }
    let mut reversed = symbols[..suffix_start].to_vec();
    reversed.reverse();
    let bumped = if is_symbolic_end(&reversed) {
        [vec!["'"], reversed].concat()
    } else {
        // bump: each leading z becomes a, then the next letter below z goes up by one, or an a goes
        // in front of the next symbol.
        let zs = reversed.iter().take_while(|symbol| **symbol == "z").count();
        let mut bumped = vec!["a"; zs];
        match reversed.get(zs) {
            None => bumped.push("a"),
            Some(symbol) => {
                let code = if symbol.len() == 1 {
                    symbol.as_bytes()[0]
                } else {
                    0
                };
                if (b'a'..=b'y').contains(&code) {
                    bumped.push(LETTERS[(code - b'a' + 1) as usize]);
                    bumped.extend_from_slice(&reversed[zs + 1..]);
                } else {
                    bumped.push("a");
                    bumped.extend_from_slice(&reversed[zs..]);
                }
            }
        }
        bumped
    };
    let mut result: String = bumped.iter().rev().copied().collect();
    result.extend(symbols[suffix_start..].iter().copied());
    result
}

fn clean_index(name: &str) -> (&str, usize) {
    let base = name.trim_end_matches('_');
    (base, name.len() - base.len())
}

pub fn clean_name(name: &str) -> &str {
    clean_index(name).0
}

/// Name.context: the declared names with their latest renaming. The TypeScript's Map is only
/// looked up, never iterated, so a persistent table keeps its contents.
pub type NameContext = Table<Name, Option<Name>>;

pub fn declare_name(name: &str, context: &NameContext) -> NameContext {
    let clean: Name = clean_name(name).into();
    if has_key(context, &clean) {
        return context.clone();
    }
    update_table(context, clean, None)
}

pub fn empty_name_context() -> NameContext {
    ["", "'"]
        .iter()
        .fold(empty_table(fast_string_ord), |context, name| {
            update_table(&context, (*name).into(), None)
        })
}

pub fn make_name_context(names: &[Name]) -> NameContext {
    names.iter().fold(empty_name_context(), |context, name| {
        declare_name(name, &context)
    })
}

/// Name.variant: a name distinct from the declared ones, keeping a suffix of underscores.
pub fn variant_name(name: &str, context: &NameContext) -> (Name, NameContext) {
    let (base, count) = clean_index(name);
    if !has_key(context, &base.into()) {
        return (
            format!("{base}{}", "_".repeat(count)).into(),
            declare_name(base, context),
        );
    }
    let initial = bump_init(base);
    let mut current: Name = initial.as_str().into();
    while let Some(renamed) = lookup_table(context, &current) {
        current = bump_string(renamed.as_ref().unwrap_or(&current)).into();
    }
    let renamed = if clean_name(&initial) == clean_name(&current) {
        context.clone()
    } else {
        update_table(
            context,
            clean_name(&initial).into(),
            Some(clean_name(&current).into()),
        )
    };
    (
        format!("{current}{}", "_".repeat(count)).into(),
        declare_name(&current, &renamed),
    )
}

pub fn variant_names(names: &[Name], context: &NameContext) -> Vec<Name> {
    let mut current = context.clone();
    names
        .iter()
        .map(|name| {
            let (variant, next) = variant_name(name, &current);
            current = next;
            variant
        })
        .collect()
}

pub fn variant_list(used: &[Name], names: &[Name]) -> Vec<Name> {
    variant_names(names, &make_name_context(used))
}

/// Name.is_bound and Name.bound: the names of loose bound variables in nets and printing.
/// Name.is_bound: the names the simplifier gives the free variables standing for bound ones.
pub fn is_bound_name(name: &str) -> bool {
    name.starts_with(':')
}

pub fn bound_name(index: i32) -> Name {
    format!(":{:0>3}", index.to_string()).into()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn names(texts: &[&str]) -> Vec<Name> {
        texts.iter().map(|text| (*text).into()).collect()
    }

    // Expected values from running name.ts with bun.
    #[test]
    fn explodes_symbols() {
        assert_eq!(
            explode_symbols("a\\<alpha>\\<^sub>1\\<b c>\\<>"),
            [
                "a",
                "\\<alpha>",
                "\\<^sub>",
                "1",
                "\\",
                "<",
                "b",
                " ",
                "c",
                ">",
                "\\<>"
            ]
        );
    }

    #[test]
    fn bumps() {
        let cases = [
            ("x", "xa", "y"),
            ("z", "za", "aa"),
            ("az", "aza", "ba"),
            ("zz_", "zz_a", "aaa_"),
            ("x'", "x'a", "y'"),
            ("A", "Aa", "Aa"),
            ("\\<alpha>", "\\<alpha>'", "\\<alpha>'"),
            ("x\\<^sub>1", "x\\<^sub>1'", "x\\<^sub>1'"),
            ("", "a", "a"),
            ("ya", "yaa", "yb"),
            ("x9", "x9a", "x9a"),
        ];
        for (text, init, bumped) in cases {
            assert_eq!(bump_init(text), init, "bump_init {text}");
            assert_eq!(bump_string(text), bumped, "bump_string {text}");
        }
    }

    #[test]
    fn variants() {
        assert_eq!(
            variant_list(
                &names(&["x", "xa", "y_"]),
                &names(&["x", "x", "x_", "y", "", "'", "xa", "u", "u"]),
            ),
            names(&["xb", "xc", "xd_", "ya", "a", "'a", "xaa", "u", "ua"])
        );
        let (variant, context) = variant_name("x__", &make_name_context(&names(&["x"])));
        assert_eq!(&*variant, "xa__");
        assert_eq!(&*variant_name("x", &context).0, "xb");
    }

    #[test]
    fn names_bounds() {
        assert_eq!(&*bound_name(7), ":007");
        assert_eq!(&*bound_name(1234), ":1234");
        assert!(is_bound_name(":007"));
    }
}
