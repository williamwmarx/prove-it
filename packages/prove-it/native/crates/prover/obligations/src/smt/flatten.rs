//! encode/n_flatten.ml: each application of a second-order construct becomes a fresh first-order
//! symbol, declared with its axioms before the fact that uses it. A port of
//! `src/prover/smt/flatten.ts`.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::smt::format::{declare, format_name, get_closing, is_js_space, slice, step_over};
use crate::smt::table::Axiom;

/// The axioms of a flattened symbol: given its name and the keys of the axioms collected so far.
pub type GetAxioms = Rc<dyn Fn(&str, &HashSet<String>) -> Vec<Axiom>>;

// A symbol that Flatten introduces, with the text tlapm's collect pass visits for its
// higher-order arguments.
pub struct Flattened {
    pub symbol: String,
    pub kind: String,
    pub visit: String,
    /// What `getLines` needs: the raw name, the arity and the axioms, which an omitted symbol
    /// doesn't have.
    lines: Option<(String, usize, GetAxioms)>,
}

impl Flattened {
    pub fn get_lines(&self, axioms: &HashSet<String>) -> Vec<String> {
        let Some((raw, arity, get_axioms)) = &self.lines else {
            return Vec::new();
        };
        let mut lines = vec![declare(&self.symbol, *arity, "Idv", "Idv")];
        lines.extend(get_axioms(&self.symbol, axioms).iter().map(|entry| {
            format!(
                "(assert (! {} :named |{} {raw}|))",
                remove_unprimable(entry.formula.as_deref().unwrap_or("")),
                entry.label
            )
        }));
        lines
    }
}

// A fact that tlapm encodes, so its symbols bring their axioms, but leaves out of the text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OmittedFact {
    pub omitted: String,
}

pub enum Entry {
    Text(String),
    Flattened(Rc<Flattened>),
    Omitted(OmittedFact),
}

// A bound variable's placeholder: its name and its depth, which the printer names in scope.
pub fn get_variable(name: &str, depth: usize) -> String {
    format!("{name}#{depth}")
}

/// `getDepth`: the number after the last `#`. The placeholders `getVariable` makes end in digits;
/// for any other text, where `Number` would give `NaN`, this gives 0.
pub fn get_depth(variable: &str) -> usize {
    let start = variable.rfind('#').map_or(0, |index| index + 1);
    let digits = &variable[start..];
    if digits.is_empty() {
        0
    } else {
        digits.parse().unwrap_or(0)
    }
}

// The head that marks the Unprimable WITNESS wraps around its witness, which Prep never removes:
// (?unprimable term). Flatten.compare_expr tells it apart, and the printed text drops it.
pub const UNPRIMABLE: &str = "?unprimable";

pub fn remove_unprimable(text: &str) -> String {
    let opening = format!("({UNPRIMABLE} ");
    let mut removed = String::with_capacity(text.len());
    let mut text = text;
    while let Some(start) = text.find(&opening) {
        let end = get_closing(text, start);
        removed.push_str(slice(text, 0, start));
        removed.push_str(&remove_unprimable(slice(text, start + opening.len(), end)));
        text = slice(text, step_over(text, end), text.len());
    }
    removed.push_str(text);
    removed
}

// Flatten.compare_expr: an application matches an earlier one with the same higher-order
// arguments, whatever the variables bound outside them. It can't compare quantifiers or
// conditionals, so an argument with one matches nothing.
fn get_flat_key(text: &str, depth: usize) -> Option<String> {
    if ["(forall ", "(exists ", "(ite "]
        .iter()
        .any(|opening| text.contains(opening))
    {
        return None;
    }
    // `/[^\s()]+#(\d+)/g`: in each run of other characters, the longest prefix that a `#` and
    // digits follow, through all the digits.
    let mut key = String::with_capacity(text.len());
    let mut index = 0;
    while let Some(tail) = text.get(index..).filter(|tail| !tail.is_empty()) {
        let run_length = tail
            .find(|other: char| is_js_space(other) || other == '(' || other == ')')
            .unwrap_or(tail.len());
        if run_length == 0 {
            let separator = tail.chars().next()?;
            key.push(separator);
            index += separator.len_utf8();
            continue;
        }
        let run = &tail[..run_length];
        let found = run.char_indices().rev().find(|(position, character)| {
            *character == '#'
                && *position > 0
                && run[position + 1..].starts_with(|next: char| next.is_ascii_digit())
        });
        let Some((hash, _)) = found else {
            key.push_str(run);
            index += run_length;
            continue;
        };
        let digits_end = run[hash + 1..]
            .find(|other: char| !other.is_ascii_digit())
            .map_or(run_length, |offset| hash + 1 + offset);
        let number: f64 = run[hash + 1..digits_end].parse().ok()?;
        let depth = depth as f64;
        if number < depth {
            key.push('#');
        } else {
            key.push_str(&format!("#{}", number - depth));
        }
        index += digits_end;
    }
    Some(key)
}

// Where an application occurs: its depth of bound variables, and whether it's in a fact that
// Smtlib leaves out, which Flatten doesn't enter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Site {
    pub depth: usize,
    pub is_omitted: bool,
}

/// The symbols a flattener introduced, by symbol, in the order they were first set.
#[derive(Default)]
pub struct FlattenedSymbols {
    entries: Vec<Rc<Flattened>>,
    positions: HashMap<String, usize>,
}

impl FlattenedSymbols {
    pub fn get(&self, symbol: &str) -> Option<&Rc<Flattened>> {
        self.positions
            .get(symbol)
            .and_then(|position| self.entries.get(*position))
    }

    fn len(&self) -> usize {
        self.entries.len()
    }

    fn set(&mut self, flat: Rc<Flattened>) {
        match self.positions.get(&flat.symbol) {
            Some(position) => self.entries[*position] = flat,
            None => {
                self.positions
                    .insert(flat.symbol.clone(), self.entries.len());
                self.entries.push(flat);
            }
        }
    }
}

// The state of Flatten.main over one obligation: its blueprint count, which init_bp_count resets
// for each obligation, and the symbols it introduced.
#[derive(Default)]
pub struct Flattener {
    pub flattened: FlattenedSymbols,
    flat_keys: HashMap<String, Rc<Flattened>>,
    blueprints: usize,
    // The symbols that the fact being encoded introduces, declared before it.
    introduced: Vec<Rc<Flattened>>,
}

pub fn create_flattener() -> Flattener {
    Flattener::default()
}

impl Flattener {
    /// `flatten`; `name` defaults to `TLA__<kind>`.
    pub fn flatten(
        &mut self,
        kind: &str,
        visit: &str,
        site: Site,
        get_axioms: GetAxioms,
        arity: usize,
        name: Option<&str>,
    ) -> String {
        let name = name.map_or_else(|| format!("TLA__{kind}"), str::to_string);
        // Flatten.find_hoapp skips a second-order ASSUME, so the application stays and only
        // N_axiomatize.collect, which runs before Flatten, visits it.
        if site.is_omitted {
            let symbol = format_name(&format!("{name}_omitted_{}", self.flattened.len()));
            self.flattened.set(Rc::new(Flattened {
                symbol: symbol.clone(),
                kind: kind.to_string(),
                visit: remove_unprimable(visit),
                lines: None,
            }));
            return symbol;
        }
        let key = get_flat_key(&format!("{name} {visit}"), site.depth);
        // Flatten.new_bp_id counts every application, even one that reuses an earlier symbol.
        self.blueprints += 1;
        if let Some(known) = key.as_ref().and_then(|key| self.flat_keys.get(key)) {
            return known.symbol.clone();
        }
        let raw = format!("{name}_flatnd_{}", self.blueprints);
        let symbol = format_name(&raw);
        let flat = Rc::new(Flattened {
            symbol: symbol.clone(),
            kind: kind.to_string(),
            visit: remove_unprimable(visit),
            lines: Some((raw, arity, get_axioms)),
        });
        if let Some(key) = key {
            self.flat_keys.insert(key, Rc::clone(&flat));
        }
        self.flattened.set(Rc::clone(&flat));
        self.introduced.push(flat);
        symbol
    }

    pub fn take_introduced(&mut self) -> Vec<Rc<Flattened>> {
        std::mem::take(&mut self.introduced)
    }
}

// Expected values from running the TypeScript.
#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::format::to_strings;
    use crate::smt::instances::{get_function_axioms, get_set_st_axioms};
    use crate::smt::table::{axiom, get_axiom_key};

    #[test]
    fn names_variables() {
        assert_eq!(get_variable("x", 3), "x#3");
        assert_eq!(get_depth("x#12"), 12);
        assert_eq!(get_depth("x#"), 0);
        assert_eq!(get_depth("a#b#7"), 7);
        assert_eq!(get_depth("42"), 42);
    }

    #[test]
    fn removes_unprimable() {
        assert_eq!(
            remove_unprimable("(f (?unprimable (g (?unprimable y))) z)"),
            "(f (g y) z)"
        );
        assert_eq!(remove_unprimable("(?unprimable x)"), "x");
        assert_eq!(remove_unprimable("(?unprimable (a b)"), "(a b)");
        assert_eq!(remove_unprimable("no"), "no");
        assert_eq!(
            remove_unprimable("(?unprimable \u{e9}) (?unprimable q)"),
            "\u{e9} q"
        );
    }

    #[test]
    fn flattens_applications() {
        assert_eq!(
            {
                let mut flattener = create_flattener();
                let symbols = [
                    flattener.flatten(
                        "SetSt",
                        "x#0 (P x#0 y#5)",
                        Site {
                            depth: 1,
                            is_omitted: false,
                        },
                        Rc::new(|symbol: &str, _axioms: &HashSet<String>| {
                            get_set_st_axioms(symbol, &to_strings(&["y#5"]), "(P x#0 y#5)", "x#0")
                        }),
                        2,
                        None,
                    ),
                    flattener.flatten(
                        "SetSt",
                        "x#0 (P x#0 y#6)",
                        Site {
                            depth: 2,
                            is_omitted: false,
                        },
                        Rc::new(|symbol: &str, _axioms: &HashSet<String>| {
                            get_set_st_axioms(symbol, &to_strings(&["y#5"]), "(P x#0 y#6)", "x#0")
                        }),
                        2,
                        None,
                    ),
                    flattener.flatten(
                        "SetSt",
                        "x#0 (P x#0 y#5)",
                        Site {
                            depth: 2,
                            is_omitted: false,
                        },
                        Rc::new(|symbol: &str, _axioms: &HashSet<String>| {
                            get_set_st_axioms(symbol, &to_strings(&["y#5"]), "(P x#0 y#5)", "x#0")
                        }),
                        2,
                        None,
                    ),
                    flattener.flatten(
                        "SetSt",
                        "x#0 (forall ((a Idv)) a)",
                        Site {
                            depth: 0,
                            is_omitted: false,
                        },
                        Rc::new(|symbol: &str, _axioms: &HashSet<String>| {
                            get_set_st_axioms(symbol, &to_strings(&["y#5"]), "(Q x#0)", "x#0")
                        }),
                        1,
                        None,
                    ),
                    flattener.flatten(
                        "SetSt",
                        "x#0 (forall ((a Idv)) a)",
                        Site {
                            depth: 0,
                            is_omitted: false,
                        },
                        Rc::new(|symbol: &str, _axioms: &HashSet<String>| {
                            get_set_st_axioms(symbol, &to_strings(&["y#5"]), "(Q x#0)", "x#0")
                        }),
                        1,
                        None,
                    ),
                    flattener.flatten(
                        "Choose",
                        "x#0 (?unprimable (R x#0))",
                        Site {
                            depth: 0,
                            is_omitted: true,
                        },
                        Rc::new(|symbol: &str, _axioms: &HashSet<String>| {
                            get_set_st_axioms(symbol, &to_strings(&["y#5"]), "(Q x#0)", "x#0")
                        }),
                        0,
                        None,
                    ),
                    flattener.flatten(
                        "FunFcn",
                        "x#0 (?unprimable (R x#0 w#3))",
                        Site {
                            depth: 1,
                            is_omitted: false,
                        },
                        Rc::new(|symbol: &str, axioms: &HashSet<String>| {
                            get_function_axioms(
                                symbol,
                                &[],
                                "(?unprimable (R x#0 w#3))",
                                "x#0",
                                axioms,
                            )
                        }),
                        1,
                        Some("TLA__Fcn"),
                    ),
                    flattener.flatten(
                        "SetSt",
                        "q#1#7a#2",
                        Site {
                            depth: 1,
                            is_omitted: false,
                        },
                        Rc::new(|symbol: &str, _axioms: &HashSet<String>| {
                            get_set_st_axioms(symbol, &to_strings(&["y#5"]), "(P x#0)", "x#0")
                        }),
                        1,
                        None,
                    ),
                ];
                let keys = HashSet::from([get_axiom_key(&axiom("FunTyping", vec![], None, None))]);
                let introduced = flattener.take_introduced();
                let lines = introduced
                    .iter()
                    .map(|flat| {
                        format!(
                            "{}:{}:{}\n{}",
                            flat.symbol,
                            flat.kind,
                            flat.visit,
                            flat.get_lines(&keys).join("\n")
                        )
                    })
                    .collect::<Vec<_>>()
                    .join("\n\n");
                let map = flattener
                    .flattened
                    .entries
                    .iter()
                    .map(|flat| {
                        format!(
                            "{}:{}:{}:{}",
                            flat.symbol,
                            flat.kind,
                            flat.visit,
                            flat.get_lines(&HashSet::new()).len()
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(";");
                let found = symbols
                    .iter()
                    .all(|symbol| flattener.flattened.get(symbol).is_some());
                format!(
                    "{}\n---\n{lines}\n---\n{map}\n---\n{}\n{found}",
                    symbols.join(";"),
                    flattener.take_introduced().len()
                )
            },
            "smt__TLA____SetSt__flatnd__1;smt__TLA____SetSt__flatnd__1;smt__TLA____SetSt__flatnd__3;smt__TLA____SetSt__flatnd__4;smt__TLA____SetSt__flatnd__5;smt__TLA____Choose__omitted__4;smt__TLA____Fcn__flatnd__6;smt__TLA____SetSt__flatnd__7\n---\nsmt__TLA____SetSt__flatnd__1:SetSt:x#0 (P x#0 y#5)\n(declare-fun smt__TLA____SetSt__flatnd__1 (Idv Idv) Idv)\n(assert (! (forall ((y#5 Idv) (a Idv) (x Idv)) (! (= (smt__TLA____Mem x (smt__TLA____SetSt__flatnd__1 a y#5)) (and (smt__TLA____Mem x a) (P x y#5))) :pattern ((smt__TLA____Mem x (smt__TLA____SetSt__flatnd__1 a y#5))) :pattern ((smt__TLA____Mem x a) (smt__TLA____SetSt__flatnd__1 a y#5)))) :named |SetStDef TLA__SetSt_flatnd_1|))\n\nsmt__TLA____SetSt__flatnd__3:SetSt:x#0 (P x#0 y#5)\n(declare-fun smt__TLA____SetSt__flatnd__3 (Idv Idv) Idv)\n(assert (! (forall ((y#5 Idv) (a Idv) (x Idv)) (! (= (smt__TLA____Mem x (smt__TLA____SetSt__flatnd__3 a y#5)) (and (smt__TLA____Mem x a) (P x y#5))) :pattern ((smt__TLA____Mem x (smt__TLA____SetSt__flatnd__3 a y#5))) :pattern ((smt__TLA____Mem x a) (smt__TLA____SetSt__flatnd__3 a y#5)))) :named |SetStDef TLA__SetSt_flatnd_3|))\n\nsmt__TLA____SetSt__flatnd__4:SetSt:x#0 (forall ((a Idv)) a)\n(declare-fun smt__TLA____SetSt__flatnd__4 (Idv) Idv)\n(assert (! (forall ((y#5 Idv) (a Idv) (x Idv)) (! (= (smt__TLA____Mem x (smt__TLA____SetSt__flatnd__4 a y#5)) (and (smt__TLA____Mem x a) (Q x))) :pattern ((smt__TLA____Mem x (smt__TLA____SetSt__flatnd__4 a y#5))) :pattern ((smt__TLA____Mem x a) (smt__TLA____SetSt__flatnd__4 a y#5)))) :named |SetStDef TLA__SetSt_flatnd_4|))\n\nsmt__TLA____SetSt__flatnd__5:SetSt:x#0 (forall ((a Idv)) a)\n(declare-fun smt__TLA____SetSt__flatnd__5 (Idv) Idv)\n(assert (! (forall ((y#5 Idv) (a Idv) (x Idv)) (! (= (smt__TLA____Mem x (smt__TLA____SetSt__flatnd__5 a y#5)) (and (smt__TLA____Mem x a) (Q x))) :pattern ((smt__TLA____Mem x (smt__TLA____SetSt__flatnd__5 a y#5))) :pattern ((smt__TLA____Mem x a) (smt__TLA____SetSt__flatnd__5 a y#5)))) :named |SetStDef TLA__SetSt_flatnd_5|))\n\nsmt__TLA____Fcn__flatnd__6:FunFcn:x#0 (R x#0 w#3)\n(declare-fun smt__TLA____Fcn__flatnd__6 (Idv) Idv)\n(assert (! (forall ((a Idv)) (! (smt__TLA____FunIsafcn (smt__TLA____Fcn__flatnd__6 a)) :pattern ((smt__TLA____Fcn__flatnd__6 a)))) :named |FunConstrIsafcn TLA__Fcn_flatnd_6|))\n(assert (! (forall ((a Idv)) (! (= (smt__TLA____FunDom (smt__TLA____Fcn__flatnd__6 a)) a) :pattern ((smt__TLA____Fcn__flatnd__6 a)))) :named |FunDomDef TLA__Fcn_flatnd_6|))\n(assert (! (forall ((a Idv) (x Idv)) (! (=> (smt__TLA____Mem x a) (= (smt__TLA____FunApp (smt__TLA____Fcn__flatnd__6 a) x) (R x w#3))) :pattern ((smt__TLA____FunApp (smt__TLA____Fcn__flatnd__6 a) x)) :pattern ((smt__TLA____Mem x a) (smt__TLA____Fcn__flatnd__6 a)))) :named |FunAppDef TLA__Fcn_flatnd_6|))\n(assert (! (forall ((a Idv) (b Idv)) (! (=> (forall ((x Idv)) (=> (smt__TLA____Mem x a) (smt__TLA____Mem (R x w#3) b))) (smt__TLA____Mem (smt__TLA____Fcn__flatnd__6 a) (smt__TLA____FunSet a b))) :pattern ((smt__TLA____Fcn__flatnd__6 a) (smt__TLA____FunSet a b)))) :named |FunTyping TLA__Fcn_flatnd_6|))\n\nsmt__TLA____SetSt__flatnd__7:SetSt:q#1#7a#2\n(declare-fun smt__TLA____SetSt__flatnd__7 (Idv) Idv)\n(assert (! (forall ((y#5 Idv) (a Idv) (x Idv)) (! (= (smt__TLA____Mem x (smt__TLA____SetSt__flatnd__7 a y#5)) (and (smt__TLA____Mem x a) (P x))) :pattern ((smt__TLA____Mem x (smt__TLA____SetSt__flatnd__7 a y#5))) :pattern ((smt__TLA____Mem x a) (smt__TLA____SetSt__flatnd__7 a y#5)))) :named |SetStDef TLA__SetSt_flatnd_7|))\n---\nsmt__TLA____SetSt__flatnd__1:SetSt:x#0 (P x#0 y#5):2;smt__TLA____SetSt__flatnd__3:SetSt:x#0 (P x#0 y#5):2;smt__TLA____SetSt__flatnd__4:SetSt:x#0 (forall ((a Idv)) a):2;smt__TLA____SetSt__flatnd__5:SetSt:x#0 (forall ((a Idv)) a):2;smt__TLA____Choose__omitted__4:Choose:x#0 (R x#0):0;smt__TLA____Fcn__flatnd__6:FunFcn:x#0 (R x#0 w#3):4;smt__TLA____SetSt__flatnd__7:SetSt:q#1#7a#2:2\n---\n0\ntrue"
        );
    }
}
