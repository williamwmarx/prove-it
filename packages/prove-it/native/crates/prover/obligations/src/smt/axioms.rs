//! encode/n_axioms.ml: the formulas of the axioms that depend on a count or on fields. A port of
//! `src/prover/smt/axioms.ts`.

use crate::errors::{ObligationError, Result};
use crate::smt::format::{
    CAST_INT, FUN_APP, FUN_DOM, FUN_EXCEPT, FUN_ISAFCN, LEN, MEM, SEQ, call, conjoin, disjoin,
    forall, get_names, tla, to_strings,
};
use crate::smt::table::{Axiom, AxiomArgument, TYPED_SYMBOLS, axiom};

// The arithmetic symbols with a Typing axiom: each one's SMT-LIB operator and arity.
pub const TYPED_OPERATORS: [(&str, &str, usize); 7] = [
    ("IntPlus", "+", 2),
    ("IntMinus", "-", 2),
    ("IntTimes", "*", 2),
    ("IntUminus", "-", 1),
    ("IntQuotient", "div", 2),
    ("IntRemainder", "mod", 2),
    ("IntLteq", "<=", 2),
];

/// `getTyping`. The TypeScript fails with a `TypeError` on a name without a Typing axiom, which
/// this reports as a bug.
pub fn get_typing(name: &str) -> Result<Axiom> {
    let (_, operator, arity) = TYPED_OPERATORS
        .iter()
        .find(|entry| entry.0 == name)
        .ok_or_else(ObligationError::assert_failure)?;
    let is_guarded = *operator == "div" || *operator == "mod";
    let variables = to_strings(if *arity == 1 {
        &["x1"]
    } else if is_guarded {
        &["x", "y"]
    } else {
        &["x1", "x2"]
    });
    let left = call(
        &tla(name),
        &variables
            .iter()
            .map(|variable| format!("({CAST_INT} {variable})"))
            .collect::<Vec<_>>(),
    );
    let right = if *operator == "<=" {
        format!("(<= {})", variables.join(" "))
    } else {
        format!("({CAST_INT} ({operator} {}))", variables.join(" "))
    };
    let equality = format!("(= {left} {right})");
    let typed = format!("T{name}");
    let index = TYPED_SYMBOLS
        .iter()
        .position(|symbol| *symbol == typed)
        .map_or(-1, |index| index as i64);
    Ok(axiom(
        "Typing",
        vec![AxiomArgument::Number(index)],
        Some(forall(
            &variables,
            &if is_guarded {
                format!("(=> (> y 0) {equality})")
            } else {
                equality
            },
            &[vec![left]],
            "Int",
        )),
        Some(format!("Typing {typed}")),
    ))
}

pub fn get_enumeration(count: usize) -> Vec<Axiom> {
    let symbol = tla(&format!("SetEnum_{count}"));
    let elements = get_names("a", count);
    let set = call(&symbol, &elements);
    let membership = format!("({MEM} x {set})");
    let elim = axiom(
        "EnumDefElim",
        vec![AxiomArgument::Number(count as i64)],
        Some(forall(
            &[elements.clone(), to_strings(&["x"])].concat(),
            &if count == 0 {
                format!("(not {membership})")
            } else {
                format!(
                    "(=> {membership} {})",
                    disjoin(
                        &elements
                            .iter()
                            .map(|element| format!("(= x {element})"))
                            .collect::<Vec<_>>()
                    )
                )
            },
            &[vec![membership.clone()]],
            "Idv",
        )),
        None,
    );
    if count == 0 {
        return vec![elim];
    }
    let intro = axiom(
        "EnumDefIntro",
        vec![AxiomArgument::Number(count as i64)],
        Some(forall(
            &elements,
            &conjoin(
                &elements
                    .iter()
                    .map(|element| format!("({MEM} {element} {set})"))
                    .collect::<Vec<_>>(),
            ),
            &[vec![set.clone()]],
            "Idv",
        )),
        None,
    );
    vec![intro, elim]
}

pub fn get_integers(count: usize) -> Vec<String> {
    (0..count)
        .map(|index| format!("({CAST_INT} {})", index + 1))
        .collect()
}

pub fn get_field_keys(fields: &[String]) -> Vec<String> {
    fields
        .iter()
        .map(|field| tla(&format!("StrLit_{field}")))
        .collect()
}

// TupExcept and RecExcept: updating one component of a tuple or record.
fn get_component_excepts(
    prefix: &str,
    args: &[AxiomArgument],
    symbol: &str,
    keys: &[String],
) -> Vec<Axiom> {
    let elements = get_names("x", keys.len());
    keys.iter()
        .enumerate()
        .map(|(index, key)| {
            let updated = format!("({FUN_EXCEPT} {} {key} x)", call(symbol, &elements));
            let replaced = elements
                .iter()
                .enumerate()
                .map(|(position, element)| {
                    if position == index {
                        "x".to_string()
                    } else {
                        element.clone()
                    }
                })
                .collect::<Vec<_>>();
            axiom(
                &format!("{prefix}Except"),
                [args.to_vec(), vec![AxiomArgument::Number(index as i64 + 1)]].concat(),
                Some(forall(
                    &[elements.clone(), to_strings(&["x"])].concat(),
                    &format!("(= {updated} {})", call(symbol, &replaced)),
                    &[vec![updated.clone()]],
                    "Idv",
                )),
                None,
            )
        })
        .collect()
}

pub fn get_tuple_excepts(count: usize) -> Vec<Axiom> {
    get_component_excepts(
        "Tup",
        &[AxiomArgument::Number(count as i64)],
        &tla(&format!("Tuple_{count}")),
        &get_integers(count),
    )
}

pub fn get_record_excepts(fields: &[String]) -> Vec<Axiom> {
    get_component_excepts(
        "Rec",
        &[AxiomArgument::Texts(fields.to_vec())],
        &tla(&format!("Record_{}", fields.join("_"))),
        &get_field_keys(fields),
    )
}

// TupIsafcn, TupDomDef and TupAppDef, or their Rec counterparts: a tuple or record is the
// function from its keys to its components. The empty tuple has no domain or components to define.
fn get_component_function(
    prefix: &str,
    args: &[AxiomArgument],
    symbol: &str,
    keys: &[String],
) -> Vec<Axiom> {
    let elements = get_names("x", keys.len());
    let value = call(symbol, &elements);
    let isafcn = axiom(
        &format!("{prefix}Isafcn"),
        args.to_vec(),
        Some(forall(
            &elements,
            &format!("({FUN_ISAFCN} {value})"),
            &[vec![value.clone()]],
            "Idv",
        )),
        None,
    );
    if keys.is_empty() {
        return vec![isafcn];
    }
    vec![
        isafcn,
        axiom(
            &format!("{prefix}DomDef"),
            args.to_vec(),
            Some(forall(
                &elements,
                &format!(
                    "(= ({FUN_DOM} {value}) {})",
                    call(&tla(&format!("SetEnum_{}", keys.len())), keys)
                ),
                &[vec![value.clone()]],
                "Idv",
            )),
            None,
        ),
        axiom(
            &format!("{prefix}AppDef"),
            args.to_vec(),
            Some(forall(
                &elements,
                &conjoin(
                    &keys
                        .iter()
                        .zip(&elements)
                        .map(|(key, element)| format!("(= ({FUN_APP} {value} {key}) {element})"))
                        .collect::<Vec<_>>(),
                ),
                &[vec![value.clone()]],
                "Idv",
            )),
            None,
        ),
    ]
}

pub fn get_tuple_axioms(count: usize, is_except: bool) -> Vec<Axiom> {
    let symbol = tla(&format!("Tuple_{count}"));
    let elements = get_names("x", count);
    let value = call(&symbol, &elements);
    let memberships = elements
        .iter()
        .map(|element| format!("({MEM} {element} a)"))
        .collect::<Vec<_>>();
    let mut axioms = get_component_function(
        "Tup",
        &[AxiomArgument::Number(count as i64)],
        &symbol,
        &get_integers(count),
    );
    axioms.push(axiom(
        "SeqTupTyping",
        vec![AxiomArgument::Number(count as i64)],
        Some(forall(
            &[to_strings(&["a"]), elements.clone()].concat(),
            &if count == 0 {
                format!("({MEM} {value} ({SEQ} a))")
            } else {
                format!("(=> {} ({MEM} {value} ({SEQ} a)))", conjoin(&memberships))
            },
            &[[memberships.clone(), vec![value.clone()]].concat()],
            "Idv",
        )),
        None,
    ));
    axioms.push(axiom(
        "SeqTupLen",
        vec![AxiomArgument::Number(count as i64)],
        Some(forall(
            &elements,
            &format!("(= ({LEN} {value}) ({CAST_INT} {count}))"),
            &[vec![value.clone()]],
            "Idv",
        )),
        None,
    ));
    if is_except {
        axioms.extend(get_tuple_excepts(count));
    }
    axioms
}

pub fn get_record_axioms(fields: &[String], is_except: bool) -> Vec<Axiom> {
    let mut axioms = get_component_function(
        "Rec",
        &[AxiomArgument::Texts(fields.to_vec())],
        &tla(&format!("Record_{}", fields.join("_"))),
        &get_field_keys(fields),
    );
    if is_except {
        axioms.extend(get_record_excepts(fields));
    }
    axioms
}

// The set of tuples or records whose components are in the given sets.
pub fn get_component_set(
    name: &str,
    args: &[AxiomArgument],
    set: &str,
    value: &str,
    keys: &[String],
    variable: &str,
) -> Vec<Axiom> {
    let sets = get_names("s", keys.len());
    let elements = get_names("x", keys.len());
    let members = call(set, &sets);
    let built = call(value, &elements);
    let projections = keys
        .iter()
        .map(|key| format!("({FUN_APP} {variable} {key})"))
        .collect::<Vec<_>>();
    let membership = format!("({MEM} {variable} {members})");
    vec![
        axiom(
            &format!("{name}Intro"),
            args.to_vec(),
            Some(forall(
                &[sets.clone(), elements.clone()].concat(),
                &format!(
                    "(=> {} ({MEM} {built} {members}))",
                    conjoin(
                        &elements
                            .iter()
                            .zip(&sets)
                            .map(|(element, set)| format!("({MEM} {element} {set})"))
                            .collect::<Vec<_>>()
                    )
                ),
                &[vec![built.clone(), members.clone()]],
                "Idv",
            )),
            None,
        ),
        axiom(
            &format!("{name}Elim"),
            args.to_vec(),
            Some(forall(
                &[sets.clone(), vec![variable.to_string()]].concat(),
                &format!(
                    "(=> {membership} {})",
                    conjoin(
                        &[
                            vec![format!("(= {variable} {})", call(value, &projections))],
                            projections
                                .iter()
                                .zip(&sets)
                                .map(|(projection, set)| format!("({MEM} {projection} {set})"))
                                .collect::<Vec<_>>(),
                        ]
                        .concat()
                    )
                ),
                &[vec![membership.clone()]],
                "Idv",
            )),
            None,
        ),
    ]
}

// Expected values from running the TypeScript.
#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::table::tests::show_axioms;

    #[test]
    fn types_operators() {
        assert_eq!(
            show_axioms(&[get_typing("IntPlus").unwrap()]),
            "Typing TIntPlus\nTyping [0]\n(forall ((x1 Int) (x2 Int)) (! (= (smt__TLA____IntPlus (smt__TLA____Cast__Int x1) (smt__TLA____Cast__Int x2)) (smt__TLA____Cast__Int (+ x1 x2))) :pattern ((smt__TLA____IntPlus (smt__TLA____Cast__Int x1) (smt__TLA____Cast__Int x2)))))"
        );
        assert_eq!(
            show_axioms(&[get_typing("IntMinus").unwrap()]),
            "Typing TIntMinus\nTyping [2]\n(forall ((x1 Int) (x2 Int)) (! (= (smt__TLA____IntMinus (smt__TLA____Cast__Int x1) (smt__TLA____Cast__Int x2)) (smt__TLA____Cast__Int (- x1 x2))) :pattern ((smt__TLA____IntMinus (smt__TLA____Cast__Int x1) (smt__TLA____Cast__Int x2)))))"
        );
        assert_eq!(
            show_axioms(&[get_typing("IntTimes").unwrap()]),
            "Typing TIntTimes\nTyping [3]\n(forall ((x1 Int) (x2 Int)) (! (= (smt__TLA____IntTimes (smt__TLA____Cast__Int x1) (smt__TLA____Cast__Int x2)) (smt__TLA____Cast__Int (* x1 x2))) :pattern ((smt__TLA____IntTimes (smt__TLA____Cast__Int x1) (smt__TLA____Cast__Int x2)))))"
        );
        assert_eq!(
            show_axioms(&[get_typing("IntUminus").unwrap()]),
            "Typing TIntUminus\nTyping [1]\n(forall ((x1 Int)) (! (= (smt__TLA____IntUminus (smt__TLA____Cast__Int x1)) (smt__TLA____Cast__Int (- x1))) :pattern ((smt__TLA____IntUminus (smt__TLA____Cast__Int x1)))))"
        );
        assert_eq!(
            show_axioms(&[get_typing("IntQuotient").unwrap()]),
            "Typing TIntQuotient\nTyping [4]\n(forall ((x Int) (y Int)) (! (=> (> y 0) (= (smt__TLA____IntQuotient (smt__TLA____Cast__Int x) (smt__TLA____Cast__Int y)) (smt__TLA____Cast__Int (div x y)))) :pattern ((smt__TLA____IntQuotient (smt__TLA____Cast__Int x) (smt__TLA____Cast__Int y)))))"
        );
        assert_eq!(
            show_axioms(&[get_typing("IntRemainder").unwrap()]),
            "Typing TIntRemainder\nTyping [5]\n(forall ((x Int) (y Int)) (! (=> (> y 0) (= (smt__TLA____IntRemainder (smt__TLA____Cast__Int x) (smt__TLA____Cast__Int y)) (smt__TLA____Cast__Int (mod x y)))) :pattern ((smt__TLA____IntRemainder (smt__TLA____Cast__Int x) (smt__TLA____Cast__Int y)))))"
        );
        assert_eq!(
            show_axioms(&[get_typing("IntLteq").unwrap()]),
            "Typing TIntLteq\nTyping [6]\n(forall ((x1 Int) (x2 Int)) (! (= (smt__TLA____IntLteq (smt__TLA____Cast__Int x1) (smt__TLA____Cast__Int x2)) (<= x1 x2)) :pattern ((smt__TLA____IntLteq (smt__TLA____Cast__Int x1) (smt__TLA____Cast__Int x2)))))"
        );
        assert_eq!(
            TYPED_OPERATORS
                .iter()
                .map(|entry| format!("{}={}/{}", entry.0, entry.1, entry.2))
                .collect::<Vec<_>>()
                .join(";"),
            "IntPlus=+/2;IntMinus=-/2;IntTimes=*/2;IntUminus=-/1;IntQuotient=div/2;IntRemainder=mod/2;IntLteq=<=/2"
        );
        assert!(get_typing("Bogus").is_err());
    }

    #[test]
    fn enumerates() {
        assert_eq!(
            show_axioms(&get_enumeration(0)),
            "EnumDefElim 0\nEnumDefElim [0]\n(forall ((x Idv)) (! (not (smt__TLA____Mem x smt__TLA____SetEnum__0)) :pattern ((smt__TLA____Mem x smt__TLA____SetEnum__0))))"
        );
        assert_eq!(
            show_axioms(&get_enumeration(1)),
            "EnumDefIntro 1\nEnumDefIntro [1]\n(forall ((a1 Idv)) (! (smt__TLA____Mem a1 (smt__TLA____SetEnum__1 a1)) :pattern ((smt__TLA____SetEnum__1 a1))))\n\nEnumDefElim 1\nEnumDefElim [1]\n(forall ((a1 Idv) (x Idv)) (! (=> (smt__TLA____Mem x (smt__TLA____SetEnum__1 a1)) (= x a1)) :pattern ((smt__TLA____Mem x (smt__TLA____SetEnum__1 a1)))))"
        );
        assert_eq!(
            show_axioms(&get_enumeration(3)),
            "EnumDefIntro 3\nEnumDefIntro [3]\n(forall ((a1 Idv) (a2 Idv) (a3 Idv)) (! (and (smt__TLA____Mem a1 (smt__TLA____SetEnum__3 a1 a2 a3)) (smt__TLA____Mem a2 (smt__TLA____SetEnum__3 a1 a2 a3)) (smt__TLA____Mem a3 (smt__TLA____SetEnum__3 a1 a2 a3))) :pattern ((smt__TLA____SetEnum__3 a1 a2 a3))))\n\nEnumDefElim 3\nEnumDefElim [3]\n(forall ((a1 Idv) (a2 Idv) (a3 Idv) (x Idv)) (! (=> (smt__TLA____Mem x (smt__TLA____SetEnum__3 a1 a2 a3)) (or (= x a1) (= x a2) (= x a3))) :pattern ((smt__TLA____Mem x (smt__TLA____SetEnum__3 a1 a2 a3)))))"
        );
    }

    #[test]
    fn builds_keys() {
        assert_eq!(get_integers(0).join(";"), "");
        assert_eq!(
            get_integers(2).join(";"),
            "(smt__TLA____Cast__Int 1);(smt__TLA____Cast__Int 2)"
        );
        assert_eq!(
            get_field_keys(&to_strings(&["a", "b c", "\u{e9}"])).join(";"),
            "smt__TLA____StrLit__a;smt__TLA____StrLit__bspace__c;smt__TLA____StrLit__\u{e9}"
        );
    }

    #[test]
    fn builds_tuples_and_records() {
        assert_eq!(show_axioms(&get_tuple_excepts(0)), "");
        assert_eq!(
            show_axioms(&get_tuple_excepts(2)),
            "TupExcept 2 1\nTupExcept [2,1]\n(forall ((x1 Idv) (x2 Idv) (x Idv)) (! (= (smt__TLA____FunExcept (smt__TLA____Tuple__2 x1 x2) (smt__TLA____Cast__Int 1) x) (smt__TLA____Tuple__2 x x2)) :pattern ((smt__TLA____FunExcept (smt__TLA____Tuple__2 x1 x2) (smt__TLA____Cast__Int 1) x))))\n\nTupExcept 2 2\nTupExcept [2,2]\n(forall ((x1 Idv) (x2 Idv) (x Idv)) (! (= (smt__TLA____FunExcept (smt__TLA____Tuple__2 x1 x2) (smt__TLA____Cast__Int 2) x) (smt__TLA____Tuple__2 x1 x)) :pattern ((smt__TLA____FunExcept (smt__TLA____Tuple__2 x1 x2) (smt__TLA____Cast__Int 2) x))))"
        );
        assert_eq!(
            show_axioms(&get_record_excepts(&to_strings(&["a", "b"]))),
            "RecExcept a b 1\nRecExcept [[\"a\",\"b\"],1]\n(forall ((x1 Idv) (x2 Idv) (x Idv)) (! (= (smt__TLA____FunExcept (smt__TLA____Record__a__b x1 x2) smt__TLA____StrLit__a x) (smt__TLA____Record__a__b x x2)) :pattern ((smt__TLA____FunExcept (smt__TLA____Record__a__b x1 x2) smt__TLA____StrLit__a x))))\n\nRecExcept a b 2\nRecExcept [[\"a\",\"b\"],2]\n(forall ((x1 Idv) (x2 Idv) (x Idv)) (! (= (smt__TLA____FunExcept (smt__TLA____Record__a__b x1 x2) smt__TLA____StrLit__b x) (smt__TLA____Record__a__b x1 x)) :pattern ((smt__TLA____FunExcept (smt__TLA____Record__a__b x1 x2) smt__TLA____StrLit__b x))))"
        );
        assert_eq!(
            show_axioms(&get_tuple_axioms(0, false)),
            "TupIsafcn 0\nTupIsafcn [0]\n(smt__TLA____FunIsafcn smt__TLA____Tuple__0)\n\nSeqTupTyping 0\nSeqTupTyping [0]\n(forall ((a Idv)) (! (smt__TLA____Mem smt__TLA____Tuple__0 (smt__TLA____Seq a)) :pattern (smt__TLA____Tuple__0)))\n\nSeqTupLen 0\nSeqTupLen [0]\n(= (smt__TLA____Len smt__TLA____Tuple__0) (smt__TLA____Cast__Int 0))"
        );
        assert_eq!(
            show_axioms(&get_tuple_axioms(0, true)),
            "TupIsafcn 0\nTupIsafcn [0]\n(smt__TLA____FunIsafcn smt__TLA____Tuple__0)\n\nSeqTupTyping 0\nSeqTupTyping [0]\n(forall ((a Idv)) (! (smt__TLA____Mem smt__TLA____Tuple__0 (smt__TLA____Seq a)) :pattern (smt__TLA____Tuple__0)))\n\nSeqTupLen 0\nSeqTupLen [0]\n(= (smt__TLA____Len smt__TLA____Tuple__0) (smt__TLA____Cast__Int 0))"
        );
        assert_eq!(
            show_axioms(&get_tuple_axioms(1, false)),
            "TupIsafcn 1\nTupIsafcn [1]\n(forall ((x1 Idv)) (! (smt__TLA____FunIsafcn (smt__TLA____Tuple__1 x1)) :pattern ((smt__TLA____Tuple__1 x1))))\n\nTupDomDef 1\nTupDomDef [1]\n(forall ((x1 Idv)) (! (= (smt__TLA____FunDom (smt__TLA____Tuple__1 x1)) (smt__TLA____SetEnum__1 (smt__TLA____Cast__Int 1))) :pattern ((smt__TLA____Tuple__1 x1))))\n\nTupAppDef 1\nTupAppDef [1]\n(forall ((x1 Idv)) (! (= (smt__TLA____FunApp (smt__TLA____Tuple__1 x1) (smt__TLA____Cast__Int 1)) x1) :pattern ((smt__TLA____Tuple__1 x1))))\n\nSeqTupTyping 1\nSeqTupTyping [1]\n(forall ((a Idv) (x1 Idv)) (! (=> (smt__TLA____Mem x1 a) (smt__TLA____Mem (smt__TLA____Tuple__1 x1) (smt__TLA____Seq a))) :pattern ((smt__TLA____Mem x1 a) (smt__TLA____Tuple__1 x1))))\n\nSeqTupLen 1\nSeqTupLen [1]\n(forall ((x1 Idv)) (! (= (smt__TLA____Len (smt__TLA____Tuple__1 x1)) (smt__TLA____Cast__Int 1)) :pattern ((smt__TLA____Tuple__1 x1))))"
        );
        assert_eq!(
            show_axioms(&get_tuple_axioms(2, true)),
            "TupIsafcn 2\nTupIsafcn [2]\n(forall ((x1 Idv) (x2 Idv)) (! (smt__TLA____FunIsafcn (smt__TLA____Tuple__2 x1 x2)) :pattern ((smt__TLA____Tuple__2 x1 x2))))\n\nTupDomDef 2\nTupDomDef [2]\n(forall ((x1 Idv) (x2 Idv)) (! (= (smt__TLA____FunDom (smt__TLA____Tuple__2 x1 x2)) (smt__TLA____SetEnum__2 (smt__TLA____Cast__Int 1) (smt__TLA____Cast__Int 2))) :pattern ((smt__TLA____Tuple__2 x1 x2))))\n\nTupAppDef 2\nTupAppDef [2]\n(forall ((x1 Idv) (x2 Idv)) (! (and (= (smt__TLA____FunApp (smt__TLA____Tuple__2 x1 x2) (smt__TLA____Cast__Int 1)) x1) (= (smt__TLA____FunApp (smt__TLA____Tuple__2 x1 x2) (smt__TLA____Cast__Int 2)) x2)) :pattern ((smt__TLA____Tuple__2 x1 x2))))\n\nSeqTupTyping 2\nSeqTupTyping [2]\n(forall ((a Idv) (x1 Idv) (x2 Idv)) (! (=> (and (smt__TLA____Mem x1 a) (smt__TLA____Mem x2 a)) (smt__TLA____Mem (smt__TLA____Tuple__2 x1 x2) (smt__TLA____Seq a))) :pattern ((smt__TLA____Mem x1 a) (smt__TLA____Mem x2 a) (smt__TLA____Tuple__2 x1 x2))))\n\nSeqTupLen 2\nSeqTupLen [2]\n(forall ((x1 Idv) (x2 Idv)) (! (= (smt__TLA____Len (smt__TLA____Tuple__2 x1 x2)) (smt__TLA____Cast__Int 2)) :pattern ((smt__TLA____Tuple__2 x1 x2))))\n\nTupExcept 2 1\nTupExcept [2,1]\n(forall ((x1 Idv) (x2 Idv) (x Idv)) (! (= (smt__TLA____FunExcept (smt__TLA____Tuple__2 x1 x2) (smt__TLA____Cast__Int 1) x) (smt__TLA____Tuple__2 x x2)) :pattern ((smt__TLA____FunExcept (smt__TLA____Tuple__2 x1 x2) (smt__TLA____Cast__Int 1) x))))\n\nTupExcept 2 2\nTupExcept [2,2]\n(forall ((x1 Idv) (x2 Idv) (x Idv)) (! (= (smt__TLA____FunExcept (smt__TLA____Tuple__2 x1 x2) (smt__TLA____Cast__Int 2) x) (smt__TLA____Tuple__2 x1 x)) :pattern ((smt__TLA____FunExcept (smt__TLA____Tuple__2 x1 x2) (smt__TLA____Cast__Int 2) x))))"
        );
        assert_eq!(
            show_axioms(&get_record_axioms(&to_strings(&[]), true)),
            "RecIsafcn\nRecIsafcn [[]]\n(smt__TLA____FunIsafcn smt__TLA____Record__)"
        );
        assert_eq!(
            show_axioms(&get_record_axioms(&to_strings(&["a", "b"]), true)),
            "RecIsafcn a b\nRecIsafcn [[\"a\",\"b\"]]\n(forall ((x1 Idv) (x2 Idv)) (! (smt__TLA____FunIsafcn (smt__TLA____Record__a__b x1 x2)) :pattern ((smt__TLA____Record__a__b x1 x2))))\n\nRecDomDef a b\nRecDomDef [[\"a\",\"b\"]]\n(forall ((x1 Idv) (x2 Idv)) (! (= (smt__TLA____FunDom (smt__TLA____Record__a__b x1 x2)) (smt__TLA____SetEnum__2 smt__TLA____StrLit__a smt__TLA____StrLit__b)) :pattern ((smt__TLA____Record__a__b x1 x2))))\n\nRecAppDef a b\nRecAppDef [[\"a\",\"b\"]]\n(forall ((x1 Idv) (x2 Idv)) (! (and (= (smt__TLA____FunApp (smt__TLA____Record__a__b x1 x2) smt__TLA____StrLit__a) x1) (= (smt__TLA____FunApp (smt__TLA____Record__a__b x1 x2) smt__TLA____StrLit__b) x2)) :pattern ((smt__TLA____Record__a__b x1 x2))))\n\nRecExcept a b 1\nRecExcept [[\"a\",\"b\"],1]\n(forall ((x1 Idv) (x2 Idv) (x Idv)) (! (= (smt__TLA____FunExcept (smt__TLA____Record__a__b x1 x2) smt__TLA____StrLit__a x) (smt__TLA____Record__a__b x x2)) :pattern ((smt__TLA____FunExcept (smt__TLA____Record__a__b x1 x2) smt__TLA____StrLit__a x))))\n\nRecExcept a b 2\nRecExcept [[\"a\",\"b\"],2]\n(forall ((x1 Idv) (x2 Idv) (x Idv)) (! (= (smt__TLA____FunExcept (smt__TLA____Record__a__b x1 x2) smt__TLA____StrLit__b x) (smt__TLA____Record__a__b x1 x)) :pattern ((smt__TLA____FunExcept (smt__TLA____Record__a__b x1 x2) smt__TLA____StrLit__b x))))"
        );
        assert_eq!(
            show_axioms(&get_record_axioms(&to_strings(&["x"]), false)),
            "RecIsafcn x\nRecIsafcn [[\"x\"]]\n(forall ((x1 Idv)) (! (smt__TLA____FunIsafcn (smt__TLA____Record__x x1)) :pattern ((smt__TLA____Record__x x1))))\n\nRecDomDef x\nRecDomDef [[\"x\"]]\n(forall ((x1 Idv)) (! (= (smt__TLA____FunDom (smt__TLA____Record__x x1)) (smt__TLA____SetEnum__1 smt__TLA____StrLit__x)) :pattern ((smt__TLA____Record__x x1))))\n\nRecAppDef x\nRecAppDef [[\"x\"]]\n(forall ((x1 Idv)) (! (= (smt__TLA____FunApp (smt__TLA____Record__x x1) smt__TLA____StrLit__x) x1) :pattern ((smt__TLA____Record__x x1))))"
        );
        assert_eq!(
            show_axioms(&get_component_set(
                "Product",
                &[AxiomArgument::Number(2)],
                "P",
                "T",
                &get_integers(2),
                "t"
            )),
            "ProductIntro 2\nProductIntro [2]\n(forall ((s1 Idv) (s2 Idv) (x1 Idv) (x2 Idv)) (! (=> (and (smt__TLA____Mem x1 s1) (smt__TLA____Mem x2 s2)) (smt__TLA____Mem (T x1 x2) (P s1 s2))) :pattern ((T x1 x2) (P s1 s2))))\n\nProductElim 2\nProductElim [2]\n(forall ((s1 Idv) (s2 Idv) (t Idv)) (! (=> (smt__TLA____Mem t (P s1 s2)) (and (= t (T (smt__TLA____FunApp t (smt__TLA____Cast__Int 1)) (smt__TLA____FunApp t (smt__TLA____Cast__Int 2)))) (smt__TLA____Mem (smt__TLA____FunApp t (smt__TLA____Cast__Int 1)) s1) (smt__TLA____Mem (smt__TLA____FunApp t (smt__TLA____Cast__Int 2)) s2))) :pattern ((smt__TLA____Mem t (P s1 s2)))))"
        );
        assert_eq!(
            show_axioms(&get_component_set(
                "RecSet",
                &[AxiomArgument::Texts(to_strings(&["a"]))],
                "R",
                "V",
                &get_field_keys(&to_strings(&["a"])),
                "r"
            )),
            "RecSetIntro a\nRecSetIntro [[\"a\"]]\n(forall ((s1 Idv) (x1 Idv)) (! (=> (smt__TLA____Mem x1 s1) (smt__TLA____Mem (V x1) (R s1))) :pattern ((V x1) (R s1))))\n\nRecSetElim a\nRecSetElim [[\"a\"]]\n(forall ((s1 Idv) (r Idv)) (! (=> (smt__TLA____Mem r (R s1)) (and (= r (V (smt__TLA____FunApp r smt__TLA____StrLit__a))) (smt__TLA____Mem (smt__TLA____FunApp r smt__TLA____StrLit__a) s1))) :pattern ((smt__TLA____Mem r (R s1)))))"
        );
        assert_eq!(
            show_axioms(&get_component_set(
                "Product",
                &[AxiomArgument::Number(0)],
                "P",
                "T",
                &[],
                "t"
            )),
            "ProductIntro 0\nProductIntro [0]\n(=> true (smt__TLA____Mem T P))\n\nProductElim 0\nProductElim [0]\n(forall ((t Idv)) (! (=> (smt__TLA____Mem t P) (= t T)) :pattern ((smt__TLA____Mem t P))))"
        );
    }
}
