//! Flatten.instantiate: the axioms of encode/n_axioms.ml for a second-order construct, instantiated
//! for one flattened symbol. Each takes the symbol's name, the bound variables its argument uses,
//! which become its last arguments, and the argument's text with the variable it binds. A port of
//! `src/prover/smt/instances.ts`.

use std::collections::HashSet;

use crate::smt::format::{
    APPEND, FUN_APP, FUN_DOM, FUN_ISAFCN, FUN_SET, IS_SET_OF, LEN, MEM, NAT_SET, PROJ_INT, SEQ,
    TUPLE_0, call, conjoin, forall, get_binders, get_names, replace_token, to_strings,
};
use crate::smt::table::{Axiom, AxiomArgument, axiom, get_axiom_key};

// SetStDef for { x \in a : body }.
pub fn get_set_st_axioms(name: &str, free: &[String], body: &str, variable: &str) -> Vec<Axiom> {
    let set = call(name, &[to_strings(&["a"]), free.to_vec()].concat());
    vec![axiom(
        "SetStDef",
        vec![],
        Some(forall(
            &[free.to_vec(), to_strings(&["a", "x"])].concat(),
            &format!(
                "(= ({MEM} x {set}) (and ({MEM} x a) {}))",
                replace_token(body, variable, "x")
            ),
            &[
                vec![format!("({MEM} x {set})")],
                vec![format!("({MEM} x a)"), set.clone()],
            ],
            "Idv",
        )),
        None,
    )]
}

// SetOfIntro, SetOfElim, and AssertIsSetOf for { element : y1 \in a1, ..., yn \in an }.
pub fn get_set_of_axioms(
    name: &str,
    free: &[String],
    element: &str,
    bound: &[String],
) -> Vec<Axiom> {
    let count = bound.len();
    let sets = get_names("a", count);
    let variables = get_names("y", count);
    let value = bound
        .iter()
        .zip(&variables)
        .fold(element.to_string(), |text, (variable, replacement)| {
            replace_token(&text, variable, replacement)
        });
    let set = call(name, &[sets.clone(), free.to_vec()].concat());
    let guards = variables
        .iter()
        .zip(&sets)
        .map(|(variable, set)| format!("({MEM} {variable} {set})"))
        .collect::<Vec<_>>();
    // N_axioms.assert_issetof names its one set a.
    let single = if count == 1 {
        to_strings(&["a"])
    } else {
        sets.clone()
    };
    let asserted = call(name, &[single.clone(), free.to_vec()].concat());
    let membership = format!("({MEM} x {set})");
    vec![
        axiom(
            "SetOfIntro",
            vec![AxiomArgument::Number(count as i64)],
            Some(forall(
                &[free.to_vec(), sets.clone(), variables.clone()].concat(),
                &format!("(=> {} ({MEM} {value} {set}))", conjoin(&guards)),
                &[
                    vec![value.clone(), set.clone()],
                    [vec![set.clone()], guards.clone()].concat(),
                ],
                "Idv",
            )),
            None,
        ),
        axiom(
            "SetOfElim",
            vec![AxiomArgument::Number(count as i64)],
            Some(forall(
                &[free.to_vec(), sets.clone(), to_strings(&["x"])].concat(),
                &format!(
                    "(=> {membership} (exists ({}) {}))",
                    get_binders(&variables, "Idv"),
                    conjoin(&[guards.clone(), vec![format!("(= x {value})")]].concat())
                ),
                &[vec![membership.clone()]],
                "Idv",
            )),
            None,
        ),
        axiom(
            "AssertIsSetOf",
            vec![AxiomArgument::Number(count as i64)],
            Some(forall(
                &[free.to_vec(), single].concat(),
                &format!("({IS_SET_OF} {asserted})"),
                &[vec![asserted.clone()]],
                "Idv",
            )),
            None,
        ),
    ]
}

// FunConstrIsafcn, FunDomDef, FunAppDef, and FunTyping when collect brought it, for
// [x \in a |-> body].
pub fn get_function_axioms(
    name: &str,
    free: &[String],
    body: &str,
    variable: &str,
    axioms: &HashSet<String>,
) -> Vec<Axiom> {
    let value = call(name, &[to_strings(&["a"]), free.to_vec()].concat());
    let result = replace_token(body, variable, "x");
    let typing = if axioms.contains(&get_axiom_key(&axiom("FunTyping", vec![], None, None))) {
        vec![axiom(
            "FunTyping",
            vec![],
            Some(forall(
                &[free.to_vec(), to_strings(&["a", "b"])].concat(),
                &format!(
                    "(=> (forall ((x Idv)) (=> ({MEM} x a) ({MEM} {result} b))) ({MEM} {value} ({FUN_SET} a b)))"
                ),
                &[vec![value.clone(), format!("({FUN_SET} a b)")]],
                "Idv",
            )),
            None,
        )]
    } else {
        vec![]
    };
    let application = format!("({FUN_APP} {value} x)");
    [
        vec![
            axiom(
                "FunConstrIsafcn",
                vec![],
                Some(forall(
                    &[free.to_vec(), to_strings(&["a"])].concat(),
                    &format!("({FUN_ISAFCN} {value})"),
                    &[vec![value.clone()]],
                    "Idv",
                )),
                None,
            ),
            axiom(
                "FunDomDef",
                vec![],
                Some(forall(
                    &[free.to_vec(), to_strings(&["a"])].concat(),
                    &format!("(= ({FUN_DOM} {value}) a)"),
                    &[vec![value.clone()]],
                    "Idv",
                )),
                None,
            ),
            axiom(
                "FunAppDef",
                vec![],
                Some(forall(
                    &[free.to_vec(), to_strings(&["a", "x"])].concat(),
                    &format!("(=> ({MEM} x a) (= {application} {result}))"),
                    &[
                        vec![application.clone()],
                        vec![format!("({MEM} x a)"), value.clone()],
                    ],
                    "Idv",
                )),
                None,
            ),
        ],
        typing,
    ]
    .concat()
}

// ChooseDef for CHOOSE x : body.
pub fn get_choose_axioms(name: &str, free: &[String], body: &str, variable: &str) -> Vec<Axiom> {
    vec![axiom(
        "ChooseDef",
        vec![],
        Some(forall(
            &[free.to_vec(), to_strings(&["x"])].concat(),
            &format!(
                "(=> {} {})",
                replace_token(body, variable, "x"),
                replace_token(body, variable, &call(name, free))
            ),
            &[],
            "Idv",
        )),
        None,
    )]
}

// The SeqSelectseq axioms for SelectSeq(s, LAMBDA x : body).
pub fn get_select_seq_axioms(
    name: &str,
    free: &[String],
    body: &str,
    variable: &str,
) -> Vec<Axiom> {
    let select = |sequence: &str| call(name, &[vec![sequence.to_string()], free.to_vec()].concat());
    let test = |term: &str| replace_token(body, variable, term);
    let appended = select(&format!("({APPEND} s x)"));
    let selected = select("s");
    vec![
        axiom(
            "SeqSelectseqTyping",
            vec![],
            Some(forall(
                &[free.to_vec(), to_strings(&["a", "s"])].concat(),
                &format!("(=> ({MEM} s ({SEQ} a)) ({MEM} {selected} ({SEQ} a)))"),
                &[vec![format!("({MEM} s ({SEQ} a))"), selected.clone()]],
                "Idv",
            )),
            None,
        ),
        axiom(
            "SeqSelectseqLen",
            vec![],
            Some(forall(
                &[free.to_vec(), to_strings(&["s"])].concat(),
                &format!(
                    "(=> ({MEM} ({LEN} s) {NAT_SET}) (<= ({PROJ_INT} ({LEN} {selected})) ({PROJ_INT} ({LEN} s))))"
                ),
                &[vec![selected.clone()]],
                "Idv",
            )),
            None,
        ),
        axiom(
            "SeqSelectseqNil",
            vec![],
            Some(forall(
                free,
                &format!("(= {} {TUPLE_0})", select(TUPLE_0)),
                &[],
                "Idv",
            )),
            None,
        ),
        axiom(
            "SeqSelectseqApp",
            vec![],
            Some(forall(
                &[free.to_vec(), to_strings(&["s", "x"])].concat(),
                &format!(
                    "(=> ({MEM} x ({FUN_DOM} {selected})) {})",
                    test(&format!("({FUN_APP} {selected} x)"))
                ),
                &[vec![format!("({FUN_APP} {selected} x)")]],
                "Idv",
            )),
            None,
        ),
        axiom(
            "SeqSelectseqAppend",
            vec![],
            Some(forall(
                &[free.to_vec(), to_strings(&["s", "x"])].concat(),
                &format!(
                    "(and (=> {} (= {appended} ({APPEND} {selected} x))) (=> (not {}) (= {appended} {selected})))",
                    test("x"),
                    test("x")
                ),
                &[vec![appended.clone()]],
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
    fn instantiates_axioms() {
        assert_eq!(
            show_axioms(&get_set_st_axioms(
                "S",
                &to_strings(&["y#1", "z#2"]),
                "(P x#3 xx#3 y#1)",
                "x#3"
            )),
            "SetStDef\nSetStDef []\n(forall ((y#1 Idv) (z#2 Idv) (a Idv) (x Idv)) (! (= (smt__TLA____Mem x (S a y#1 z#2)) (and (smt__TLA____Mem x a) (P x xx#3 y#1))) :pattern ((smt__TLA____Mem x (S a y#1 z#2))) :pattern ((smt__TLA____Mem x a) (S a y#1 z#2))))"
        );
        assert_eq!(
            show_axioms(&get_set_st_axioms("S", &to_strings(&[]), "x#0", "x#0")),
            "SetStDef\nSetStDef []\n(forall ((a Idv) (x Idv)) (! (= (smt__TLA____Mem x (S a)) (and (smt__TLA____Mem x a) x)) :pattern ((smt__TLA____Mem x (S a))) :pattern ((smt__TLA____Mem x a) (S a))))"
        );
        assert_eq!(
            show_axioms(&get_set_of_axioms(
                "O",
                &to_strings(&["y#1", "z#2"]),
                "(g u#4 v#5)",
                &to_strings(&["u#4", "v#5"])
            )),
            "SetOfIntro 2\nSetOfIntro [2]\n(forall ((y#1 Idv) (z#2 Idv) (a1 Idv) (a2 Idv) (y1 Idv) (y2 Idv)) (! (=> (and (smt__TLA____Mem y1 a1) (smt__TLA____Mem y2 a2)) (smt__TLA____Mem (g y1 y2) (O a1 a2 y#1 z#2))) :pattern ((g y1 y2) (O a1 a2 y#1 z#2)) :pattern ((O a1 a2 y#1 z#2) (smt__TLA____Mem y1 a1) (smt__TLA____Mem y2 a2))))\n\nSetOfElim 2\nSetOfElim [2]\n(forall ((y#1 Idv) (z#2 Idv) (a1 Idv) (a2 Idv) (x Idv)) (! (=> (smt__TLA____Mem x (O a1 a2 y#1 z#2)) (exists ((y1 Idv) (y2 Idv)) (and (smt__TLA____Mem y1 a1) (smt__TLA____Mem y2 a2) (= x (g y1 y2))))) :pattern ((smt__TLA____Mem x (O a1 a2 y#1 z#2)))))\n\nAssertIsSetOf 2\nAssertIsSetOf [2]\n(forall ((y#1 Idv) (z#2 Idv) (a1 Idv) (a2 Idv)) (! (smt__TLA____IsSetOf (O a1 a2 y#1 z#2)) :pattern ((O a1 a2 y#1 z#2))))"
        );
        assert_eq!(
            show_axioms(&get_set_of_axioms(
                "O",
                &to_strings(&[]),
                "(g u#4)",
                &to_strings(&["u#4"])
            )),
            "SetOfIntro 1\nSetOfIntro [1]\n(forall ((a1 Idv) (y1 Idv)) (! (=> (smt__TLA____Mem y1 a1) (smt__TLA____Mem (g y1) (O a1))) :pattern ((g y1) (O a1)) :pattern ((O a1) (smt__TLA____Mem y1 a1))))\n\nSetOfElim 1\nSetOfElim [1]\n(forall ((a1 Idv) (x Idv)) (! (=> (smt__TLA____Mem x (O a1)) (exists ((y1 Idv)) (and (smt__TLA____Mem y1 a1) (= x (g y1))))) :pattern ((smt__TLA____Mem x (O a1)))))\n\nAssertIsSetOf 1\nAssertIsSetOf [1]\n(forall ((a Idv)) (! (smt__TLA____IsSetOf (O a)) :pattern ((O a))))"
        );
        assert_eq!(
            show_axioms(&get_set_of_axioms(
                "O",
                &to_strings(&["w"]),
                "c",
                &to_strings(&[])
            )),
            "SetOfIntro 0\nSetOfIntro [0]\n(forall ((w Idv)) (! (=> true (smt__TLA____Mem c (O w))) :pattern (c (O w)) :pattern ((O w))))\n\nSetOfElim 0\nSetOfElim [0]\n(forall ((w Idv) (x Idv)) (! (=> (smt__TLA____Mem x (O w)) (exists () (= x c))) :pattern ((smt__TLA____Mem x (O w)))))\n\nAssertIsSetOf 0\nAssertIsSetOf [0]\n(forall ((w Idv)) (! (smt__TLA____IsSetOf (O w)) :pattern ((O w))))"
        );
        assert_eq!(
            show_axioms(&get_function_axioms(
                "F",
                &to_strings(&["y#1", "z#2"]),
                "(+ x#3 y#1)",
                "x#3",
                &HashSet::new()
            )),
            "FunConstrIsafcn\nFunConstrIsafcn []\n(forall ((y#1 Idv) (z#2 Idv) (a Idv)) (! (smt__TLA____FunIsafcn (F a y#1 z#2)) :pattern ((F a y#1 z#2))))\n\nFunDomDef\nFunDomDef []\n(forall ((y#1 Idv) (z#2 Idv) (a Idv)) (! (= (smt__TLA____FunDom (F a y#1 z#2)) a) :pattern ((F a y#1 z#2))))\n\nFunAppDef\nFunAppDef []\n(forall ((y#1 Idv) (z#2 Idv) (a Idv) (x Idv)) (! (=> (smt__TLA____Mem x a) (= (smt__TLA____FunApp (F a y#1 z#2) x) (+ x y#1))) :pattern ((smt__TLA____FunApp (F a y#1 z#2) x)) :pattern ((smt__TLA____Mem x a) (F a y#1 z#2))))"
        );
        assert_eq!(
            show_axioms(&get_function_axioms(
                "F",
                &to_strings(&[]),
                "x#3",
                "x#3",
                &HashSet::from(["FunTyping []".to_string()])
            )),
            "FunConstrIsafcn\nFunConstrIsafcn []\n(forall ((a Idv)) (! (smt__TLA____FunIsafcn (F a)) :pattern ((F a))))\n\nFunDomDef\nFunDomDef []\n(forall ((a Idv)) (! (= (smt__TLA____FunDom (F a)) a) :pattern ((F a))))\n\nFunAppDef\nFunAppDef []\n(forall ((a Idv) (x Idv)) (! (=> (smt__TLA____Mem x a) (= (smt__TLA____FunApp (F a) x) x)) :pattern ((smt__TLA____FunApp (F a) x)) :pattern ((smt__TLA____Mem x a) (F a))))\n\nFunTyping\nFunTyping []\n(forall ((a Idv) (b Idv)) (! (=> (forall ((x Idv)) (=> (smt__TLA____Mem x a) (smt__TLA____Mem x b))) (smt__TLA____Mem (F a) (smt__TLA____FunSet a b))) :pattern ((F a) (smt__TLA____FunSet a b))))"
        );
        assert_eq!(
            show_axioms(&get_choose_axioms(
                "C",
                &to_strings(&["y#1", "z#2"]),
                "(P x#3 y#1)",
                "x#3"
            )),
            "ChooseDef\nChooseDef []\n(forall ((y#1 Idv) (z#2 Idv) (x Idv)) (=> (P x y#1) (P (C y#1 z#2) y#1)))"
        );
        assert_eq!(
            show_axioms(&get_choose_axioms("C", &to_strings(&[]), "(P x#3)", "x#3")),
            "ChooseDef\nChooseDef []\n(forall ((x Idv)) (=> (P x) (P C)))"
        );
        assert_eq!(
            show_axioms(&get_select_seq_axioms(
                "L",
                &to_strings(&["y#1", "z#2"]),
                "(Q x#3 z#2)",
                "x#3"
            )),
            "SeqSelectseqTyping\nSeqSelectseqTyping []\n(forall ((y#1 Idv) (z#2 Idv) (a Idv) (s Idv)) (! (=> (smt__TLA____Mem s (smt__TLA____Seq a)) (smt__TLA____Mem (L s y#1 z#2) (smt__TLA____Seq a))) :pattern ((smt__TLA____Mem s (smt__TLA____Seq a)) (L s y#1 z#2))))\n\nSeqSelectseqLen\nSeqSelectseqLen []\n(forall ((y#1 Idv) (z#2 Idv) (s Idv)) (! (=> (smt__TLA____Mem (smt__TLA____Len s) smt__TLA____NatSet) (<= (smt__TLA____Proj__Int (smt__TLA____Len (L s y#1 z#2))) (smt__TLA____Proj__Int (smt__TLA____Len s)))) :pattern ((L s y#1 z#2))))\n\nSeqSelectseqNil\nSeqSelectseqNil []\n(forall ((y#1 Idv) (z#2 Idv)) (= (L smt__TLA____Tuple__0 y#1 z#2) smt__TLA____Tuple__0))\n\nSeqSelectseqApp\nSeqSelectseqApp []\n(forall ((y#1 Idv) (z#2 Idv) (s Idv) (x Idv)) (! (=> (smt__TLA____Mem x (smt__TLA____FunDom (L s y#1 z#2))) (Q (smt__TLA____FunApp (L s y#1 z#2) x) z#2)) :pattern ((smt__TLA____FunApp (L s y#1 z#2) x))))\n\nSeqSelectseqAppend\nSeqSelectseqAppend []\n(forall ((y#1 Idv) (z#2 Idv) (s Idv) (x Idv)) (! (and (=> (Q x z#2) (= (L (smt__TLA____Append s x) y#1 z#2) (smt__TLA____Append (L s y#1 z#2) x))) (=> (not (Q x z#2)) (= (L (smt__TLA____Append s x) y#1 z#2) (L s y#1 z#2)))) :pattern ((L (smt__TLA____Append s x) y#1 z#2))))"
        );
        assert_eq!(
            show_axioms(&get_select_seq_axioms(
                "L",
                &to_strings(&[]),
                "(Q x#3)",
                "x#3"
            )),
            "SeqSelectseqTyping\nSeqSelectseqTyping []\n(forall ((a Idv) (s Idv)) (! (=> (smt__TLA____Mem s (smt__TLA____Seq a)) (smt__TLA____Mem (L s) (smt__TLA____Seq a))) :pattern ((smt__TLA____Mem s (smt__TLA____Seq a)) (L s))))\n\nSeqSelectseqLen\nSeqSelectseqLen []\n(forall ((s Idv)) (! (=> (smt__TLA____Mem (smt__TLA____Len s) smt__TLA____NatSet) (<= (smt__TLA____Proj__Int (smt__TLA____Len (L s))) (smt__TLA____Proj__Int (smt__TLA____Len s)))) :pattern ((L s))))\n\nSeqSelectseqNil\nSeqSelectseqNil []\n(= (L smt__TLA____Tuple__0) smt__TLA____Tuple__0)\n\nSeqSelectseqApp\nSeqSelectseqApp []\n(forall ((s Idv) (x Idv)) (! (=> (smt__TLA____Mem x (smt__TLA____FunDom (L s))) (Q (smt__TLA____FunApp (L s) x))) :pattern ((smt__TLA____FunApp (L s) x))))\n\nSeqSelectseqAppend\nSeqSelectseqAppend []\n(forall ((s Idv) (x Idv)) (! (and (=> (Q x) (= (L (smt__TLA____Append s x)) (smt__TLA____Append (L s) x))) (=> (not (Q x)) (= (L (smt__TLA____Append s x)) (L s)))) :pattern ((L (smt__TLA____Append s x)))))"
        );
    }
}
