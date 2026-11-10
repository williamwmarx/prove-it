//! encode/n_data.ml: the declaration, dependencies, and axioms of each symbol tlapm's SMT encoding
//! uses. A port of `src/prover/smt/data.ts`.

use std::collections::HashMap;

use crate::errors::{ObligationError, Result};
use crate::smt::axioms::{
    TYPED_OPERATORS, get_component_set, get_enumeration, get_field_keys, get_integers,
    get_record_axioms, get_record_excepts, get_tuple_axioms, get_tuple_excepts, get_typing,
};
use crate::smt::format::{
    APPEND, BOOL_SET, CAP, CAST_BOOL, CAST_INT, CAT, FUN_APP, FUN_DOM, FUN_EXCEPT, FUN_ISAFCN,
    FUN_SET, HEAD, INT_LTEQ, INT_RANGE, INT_SET, IS_SET_OF, LEN, MEM, NAT_SET, PROJ_INT, SEQ,
    SET_EXT_TRIGGER, STR_SET, SUB_SEQ, SUBSET, SUBSET_EQ, TAIL, TRIG_EQ, TT_IDV, UNION, declare,
    forall, tla, to_strings,
};
use crate::smt::table::{Axiom, AxiomArgument, axiom};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymbolSpec {
    pub declaration: Option<String>,
    pub deps: Vec<String>,
    pub axioms: Vec<Axiom>,
}

// N_data.s: what the symbols collected so far change about the axioms of the next ones. The maps
// are looked up only, never iterated.
#[derive(Clone, Debug)]
pub struct CollectState<'encoder> {
    // The fields of each record symbol the obligation uses.
    pub record_fields: &'encoder HashMap<String, Vec<String>>,
    pub strings: Vec<String>,
    pub is_fun_constr: bool,
    pub is_fun_set: bool,
    pub is_except: bool,
    pub tuples: Vec<usize>,
    pub records: Vec<Vec<String>>,
    pub anonymous: &'encoder HashMap<String, usize>,
}

const SEQUENCE_DEPS: [&str; 7] = [
    "Mem", "Seq", "Len", "FunApp", "NatSet", "Cast_Int", "Proj_Int",
];

/// `/^<prefix>(\d+)$/` and `Number` of the digits. A count too large for `usize` doesn't match.
fn get_count(name: &str, prefix: &str) -> Option<usize> {
    let digits = name.strip_prefix(prefix)?;
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    digits.parse().ok()
}

fn spec(declaration: Option<String>, deps: &[&str], axioms: Vec<Axiom>) -> SymbolSpec {
    SymbolSpec {
        declaration,
        deps: to_strings(deps),
        axioms,
    }
}

fn no_formula(name: &str) -> Axiom {
    axiom(name, vec![], None, None)
}

fn with_formula(name: &str, formula: String) -> Axiom {
    axiom(name, vec![], Some(formula), None)
}

// N_data.get_deps, with arithmetic and set extensionality as tlapm's SMT backend sets them.
pub fn get_symbol_spec(name: &str, state: &mut CollectState) -> Result<SymbolSpec> {
    let symbol = tla(name);
    let fixed = |arity: usize, deps: Vec<String>, axioms: Vec<Axiom>, sort: &str| SymbolSpec {
        declaration: Some(declare(&symbol, arity, sort, "Idv")),
        deps,
        axioms,
    };
    if let Some(count) = get_count(name, "SetEnum_") {
        return Ok(fixed(
            count,
            to_strings(&["Mem"]),
            get_enumeration(count),
            "Idv",
        ));
    }
    if let Some(count) = get_count(name, "SetOf_") {
        let count_argument = || vec![AxiomArgument::Number(count as i64)];
        return Ok(spec(
            None,
            &["Mem", "IsSetOf"],
            vec![
                axiom("SetOfIntro", count_argument(), None, None),
                axiom("SetOfElim", count_argument(), None, None),
                axiom("AssertIsSetOf", count_argument(), None, None),
                with_formula(
                    "CompareSetOfTrigger",
                    forall(
                        &to_strings(&["a", "b"]),
                        &format!("({SET_EXT_TRIGGER} a b)"),
                        &[vec![format!("({IS_SET_OF} a)"), format!("({IS_SET_OF} b)")]],
                        "Idv",
                    ),
                ),
            ],
        ));
    }
    if let Some(value) = name.strip_prefix("StrLit_") {
        let distinct = state
            .strings
            .iter()
            .map(|other| {
                axiom(
                    "StrLitDistinct",
                    vec![
                        AxiomArgument::Text(value.to_string()),
                        AxiomArgument::Text(other.clone()),
                    ],
                    Some(format!(
                        "(distinct {symbol} {})",
                        tla(&format!("StrLit_{other}"))
                    )),
                    None,
                )
            })
            .collect::<Vec<_>>();
        state.strings.push(value.to_string());
        let mut axioms = vec![axiom(
            "StrLitIsstr",
            vec![AxiomArgument::Text(value.to_string())],
            Some(format!("({MEM} {symbol} {STR_SET})")),
            None,
        )];
        axioms.extend(distinct);
        return Ok(fixed(0, to_strings(&["Mem", "StrSet"]), axioms, "Idv"));
    }
    if let Some(count) = get_count(name, "Tuple_") {
        state.tuples.push(count);
        let deps = if count == 0 {
            to_strings(&["FunIsafcn", "Cast_Int", "Seq", "Len"])
        } else {
            vec![
                "FunIsafcn".to_string(),
                "FunDom".to_string(),
                "FunApp".to_string(),
                format!("SetEnum_{count}"),
                "Cast_Int".to_string(),
                "Mem".to_string(),
                "Seq".to_string(),
                "Len".to_string(),
            ]
        };
        return Ok(fixed(
            count,
            deps,
            get_tuple_axioms(count, state.is_except),
            "Idv",
        ));
    }
    if let Some(count) = get_count(name, "Product_") {
        return Ok(fixed(
            count,
            vec![
                "Mem".to_string(),
                format!("Tuple_{count}"),
                "FunApp".to_string(),
                "Cast_Int".to_string(),
                "Proj_Int".to_string(),
            ],
            get_component_set(
                "Product",
                &[AxiomArgument::Number(count as i64)],
                &symbol,
                &tla(&format!("Tuple_{count}")),
                &get_integers(count),
                "t",
            ),
            "Idv",
        ));
    }
    let fields = state.record_fields.get(name);
    if let Some(fields) = fields
        && name.starts_with("Record_")
    {
        state.records.push(fields.clone());
        let mut deps = vec![
            "FunIsafcn".to_string(),
            "FunDom".to_string(),
            "FunApp".to_string(),
            format!("SetEnum_{}", fields.len()),
        ];
        deps.extend(fields.iter().map(|field| format!("StrLit_{field}")));
        return Ok(fixed(
            fields.len(),
            deps,
            get_record_axioms(fields, state.is_except),
            "Idv",
        ));
    }
    if let Some(fields) = fields
        && name.starts_with("RecordSet_")
    {
        let record = format!("Record_{}", fields.join("_"));
        let mut deps = vec!["Mem".to_string(), record.clone(), "FunApp".to_string()];
        deps.extend(fields.iter().map(|field| format!("StrLit_{field}")));
        return Ok(fixed(
            fields.len(),
            deps,
            get_component_set(
                "RecSet",
                &[AxiomArgument::Texts(fields.clone())],
                &symbol,
                &tla(&record),
                &get_field_keys(fields),
                "r",
            ),
            "Idv",
        ));
    }
    if let Some(anonymous) = state.anonymous.get(name) {
        return Ok(fixed(*anonymous, vec![], vec![], "Idv"));
    }
    if let Some(typed) = TYPED_OPERATORS.iter().find(|entry| entry.0 == name) {
        return Ok(fixed(
            typed.2,
            to_strings(&["Cast_Int"]),
            vec![get_typing(name)?],
            if name == "IntLteq" { "Bool" } else { "Idv" },
        ));
    }
    let fixed = |arity: usize, deps: &[&str], axioms: Vec<Axiom>, sort: &str| {
        fixed(arity, to_strings(deps), axioms, sort)
    };
    Ok(match name {
        // SMT-LIB has no exponentiation, so IntExp keeps only its typing.
        "IntExp" => fixed(
            2,
            &[
                "Mem",
                "IntSet",
                "Cast_Int",
                "TIntLteq",
                "TIntLit_0",
                "TIntLit_1",
            ],
            vec![with_formula(
                "IntExpTyping",
                format!(
                    "(forall ((x Idv) (y Idv)) (! (=> (and ({MEM} x {INT_SET}) ({MEM} y {INT_SET}) (or (distinct x ({CAST_INT} 0)) ({INT_LTEQ} ({CAST_INT} 1) y))) ({MEM} ({symbol} x y) {INT_SET})) :pattern (({symbol} x y))))"
                ),
            )],
            "Idv",
        ),
        "SelectSeq" => spec(
            None,
            &[
                "Mem", "Seq", "Len", "Append", "FunApp", "FunDom", "IntSet", "NatSet", "Tuple_0",
                "Proj_Int",
            ],
            vec![
                no_formula("SeqSelectseqTyping"),
                no_formula("SeqSelectseqLen"),
                no_formula("SeqSelectseqNil"),
                no_formula("SeqSelectseqApp"),
                no_formula("SeqSelectseqAppend"),
            ],
        ),
        "Choose" => spec(None, &[], vec![no_formula("ChooseDef")]),
        "Mem" => fixed(
            2,
            &["SetExtTrigger"],
            vec![with_formula(
                "SetExt",
                format!(
                    "(forall ((x Idv) (y Idv)) (! (=> (forall ((z Idv)) (= ({MEM} z x) ({MEM} z y))) (= x y)) :pattern (({SET_EXT_TRIGGER} x y))))"
                ),
            )],
            "Bool",
        ),
        "SubsetEq" => fixed(
            2,
            &["Mem"],
            vec![
                with_formula(
                    "SubsetEqIntro",
                    format!(
                        "(forall ((x Idv) (y Idv)) (! (=> (forall ((z Idv)) (=> ({MEM} z x) ({MEM} z y))) ({SUBSET_EQ} x y)) :pattern (({SUBSET_EQ} x y))))"
                    ),
                ),
                with_formula(
                    "SubsetEqElim",
                    format!(
                        "(forall ((x Idv) (y Idv) (z Idv)) (! (=> (and ({SUBSET_EQ} x y) ({MEM} z x)) ({MEM} z y)) :pattern (({SUBSET_EQ} x y) ({MEM} z x))))"
                    ),
                ),
            ],
            "Bool",
        ),
        "Union" => fixed(
            1,
            &["Mem"],
            vec![
                with_formula(
                    "UnionIntro",
                    format!(
                        "(forall ((a Idv) (x Idv) (y Idv)) (! (=> (and ({MEM} y a) ({MEM} x y)) ({MEM} x ({UNION} a))) :pattern (({MEM} y a) ({MEM} x ({UNION} a))) :pattern (({MEM} x y) ({MEM} x ({UNION} a))) :pattern (({MEM} y a) ({MEM} x y) ({UNION} a))))"
                    ),
                ),
                with_formula(
                    "UnionElim",
                    format!(
                        "(forall ((a Idv) (x Idv)) (! (=> ({MEM} x ({UNION} a)) (exists ((y Idv)) (and ({MEM} y a) ({MEM} x y)))) :pattern (({MEM} x ({UNION} a)))))"
                    ),
                ),
            ],
            "Idv",
        ),
        "Subset" => fixed(
            1,
            &["Mem", "SubsetEq"],
            vec![with_formula(
                "SubsetDefAlt",
                format!(
                    "(forall ((a Idv) (x Idv)) (! (= ({MEM} x ({SUBSET} a)) ({SUBSET_EQ} x a)) :pattern (({MEM} x ({SUBSET} a))) :pattern (({SUBSET_EQ} x a) ({SUBSET} a))))"
                ),
            )],
            "Idv",
        ),
        "Cup" | "Cap" | "SetMinus" => {
            let condition = match name {
                "Cup" => "(or (MEM x a) (MEM x b))",
                "Cap" => "(and (MEM x a) (MEM x b))",
                _ => "(and (MEM x a) (not (MEM x b)))",
            };
            let definition = with_formula(
                &format!("{name}Def"),
                format!(
                    "(forall ((a Idv) (b Idv) (x Idv)) (! (= ({MEM} x ({symbol} a b)) {}) :pattern (({MEM} x ({symbol} a b))) :pattern (({MEM} x a) ({symbol} a b)) :pattern (({MEM} x b) ({symbol} a b))))",
                    condition.replace("MEM", MEM)
                ),
            );
            if name != "Cap" {
                return Ok(fixed(2, &["Mem"], vec![definition], "Idv"));
            }
            fixed(
                2,
                &["Mem", "SetEnum_0", "SetExtTrigger"],
                vec![
                    definition,
                    with_formula(
                        "DisjointTrigger",
                        format!(
                            "(forall ((x Idv) (y Idv)) (! ({SET_EXT_TRIGGER} ({CAP} x y) {}) :pattern (({CAP} x y))))",
                            tla("SetEnum_0")
                        ),
                    ),
                ],
                "Idv",
            )
        }
        "SetSt" => spec(
            None,
            &["Mem", "SetEnum_0", "SetExtTrigger"],
            vec![
                no_formula("SetStDef"),
                no_formula("EmptyComprehensionTrigger"),
            ],
        ),
        "NatSet" => fixed(
            0,
            &["IntSet", "TIntLit_0", "Cast_Int", "IntLteq"],
            vec![with_formula(
                "NatSetDef",
                format!(
                    "(forall ((x Idv)) (! (= ({MEM} x {NAT_SET}) (and ({MEM} x {INT_SET}) ({INT_LTEQ} ({CAST_INT} 0) x))) :pattern (({MEM} x {NAT_SET}))))"
                ),
            )],
            "Idv",
        ),
        "IntRange" => fixed(
            2,
            &["Mem", "IntSet", "IntLteq"],
            vec![with_formula(
                "IntRangeDef",
                format!(
                    "(forall ((a Idv) (b Idv) (x Idv)) (! (= ({MEM} x ({INT_RANGE} a b)) (and ({MEM} x {INT_SET}) ({INT_LTEQ} a x) ({INT_LTEQ} x b))) :pattern (({MEM} x ({INT_RANGE} a b)))))"
                ),
            )],
            "Idv",
        ),
        "FunIsafcn" => fixed(
            1,
            &["Mem", "FunDom", "FunFcn", "FunApp"],
            vec![with_formula(
                "FunExt",
                format!(
                    "(forall ((f Idv) (g Idv)) (! (=> (and ({FUN_ISAFCN} f) ({FUN_ISAFCN} g) (= ({FUN_DOM} f) ({FUN_DOM} g)) (forall ((x Idv)) (=> ({MEM} x ({FUN_DOM} f)) (= ({FUN_APP} f x) ({FUN_APP} g x))))) (= f g)) :pattern (({FUN_ISAFCN} f) ({FUN_ISAFCN} g))))"
                ),
            )],
            "Bool",
        ),
        "FunSet" => {
            state.is_fun_set = true;
            let mut axioms = vec![
                with_formula(
                    "FunSetIntro",
                    format!(
                        "(forall ((a Idv) (b Idv) (f Idv)) (! (=> (and ({FUN_ISAFCN} f) (= ({FUN_DOM} f) a) (forall ((x Idv)) (=> ({MEM} x a) ({MEM} ({FUN_APP} f x) b)))) ({MEM} f ({FUN_SET} a b))) :pattern (({MEM} f ({FUN_SET} a b)))))"
                    ),
                ),
                with_formula(
                    "FunSetElim1",
                    format!(
                        "(forall ((a Idv) (b Idv) (f Idv)) (! (=> ({MEM} f ({FUN_SET} a b)) (and ({FUN_ISAFCN} f) (= ({FUN_DOM} f) a))) :pattern (({MEM} f ({FUN_SET} a b)))))"
                    ),
                ),
                with_formula(
                    "FunSetElim2",
                    format!(
                        "(forall ((a Idv) (b Idv) (f Idv) (x Idv)) (! (=> (and ({MEM} f ({FUN_SET} a b)) ({MEM} x a)) ({MEM} ({FUN_APP} f x) b)) :pattern (({MEM} f ({FUN_SET} a b)) ({MEM} x a)) :pattern (({MEM} f ({FUN_SET} a b)) ({FUN_APP} f x))))"
                    ),
                ),
            ];
            if state.is_fun_constr {
                axioms.push(no_formula("FunTyping"));
            }
            fixed(2, &["Mem", "FunIsafcn", "FunDom", "FunApp"], axioms, "Idv")
        }
        "FunFcn" => {
            state.is_fun_constr = true;
            let mut axioms = vec![no_formula("FunConstrIsafcn")];
            if state.is_fun_set {
                axioms.push(no_formula("FunTyping"));
            }
            spec(None, &["FunIsafcn"], axioms)
        }
        "FunDom" => fixed(1, &["FunFcn"], vec![no_formula("FunDomDef")], "Idv"),
        "FunApp" => fixed(2, &["Mem", "FunFcn"], vec![no_formula("FunAppDef")], "Idv"),
        "FunExcept" => {
            state.is_except = true;
            let updated = format!("({FUN_EXCEPT} f x y)");
            let mut axioms = vec![
                with_formula(
                    "FunExceptIsafcn",
                    format!(
                        "(forall ((f Idv) (x Idv) (y Idv)) (! ({FUN_ISAFCN} {updated}) :pattern ({updated})))"
                    ),
                ),
                with_formula(
                    "FunExceptDomDef",
                    format!(
                        "(forall ((f Idv) (x Idv) (y Idv)) (! (= ({FUN_DOM} {updated}) ({FUN_DOM} f)) :pattern ({updated})))"
                    ),
                ),
                with_formula(
                    "FunExceptAppDef1",
                    format!(
                        "(forall ((f Idv) (x Idv) (y Idv)) (! (=> ({MEM} x ({FUN_DOM} f)) (= ({FUN_APP} {updated} x) y)) :pattern ({updated})))"
                    ),
                ),
                with_formula(
                    "FunExceptAppDef2",
                    format!(
                        "(forall ((f Idv) (x Idv) (y Idv) (z Idv)) (! (=> ({MEM} z ({FUN_DOM} f)) (and (=> (= z x) (= ({FUN_APP} {updated} z) y)) (=> (distinct z x) (= ({FUN_APP} {updated} z) ({FUN_APP} f z))))) :pattern (({FUN_APP} {updated} z)) :pattern ({updated} ({FUN_APP} f z))))"
                    ),
                ),
            ];
            axioms.extend(
                state
                    .tuples
                    .iter()
                    .flat_map(|count| get_tuple_excepts(*count)),
            );
            axioms.extend(
                state
                    .records
                    .iter()
                    .flat_map(|fields| get_record_excepts(fields)),
            );
            fixed(3, &["Mem", "FunIsafcn", "FunDom", "FunApp"], axioms, "Idv")
        }
        // tlapm labels SeqSetElim1 and SeqSetElim2 SetSetElim1 and SetSetElim2.
        "Seq" => fixed(
            1,
            &[
                "Mem",
                "Len",
                "FunIsafcn",
                "FunDom",
                "FunApp",
                "IntSet",
                "NatSet",
                "IntRange",
                "Cast_Int",
                "Proj_Int",
            ],
            vec![
                with_formula(
                    "SeqSetIntro",
                    format!(
                        "(forall ((a Idv) (s Idv)) (! (=> (and ({FUN_ISAFCN} s) (>= ({PROJ_INT} ({LEN} s)) 0) (forall ((i Idv)) (= ({MEM} i ({FUN_DOM} s)) (and ({MEM} i {INT_SET}) (<= 1 ({PROJ_INT} i)) (<= ({PROJ_INT} i) ({PROJ_INT} ({LEN} s)))))) (forall ((i Int)) (=> (and (<= 1 i) (<= i ({PROJ_INT} ({LEN} s)))) ({MEM} ({FUN_APP} s ({CAST_INT} i)) a)))) ({MEM} s ({SEQ} a))) :pattern (({MEM} s ({SEQ} a)))))"
                    ),
                ),
                axiom(
                    "SeqSetElim1",
                    vec![],
                    Some(format!(
                        "(forall ((a Idv) (s Idv)) (! (=> ({MEM} s ({SEQ} a)) (and ({FUN_ISAFCN} s) ({MEM} ({LEN} s) {NAT_SET}) (= ({FUN_DOM} s) ({INT_RANGE} ({CAST_INT} 1) ({LEN} s))))) :pattern (({MEM} s ({SEQ} a)))))"
                    )),
                    Some("SetSetElim1".to_string()),
                ),
                axiom(
                    "SeqSetElim2",
                    vec![],
                    Some(format!(
                        "(forall ((a Idv) (s Idv) (i Int)) (! (=> (and ({MEM} s ({SEQ} a)) (<= 1 i) (<= i ({PROJ_INT} ({LEN} s)))) ({MEM} ({FUN_APP} s ({CAST_INT} i)) a)) :pattern (({MEM} s ({SEQ} a)) ({FUN_APP} s ({CAST_INT} i)))))"
                    )),
                    Some("SetSetElim2".to_string()),
                ),
            ],
            "Idv",
        ),
        "Len" => fixed(
            1,
            &["FunDom", "IntRange", "Cast_Int"],
            vec![with_formula(
                "SeqLenDef",
                format!(
                    "(forall ((s Idv) (z Int)) (=> (and (>= z 0) (= ({FUN_DOM} s) ({INT_RANGE} ({CAST_INT} 1) ({CAST_INT} z)))) (= ({LEN} s) ({CAST_INT} z))))"
                ),
            )],
            "Idv",
        ),
        "BSeq" => fixed(1, &[], vec![], "Idv"),
        "Cat" => fixed(
            2,
            &SEQUENCE_DEPS,
            vec![
                with_formula(
                    "SeqCatTyping",
                    format!(
                        "(forall ((a Idv) (s Idv) (t Idv)) (! (=> (and ({MEM} s ({SEQ} a)) ({MEM} t ({SEQ} a))) ({MEM} ({CAT} s t) ({SEQ} a))) :pattern (({MEM} s ({SEQ} a)) ({CAT} s t)) :pattern (({MEM} t ({SEQ} a)) ({CAT} s t))))"
                    ),
                ),
                with_formula(
                    "SeqCatLen",
                    format!(
                        "(forall ((s Idv) (t Idv)) (! (=> (and ({MEM} ({LEN} s) {NAT_SET}) ({MEM} ({LEN} t) {NAT_SET})) (= ({LEN} ({CAT} s t)) ({CAST_INT} (+ ({PROJ_INT} ({LEN} s)) ({PROJ_INT} ({LEN} t)))))) :pattern (({CAT} s t))))"
                    ),
                ),
                with_formula(
                    "SeqCatApp1",
                    format!(
                        "(forall ((s Idv) (t Idv) (i Int)) (! (=> (and ({MEM} ({LEN} s) {NAT_SET}) ({MEM} ({LEN} t) {NAT_SET}) (<= 1 i) (<= i ({PROJ_INT} ({LEN} s)))) (= ({FUN_APP} ({CAT} s t) ({CAST_INT} i)) ({FUN_APP} s ({CAST_INT} i)))) :pattern (({FUN_APP} ({CAT} s t) ({CAST_INT} i))) :pattern (({CAT} s t) ({FUN_APP} s ({CAST_INT} i)))))"
                    ),
                ),
                with_formula(
                    "SeqCatApp2",
                    format!(
                        "(forall ((s Idv) (t Idv) (i Int)) (! (=> (and ({MEM} ({LEN} s) {NAT_SET}) ({MEM} ({LEN} t) {NAT_SET}) (<= i (+ ({PROJ_INT} ({LEN} s)) ({PROJ_INT} ({LEN} t)))) (< ({PROJ_INT} ({LEN} s)) i)) (= ({FUN_APP} ({CAT} s t) ({CAST_INT} i)) ({FUN_APP} t ({CAST_INT} (- i ({PROJ_INT} ({LEN} s))))))) :pattern (({FUN_APP} ({CAT} s t) ({CAST_INT} i)))))"
                    ),
                ),
            ],
            "Idv",
        ),
        "Append" => fixed(
            2,
            &SEQUENCE_DEPS,
            vec![
                with_formula(
                    "SeqAppendTyping",
                    format!(
                        "(forall ((a Idv) (s Idv) (x Idv)) (! (=> (and ({MEM} s ({SEQ} a)) ({MEM} x a)) ({MEM} ({APPEND} s x) ({SEQ} a))) :pattern (({MEM} s ({SEQ} a)) ({APPEND} s x))))"
                    ),
                ),
                with_formula(
                    "SeqAppendLen",
                    format!(
                        "(forall ((s Idv) (x Idv)) (! (=> ({MEM} ({LEN} s) {NAT_SET}) (= ({LEN} ({APPEND} s x)) ({CAST_INT} (+ ({PROJ_INT} ({LEN} s)) 1)))) :pattern (({APPEND} s x))))"
                    ),
                ),
                with_formula(
                    "SeqAppendApp1",
                    format!(
                        "(forall ((s Idv) (x Idv) (i Int)) (! (=> (and ({MEM} ({LEN} s) {NAT_SET}) (<= 1 i) (<= i ({PROJ_INT} ({LEN} s)))) (= ({FUN_APP} ({APPEND} s x) ({CAST_INT} i)) ({FUN_APP} s ({CAST_INT} i)))) :pattern (({FUN_APP} ({APPEND} s x) ({CAST_INT} i))) :pattern (({APPEND} s x) ({FUN_APP} s ({CAST_INT} i)))))"
                    ),
                ),
                with_formula(
                    "SeqAppendApp2",
                    format!(
                        "(forall ((s Idv) (x Idv)) (! (=> ({MEM} ({LEN} s) {NAT_SET}) (= ({FUN_APP} ({APPEND} s x) ({CAST_INT} (+ ({PROJ_INT} ({LEN} s)) 1))) x)) :pattern (({APPEND} s x))))"
                    ),
                ),
            ],
            "Idv",
        ),
        "Head" => fixed(
            1,
            &["FunApp", "Cast_Int"],
            vec![with_formula(
                "SeqHeadDef",
                format!(
                    "(forall ((s Idv)) (! (= ({HEAD} s) ({FUN_APP} s ({CAST_INT} 1))) :pattern (({HEAD} s))))"
                ),
            )],
            "Idv",
        ),
        "Tail" => fixed(
            1,
            &SEQUENCE_DEPS,
            vec![
                with_formula(
                    "SeqTailTyping",
                    format!(
                        "(forall ((a Idv) (s Idv)) (! (=> (and ({MEM} s ({SEQ} a)) (distinct ({PROJ_INT} ({LEN} s)) 0)) ({MEM} ({TAIL} s) ({SEQ} a))) :pattern (({MEM} s ({SEQ} a)) ({TAIL} s))))"
                    ),
                ),
                with_formula(
                    "SeqTailLen",
                    format!(
                        "(forall ((s Idv)) (! (=> (and ({MEM} ({LEN} s) {NAT_SET}) (distinct ({PROJ_INT} ({LEN} s)) 0)) (= ({LEN} ({TAIL} s)) ({CAST_INT} (- ({PROJ_INT} ({LEN} s)) 1)))) :pattern (({TAIL} s))))"
                    ),
                ),
                with_formula(
                    "SeqTailApp",
                    format!(
                        "(forall ((s Idv) (i Int)) (! (=> (and ({MEM} ({LEN} s) {NAT_SET}) (distinct ({PROJ_INT} ({LEN} s)) 0) (<= 1 i) (<= i (- ({PROJ_INT} ({LEN} s)) 1))) (= ({FUN_APP} ({TAIL} s) ({CAST_INT} i)) ({FUN_APP} s ({CAST_INT} (+ i 1))))) :pattern (({FUN_APP} ({TAIL} s) ({CAST_INT} i)))))"
                    ),
                ),
            ],
            "Idv",
        ),
        "SubSeq" => {
            let range = format!("({SUB_SEQ} s ({CAST_INT} x) ({CAST_INT} y))");
            fixed(
                3,
                &[
                    "Mem", "Seq", "Len", "FunApp", "IntSet", "Cast_Int", "Proj_Int",
                ],
                vec![
                    with_formula(
                        "SeqSubseqTyping",
                        format!(
                            "(forall ((a Idv) (s Idv) (x Int) (y Int)) (! (=> (or (< y x) (and ({MEM} s ({SEQ} a)) (<= 1 x) (<= y ({PROJ_INT} ({LEN} s))))) ({MEM} {range} ({SEQ} a))) :pattern (({MEM} s ({SEQ} a)) {range})))"
                        ),
                    ),
                    with_formula(
                        "SeqSubseqLen",
                        format!(
                            "(forall ((s Idv) (x Int) (y Int)) (! (and (=> (<= x (+ y 1)) (= ({LEN} {range}) ({CAST_INT} (- (+ y 1) x)))) (=> (> x (+ y 1)) (= ({LEN} {range}) ({CAST_INT} 0)))) :pattern ({range})))"
                        ),
                    ),
                    with_formula(
                        "SeqSubseqApp",
                        format!(
                            "(forall ((s Idv) (x Int) (y Int) (z Int)) (! (=> (and (<= 1 x) (<= 1 z) (<= z (- (+ y 1) x))) (= ({FUN_APP} {range} ({CAST_INT} z)) ({FUN_APP} s ({CAST_INT} (- (+ z x) 1))))) :pattern (({FUN_APP} {range} ({CAST_INT} z)))))"
                        ),
                    ),
                ],
                "Idv",
            )
        }
        "Cast_Int" => spec(
            Some(declare(&symbol, 1, "Idv", "Int")),
            &["Mem", "IntSet", "Proj_Int"],
            vec![
                axiom(
                    "CastInjAlt",
                    vec![AxiomArgument::Text("Int".to_string())],
                    Some(format!(
                        "(forall ((x Int)) (! (= x ({PROJ_INT} ({CAST_INT} x))) :pattern (({CAST_INT} x))))"
                    )),
                    None,
                ),
                axiom(
                    "TypeGuardIntro",
                    vec![AxiomArgument::Text("Int".to_string())],
                    Some(format!(
                        "(forall ((z Int)) (! ({MEM} ({CAST_INT} z) {INT_SET}) :pattern (({CAST_INT} z))))"
                    )),
                    None,
                ),
                axiom(
                    "TypeGuardElim",
                    vec![AxiomArgument::Text("Int".to_string())],
                    Some(format!(
                        "(forall ((x Idv)) (! (=> ({MEM} x {INT_SET}) (= x ({CAST_INT} ({PROJ_INT} x)))) :pattern (({MEM} x {INT_SET}))))"
                    )),
                    None,
                ),
            ],
        ),
        "Cast_Bool" => spec(
            Some(declare(&symbol, 1, "Idv", "Bool")),
            &["Mem", "BoolSet", "Tt_Idv"],
            vec![
                axiom(
                    "CastInjAlt",
                    vec![AxiomArgument::Text("Bool".to_string())],
                    Some(format!(
                        "(and (= ({CAST_BOOL} true) {TT_IDV}) (distinct ({CAST_BOOL} false) {TT_IDV}))"
                    )),
                    None,
                ),
                axiom(
                    "TypeGuardIntro",
                    vec![AxiomArgument::Text("Bool".to_string())],
                    Some(format!(
                        "(forall ((z Bool)) (! ({MEM} ({CAST_BOOL} z) {BOOL_SET}) :pattern (({CAST_BOOL} z))))"
                    )),
                    None,
                ),
                axiom(
                    "TypeGuardElim",
                    vec![AxiomArgument::Text("Bool".to_string())],
                    Some(format!(
                        "(forall ((x Idv)) (! (=> ({MEM} x {BOOL_SET}) (or (= x ({CAST_BOOL} true)) (= x ({CAST_BOOL} false)))) :pattern (({MEM} x {BOOL_SET}))))"
                    )),
                    None,
                ),
            ],
        ),
        "Proj_Int" => spec(Some(declare(&symbol, 1, "Int", "Idv")), &[], vec![]),
        "TrigEq_Set$Idv$" => fixed(
            2,
            &["SetExtTrigger"],
            vec![
                axiom(
                    "ExtTrigEqDef",
                    vec![AxiomArgument::Text("Set$Idv$".to_string())],
                    Some(format!(
                        "(forall ((x Idv) (y Idv)) (! (= ({TRIG_EQ} x y) (= x y)) :pattern (({TRIG_EQ} x y))))"
                    )),
                    None,
                ),
                axiom(
                    "ExtTrigEqTrigger",
                    vec![AxiomArgument::Text("Idv".to_string())],
                    Some(format!(
                        "(forall ((x Idv) (y Idv)) (! ({SET_EXT_TRIGGER} x y) :pattern (({TRIG_EQ} x y))))"
                    )),
                    None,
                ),
            ],
            "Bool",
        ),
        "SetExtTrigger" | "IsSetOf" => {
            fixed(if name == "IsSetOf" { 1 } else { 2 }, &[], vec![], "Bool")
        }
        "BoolSet" | "StrSet" | "IntSet" | "Tt_Idv" => fixed(0, &[], vec![], "Idv"),
        "TIntLteq" => spec(None, &["IntLteq"], vec![get_typing("IntLteq")?]),
        // The rest are numerals, which SMT-LIB has natively.
        _ if name.starts_with("TIntLit_") => spec(None, &[], vec![]),
        _ => return Err(ObligationError::unsupported(format!("the symbol {name}"))),
    })
}

// Expected values from running the TypeScript.
#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::table::tests::show_axioms;

    fn show(name: &str, state: &mut CollectState) -> String {
        match get_symbol_spec(name, state) {
            Ok(spec) => format!(
                "{}\n{}\n{}",
                spec.declaration.as_deref().unwrap_or("<none>"),
                spec.deps.join(","),
                show_axioms(&spec.axioms)
            ),
            Err(error) => format!("ERR {}: {}", error.name(), error.message()),
        }
    }

    /// FNV-1a over the UTF-8 bytes, which the TypeScript side computes the same way.
    fn get_digest(text: &str) -> u64 {
        text.bytes().fold(0xcbf2_9ce4_8422_2325, |hash, byte| {
            (hash ^ u64::from(byte)).wrapping_mul(0x0100_0000_01b3)
        })
    }

    #[test]
    fn specifies_symbols() {
        assert_eq!(
            {
                let record_fields = HashMap::from([
                    ("Record_a_b".to_string(), to_strings(&["a", "b"])),
                    ("RecordSet_a_b".to_string(), to_strings(&["a", "b"])),
                    ("Record_x".to_string(), to_strings(&["x"])),
                ]);
                let anonymous = HashMap::from([("Anon_foo".to_string(), 2)]);
                let mut state = CollectState {
                    record_fields: &record_fields,
                    strings: vec![],
                    is_fun_constr: false,
                    is_fun_set: false,
                    is_except: false,
                    tuples: vec![],
                    records: vec![],
                    anonymous: &anonymous,
                };
                let dumps = [
                    "Tuple_2",
                    "FunExcept",
                    "Record_a_b",
                    "RecordSet_a_b",
                    "FunSet",
                    "FunFcn",
                    "FunSet",
                    "StrLit_a",
                    "StrLit_b",
                    "StrLit_\u{e9}\"",
                    "SetEnum_0",
                    "SetEnum_3",
                    "SetEnum_007",
                    "SetOf_2",
                    "Product_2",
                    "Product_0",
                    "IntPlus",
                    "IntMinus",
                    "IntTimes",
                    "IntUminus",
                    "IntQuotient",
                    "IntRemainder",
                    "IntLteq",
                    "IntExp",
                    "SelectSeq",
                    "Choose",
                    "Mem",
                    "SubsetEq",
                    "Union",
                    "Subset",
                    "Cup",
                    "Cap",
                    "SetMinus",
                    "SetSt",
                    "NatSet",
                    "IntRange",
                    "FunIsafcn",
                    "FunDom",
                    "FunApp",
                    "Seq",
                    "Len",
                    "BSeq",
                    "Cat",
                    "Append",
                    "Head",
                    "Tail",
                    "SubSeq",
                    "Cast_Int",
                    "Cast_Bool",
                    "Proj_Int",
                    "TrigEq_Set$Idv$",
                    "SetExtTrigger",
                    "IsSetOf",
                    "BoolSet",
                    "StrSet",
                    "IntSet",
                    "Tt_Idv",
                    "TIntLteq",
                    "TIntLit_5",
                    "Anon_foo",
                    "Bogus",
                    "Record_zz",
                    "Tuple_0",
                    "Record_x",
                    "FunExcept",
                    "SetEnum_",
                    "Tuple_1x",
                ]
                .iter()
                .map(|name| format!("== {name}\n{}", show(name, &mut state)))
                .collect::<Vec<_>>();
                let dump = format!(
                    "{}\n== state\n{}|{}|{}|{}|{}|{}",
                    dumps.join("\n"),
                    state.strings.join(","),
                    state.is_fun_constr,
                    state.is_fun_set,
                    state.is_except,
                    state
                        .tuples
                        .iter()
                        .map(usize::to_string)
                        .collect::<Vec<_>>()
                        .join(","),
                    state
                        .records
                        .iter()
                        .map(|fields| fields.join(","))
                        .collect::<Vec<_>>()
                        .join(";")
                );
                let picked = [30, 8, 60, 57, 59]
                    .iter()
                    .map(|index| dumps[*index].clone())
                    .collect::<Vec<_>>()
                    .join("\n");
                format!("{:016x}\n{picked}", get_digest(&dump))
            },
            "0ce94363a181f0f3\n== Cup\n(declare-fun smt__TLA____Cup (Idv Idv) Idv)\nMem\nCupDef\nCupDef []\n(forall ((a Idv) (b Idv) (x Idv)) (! (= (smt__TLA____Mem x (smt__TLA____Cup a b)) (or (smt__TLA____Mem x a) (smt__TLA____Mem x b))) :pattern ((smt__TLA____Mem x (smt__TLA____Cup a b))) :pattern ((smt__TLA____Mem x a) (smt__TLA____Cup a b)) :pattern ((smt__TLA____Mem x b) (smt__TLA____Cup a b))))\n== StrLit_b\n(declare-fun smt__TLA____StrLit__b () Idv)\nMem,StrSet\nStrLitIsstr b\nStrLitIsstr [\"b\"]\n(smt__TLA____Mem smt__TLA____StrLit__b smt__TLA____StrSet)\n\nStrLitDistinct b a\nStrLitDistinct [\"b\",\"a\"]\n(distinct smt__TLA____StrLit__b smt__TLA____StrLit__a)\n== Bogus\nERR TlaUnsupportedError: the symbol Bogus\n== TIntLteq\n<none>\nIntLteq\nTyping TIntLteq\nTyping [6]\n(forall ((x1 Int) (x2 Int)) (! (= (smt__TLA____IntLteq (smt__TLA____Cast__Int x1) (smt__TLA____Cast__Int x2)) (<= x1 x2)) :pattern ((smt__TLA____IntLteq (smt__TLA____Cast__Int x1) (smt__TLA____Cast__Int x2)))))\n== Anon_foo\n(declare-fun smt__TLA____Anon__foo (Idv Idv) Idv)\n\n"
        );
    }
}
