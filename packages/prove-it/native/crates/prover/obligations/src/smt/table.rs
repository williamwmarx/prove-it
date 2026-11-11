//! encode/n_table.ml: the axioms tlapm's SMT encoding can assert, in the order it prints them. A
//! port of `src/prover/smt/table.ts`.

use crate::errors::quote_json;
use crate::ocaml::{OcamlValue, compare_values};

// The order of tlapm's Table.tla_axm constructors. OCaml compares constant constructors before
// those with arguments, so the axioms of an obligation print in this order.
const CONSTANT_AXIOMS: [&str; 78] = [
    "ChooseDef",
    "ChooseExt",
    "SetExt",
    "SubsetEqDef",
    "SubsetEqIntro",
    "SubsetEqElim",
    "UnionDef",
    "UnionIntro",
    "UnionElim",
    "SubsetDef",
    "SubsetDefAlt",
    "SubsetIntro",
    "SubsetElim",
    "CupDef",
    "CapDef",
    "SetMinusDef",
    "SetStDef",
    "NatSetDef",
    "IntPlusTyping",
    "IntUminusTyping",
    "IntMinusTyping",
    "IntTimesTyping",
    "IntQuotientTyping",
    "IntRemainderTyping",
    "IntExpTyping",
    "NatPlusTyping",
    "NatTimesTyping",
    "IntRangeDef",
    "NonNegIsPos",
    "LteqReflexive",
    "LteqTransitive",
    "LteqAntisym",
    "FunExt",
    "FunConstrIsafcn",
    "FunSetDef",
    "FunSetIntro",
    "FunSetElim1",
    "FunSetElim2",
    "FunSetImIntro",
    "FunSetSubs",
    "FunDomDef",
    "FunAppDef",
    "FunTyping",
    "FunExceptIsafcn",
    "FunExceptDomDef",
    "FunExceptAppDef1",
    "FunExceptAppDef2",
    "FunExceptTyping",
    "FunImDef",
    "FunImIntro",
    "FunImElim",
    "SeqSetIntro",
    "SeqSetElim1",
    "SeqSetElim2",
    "SeqLenDef",
    "SeqCatTyping",
    "SeqCatLen",
    "SeqCatApp1",
    "SeqCatApp2",
    "SeqAppendTyping",
    "SeqAppendLen",
    "SeqAppendApp1",
    "SeqAppendApp2",
    "SeqHeadDef",
    "SeqTailTyping",
    "SeqTailLen",
    "SeqTailApp",
    "SeqSubseqTyping",
    "SeqSubseqLen",
    "SeqSubseqApp",
    "SeqSelectseqTyping",
    "SeqSelectseqLen",
    "SeqSelectseqNil",
    "SeqSelectseqApp",
    "SeqSelectseqAppend",
    "DisjointTrigger",
    "EmptyComprehensionTrigger",
    "CompareSetOfTrigger",
];

const BLOCK_AXIOMS: [&str; 36] = [
    "EnumDef",
    "EnumDefIntro",
    "EnumDefElim",
    "SetOfDef",
    "SetOfIntro",
    "SetOfElim",
    "StrLitIsstr",
    "StrLitDistinct",
    "IntLitIsint",
    "IntLitDistinct",
    "IntLitZeroCmp",
    "TupIsafcn",
    "TupDomDef",
    "TupAppDef",
    "TupExcept",
    "ProductDef",
    "ProductIntro",
    "ProductElim",
    "RecIsafcn",
    "RecDomDef",
    "RecAppDef",
    "RecExcept",
    "RecSetDef",
    "RecSetIntro",
    "RecSetElim",
    "SeqTupTyping",
    "SeqTupLen",
    "CastInj",
    "CastInjAlt",
    "TypeGuard",
    "TypeGuardIntro",
    "TypeGuardElim",
    "Typing",
    "ExtTrigEqDef",
    "ExtTrigEqTrigger",
    "AssertIsSetOf",
];

// Table.tla_smb's typed constant constructors, which Typing takes, in order.
pub const TYPED_SYMBOLS: [&str; 7] = [
    "TIntPlus",
    "TIntUminus",
    "TIntMinus",
    "TIntTimes",
    "TIntQuotient",
    "TIntRemainder",
    "TIntLteq",
];

/// `AxiomArgument`: a number, a string, or a list of strings.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AxiomArgument {
    Number(i64),
    Text(String),
    Texts(Vec<String>),
}

// An axiom without a formula belongs to a second-order symbol. Flattening instantiates it for
// each use of the symbol, and otherwise it isn't printed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Axiom {
    pub name: String,
    pub args: Vec<AxiomArgument>,
    pub label: String,
    pub formula: Option<String>,
}

/// `axiom`; the default label is the name and the flattened arguments.
pub fn axiom(
    name: &str,
    args: Vec<AxiomArgument>,
    formula: Option<String>,
    label: Option<String>,
) -> Axiom {
    let label = label.unwrap_or_else(|| {
        let mut words = vec![name.to_string()];
        for argument in &args {
            match argument {
                AxiomArgument::Number(number) => words.push(number.to_string()),
                AxiomArgument::Text(text) => words.push(text.clone()),
                AxiomArgument::Texts(texts) => words.extend(texts.iter().cloned()),
            }
        }
        words.join(" ")
    });
    Axiom {
        name: name.to_string(),
        args,
        label,
        formula,
    }
}

pub fn get_axiom_key(entry: &Axiom) -> String {
    let json = entry
        .args
        .iter()
        .map(|argument| match argument {
            AxiomArgument::Number(number) => number.to_string(),
            AxiomArgument::Text(text) => quote_json(text),
            AxiomArgument::Texts(texts) => format!(
                "[{}]",
                texts
                    .iter()
                    .map(|text| quote_json(text))
                    .collect::<Vec<_>>()
                    .join(",")
            ),
        })
        .collect::<Vec<_>>()
        .join(",");
    format!("{} [{json}]", entry.name)
}

fn get_axiom_rank(entry: &Axiom) -> i64 {
    let index_of = |names: &[&str]| {
        names
            .iter()
            .position(|name| *name == entry.name)
            .map_or(-1, |index| index as i64)
    };
    let constant = index_of(&CONSTANT_AXIOMS);
    if constant == -1 {
        CONSTANT_AXIOMS.len() as i64 + index_of(&BLOCK_AXIOMS)
    } else {
        constant
    }
}

fn get_ocaml_value(args: &[AxiomArgument]) -> OcamlValue {
    OcamlValue::List(
        args.iter()
            .map(|argument| match argument {
                AxiomArgument::Number(number) => OcamlValue::Int(*number),
                AxiomArgument::Text(text) => OcamlValue::Text(text.clone()),
                AxiomArgument::Texts(texts) => {
                    OcamlValue::List(texts.iter().cloned().map(OcamlValue::Text).collect())
                }
            })
            .collect(),
    )
}

// N_axiomatize.TlaAxmSet orders axioms as OCaml's compare does.
pub fn compare_axioms(left: &Axiom, right: &Axiom) -> i64 {
    match get_axiom_rank(left) - get_axiom_rank(right) {
        0 => compare_values(&get_ocaml_value(&left.args), &get_ocaml_value(&right.args)),
        rank => rank,
    }
}

// Expected values from running the TypeScript.
#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::smt::format::to_strings;

    pub(crate) fn show_axiom(entry: &Axiom) -> String {
        format!(
            "{}\n{}\n{}",
            entry.label,
            get_axiom_key(entry),
            entry.formula.as_deref().unwrap_or("<none>")
        )
    }

    pub(crate) fn show_axioms(entries: &[Axiom]) -> String {
        entries
            .iter()
            .map(show_axiom)
            .collect::<Vec<_>>()
            .join("\n\n")
    }

    #[test]
    fn labels_and_keys() {
        assert_eq!(
            show_axiom(&axiom(
                "Typing",
                vec![AxiomArgument::Number(3)],
                Some("(p)".to_string()),
                None
            )),
            "Typing 3\nTyping [3]\n(p)"
        );
        assert_eq!(
            show_axiom(&axiom(
                "RecExcept",
                vec![
                    AxiomArgument::Texts(to_strings(&["a", "b"])),
                    AxiomArgument::Number(2)
                ],
                None,
                None
            )),
            "RecExcept a b 2\nRecExcept [[\"a\",\"b\"],2]\n<none>"
        );
        assert_eq!(
            show_axiom(&axiom(
                "SeqSetElim1",
                vec![],
                Some("(q)".to_string()),
                Some("SetSetElim1".to_string())
            )),
            "SetSetElim1\nSeqSetElim1 []\n(q)"
        );
        assert_eq!(
            show_axiom(&axiom(
                "RecIsafcn",
                vec![AxiomArgument::Texts(to_strings(&[]))],
                None,
                None
            )),
            "RecIsafcn\nRecIsafcn [[]]\n<none>"
        );
        assert_eq!(
            show_axiom(&axiom(
                "StrLitDistinct",
                vec![
                    AxiomArgument::Text("a\"b".to_string()),
                    AxiomArgument::Text("c\\d\n\u{e9}\u{1}".to_string())
                ],
                None,
                None
            )),
            "StrLitDistinct a\"b c\\d\n\u{e9}\u{1}\nStrLitDistinct [\"a\\\"b\",\"c\\\\d\\n\u{e9}\\u0001\"]\n<none>"
        );
        assert_eq!(
            show_axiom(&axiom(
                "CastInjAlt",
                vec![AxiomArgument::Text("Int".to_string())],
                None,
                None
            )),
            "CastInjAlt Int\nCastInjAlt [\"Int\"]\n<none>"
        );
    }

    #[test]
    fn orders_axioms() {
        assert_eq!(
            {
                let mut axioms = vec![
                    axiom("TupIsafcn", vec![AxiomArgument::Number(2)], None, None),
                    axiom("SetExt", vec![], None, None),
                    axiom("Bogus", vec![], None, None),
                    axiom("TupIsafcn", vec![AxiomArgument::Number(1)], None, None),
                    axiom("CompareSetOfTrigger", vec![], None, None),
                    axiom(
                        "RecIsafcn",
                        vec![AxiomArgument::Texts(to_strings(&["b"]))],
                        None,
                        None,
                    ),
                    axiom(
                        "RecIsafcn",
                        vec![AxiomArgument::Texts(to_strings(&["a", "z"]))],
                        None,
                        None,
                    ),
                    axiom(
                        "RecIsafcn",
                        vec![AxiomArgument::Texts(to_strings(&["a"]))],
                        None,
                        None,
                    ),
                    axiom("ChooseDef", vec![], None, None),
                    axiom(
                        "StrLitDistinct",
                        vec![
                            AxiomArgument::Text("b".to_string()),
                            AxiomArgument::Text("a".to_string()),
                        ],
                        None,
                        None,
                    ),
                    axiom(
                        "StrLitDistinct",
                        vec![
                            AxiomArgument::Text("a".to_string()),
                            AxiomArgument::Text("c".to_string()),
                        ],
                        None,
                        None,
                    ),
                    axiom("Typing", vec![AxiomArgument::Number(6)], None, None),
                    axiom("Typing", vec![AxiomArgument::Number(0)], None, None),
                    axiom("EnumDef", vec![], None, None),
                ];
                axioms.sort_by(|left, right| compare_axioms(left, right).cmp(&0));
                axioms
                    .iter()
                    .map(|entry| entry.label.clone())
                    .collect::<Vec<_>>()
                    .join(",")
            },
            "ChooseDef,SetExt,Bogus,CompareSetOfTrigger,EnumDef,StrLitDistinct a c,StrLitDistinct b a,TupIsafcn 1,TupIsafcn 2,RecIsafcn a,RecIsafcn a z,RecIsafcn b,Typing 0,Typing 6"
        );
        assert_eq!(
            compare_axioms(
                &axiom("TupIsafcn", vec![AxiomArgument::Number(2)], None, None),
                &axiom("TupIsafcn", vec![AxiomArgument::Number(1)], None, None)
            ),
            1
        );
        assert_eq!(
            compare_axioms(
                &axiom("SetExt", vec![], None, None),
                &axiom("TupIsafcn", vec![AxiomArgument::Number(2)], None, None)
            ),
            -87
        );
        assert_eq!(
            compare_axioms(
                &axiom("Bogus", vec![], None, None),
                &axiom("CompareSetOfTrigger", vec![], None, None)
            ),
            0
        );
        assert_eq!(
            compare_axioms(
                &axiom(
                    "RecIsafcn",
                    vec![AxiomArgument::Texts(to_strings(&["a", "z"]))],
                    None,
                    None
                ),
                &axiom(
                    "RecIsafcn",
                    vec![AxiomArgument::Texts(to_strings(&["a"]))],
                    None,
                    None
                )
            ),
            1
        );
    }
}
