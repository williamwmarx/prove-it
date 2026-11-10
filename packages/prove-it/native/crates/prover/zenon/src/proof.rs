// Ported from Zenon's mlproof.ml, as shipped in tlapm. Copyright 2004 INRIA, see LICENSE.
//! The proofs that the search builds and the checker reads. Each rule takes a fixed number of
//! arguments, or at least a fixed number. The rules of the TLA+ extension, Zenon's Ext, sit beside
//! the core rules: their names don't clash. `notall` and `notallex` are the rules that only the
//! translation to low-level proofs builds (mltoll's MlRule).

use std::rc::Rc;

use crate::expr::Expr;
use crate::parse::Definition;

macro_rules! rule_names {
    ($($variant:ident = $name:literal, $arity:literal, $is_variadic:literal, $is_relation:literal;)*) => {
        /// A rule's name, as in Zenon's Mlproof.rule.
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub enum RuleName {
            $($variant,)*
        }

        impl RuleName {
            /// The name as the TypeScript and Zenon spell it.
            pub fn as_str(self) -> &'static str {
                match self {
                    $(RuleName::$variant => $name,)*
                }
            }

            /// The number of arguments, or the least number for a variadic rule.
            pub fn arity(self) -> usize {
                match self {
                    $(RuleName::$variant => $arity,)*
                }
            }

            pub fn is_variadic(self) -> bool {
                match self {
                    $(RuleName::$variant => $is_variadic,)*
                }
            }

            /// Whether the rule holds for any relation the hypotheses make reflexive or symmetric,
            /// and so names the relation.
            pub fn is_relation(self) -> bool {
                match self {
                    $(RuleName::$variant => $is_relation,)*
                }
            }
        }
    };
}

rule_names! {
    Close = "close", 1, false, false;
    False = "false", 0, false, false;
    NotTrue = "not_true", 0, false, false;
    ConjTree = "conj_tree", 1, false, false;
    DisjTree = "disj_tree", 1, false, false;
    And = "and", 2, false, false;
    NotNot = "not_not", 1, false, false;
    NotOr = "not_or", 2, false, false;
    NotImpl = "not_impl", 2, false, false;
    Or = "or", 2, false, false;
    Impl = "impl", 2, false, false;
    Equiv = "equiv", 2, false, false;
    NotAnd = "not_and", 2, false, false;
    NotEquiv = "not_equiv", 2, false, false;
    Ex = "ex", 1, false, false;
    NotAllEx = "not_all_ex", 1, false, false;
    All = "all", 2, false, false;
    NotEx = "not_ex", 2, false, false;
    NotEqual = "not_equal", 2, false, false;
    PNotP = "p_not_p", 2, false, false;
    Trans = "trans", 2, false, false;
    TransSym = "trans_sym", 2, false, false;
    TransEq = "trans_eq", 3, false, false;
    TransEqSym = "trans_eq_sym", 3, false, false;
    TransEq2 = "trans_eq2", 3, false, false;
    Cut = "cut", 1, false, false;
    CongruenceLr = "congruence_lr", 3, false, false;
    CongruenceRl = "congruence_rl", 3, false, false;
    Stringequal = "stringequal", 2, false, false;
    Stringdiffll = "stringdiffll", 4, false, false;
    Stringdifflr = "stringdifflr", 4, false, false;
    Stringdiffrl = "stringdiffrl", 4, false, false;
    Stringdiffrr = "stringdiffrr", 4, false, false;
    EqXTrue = "eq_x_true", 3, false, false;
    EqTrueX = "eq_true_x", 3, false, false;
    NoteqXTrue = "noteq_x_true", 3, false, false;
    NoteqTrueX = "noteq_true_x", 3, false, false;
    EqXFalse = "eq_x_false", 3, false, false;
    EqFalseX = "eq_false_x", 3, false, false;
    InEmptyset = "in_emptyset", 2, false, false;
    InUpair = "in_upair", 6, false, false;
    NotinUpair = "notin_upair", 6, false, false;
    InAddElt = "in_addElt", 3, false, false;
    NotinAddElt = "notin_addElt", 3, false, false;
    InSet = "in_set", 3, false, false;
    NotinSet = "notin_set", 3, false, false;
    InSUBSET = "in_SUBSET", 4, false, false;
    NotinSUBSET = "notin_SUBSET", 4, false, false;
    InUNION = "in_UNION", 4, false, false;
    NotinUNION = "notin_UNION", 4, false, false;
    InCup = "in_cup", 6, false, false;
    NotinCup = "notin_cup", 6, false, false;
    InCap = "in_cap", 6, false, false;
    NotinCap = "notin_cap", 6, false, false;
    InSetminus = "in_setminus", 6, false, false;
    NotinSetminus = "notin_setminus", 6, false, false;
    InSubsetof = "in_subsetof", 6, false, false;
    NotinSubsetof = "notin_subsetof", 6, false, false;
    InSetofall = "in_setofall", 5, false, false;
    NotinSetofall = "notin_setofall", 5, false, false;
    InFuncset = "in_funcset", 7, false, false;
    NotinFuncset = "notin_funcset", 7, false, false;
    ExceptNotinFuncset = "except_notin_funcset", 8, false, false;
    Setequalempty = "setequalempty", 3, false, false;
    Setemptyequal = "setemptyequal", 3, false, false;
    Setequal = "setequal", 4, false, false;
    Notsetequal = "notsetequal", 4, false, false;
    NotisafcnFcn = "notisafcn_fcn", 3, false, false;
    NotisafcnExcept = "notisafcn_except", 4, false, false;
    NotisafcnOnearg = "notisafcn_onearg", 3, false, false;
    NotisafcnExtend = "notisafcn_extend", 3, false, false;
    Funequal = "funequal", 4, false, false;
    Notfunequal = "notfunequal", 4, false, false;
    ChooseDiffChoose = "choose_diff_choose", 4, false, false;
    Notequivdef = "notequivdef", 0, false, false;
    Notequalchoose = "notequalchoose", 5, false, false;
    InNat0 = "in_nat_0", 1, false, false;
    InNatSucc = "in_nat_succ", 3, false, false;
    BoxP = "box_p", 2, false, false;
    TupleEqMatch = "tuple_eq_match", 1, true, false;
    TupleEqMismatch = "tuple_eq_mismatch", 2, false, false;
    InProduct = "in_product", 5, true, false;
    NotinProduct = "notin_product", 3, true, false;
    TupleNotisaseq = "tuple_notisaseq", 1, false, false;
    RecordEqMatch = "record_eq_match", 1, true, false;
    RecordEqMismatch = "record_eq_mismatch", 2, false, false;
    RecordNeqMatch = "record_neq_match", 1, true, false;
    NeqRecord = "neq_record", 3, true, false;
    RecordNeq = "record_neq", 3, true, false;
    InRecordset = "in_recordset", 3, true, false;
    NotinRecordset = "notin_recordset", 3, true, false;
    RecordNotisafcn = "record_notisafcn", 1, false, false;
    CupSubseteq = "cup_subseteq", 3, false, false;
    NotCupSubseteq = "not_cup_subseteq", 3, false, false;
    SubseteqCap = "subseteq_cap", 3, false, false;
    NotSubseteqCap = "not_subseteq_cap", 3, false, false;
    AllIn = "all_in", 5, false, false;
    NotexIn = "notex_in", 5, false, false;
    PEqL = "p_eq_l", 7, false, false;
    PEqR = "p_eq_r", 7, false, false;
    NpEqL = "np_eq_l", 7, false, false;
    NpEqR = "np_eq_r", 7, false, false;
    Trueistrue = "trueistrue", 5, false, false;
    Fapplyfcn = "fapplyfcn", 7, false, false;
    Fapplyexcept = "fapplyexcept", 13, false, false;
    TupleAccess = "tuple_access", 5, false, false;
    RecordAccess = "record_access", 5, false, false;
    DomainFcn = "domain_fcn", 5, false, false;
    DomainExcept = "domain_except", 6, false, false;
    RecordDomain = "record_domain", 5, false, false;
    BoolcaseNot = "boolcase_not", 7, false, false;
    BoolcaseAnd = "boolcase_and", 8, false, false;
    BoolcaseOr = "boolcase_or", 8, false, false;
    BoolcaseImply = "boolcase_imply", 8, false, false;
    BoolcaseEquiv = "boolcase_equiv", 8, false, false;
    BoolcaseEqual = "boolcase_equal", 8, false, false;
    BoolcaseAll = "boolcase_all", 7, false, false;
    BoolcaseEx = "boolcase_ex", 7, false, false;
    Iftrue = "iftrue", 5, false, false;
    Iffalse = "iffalse", 5, false, false;
    Ifthenelse = "ifthenelse", 9, false, false;
    Case = "case", 2, true, false;
    TupleLen = "tuple_len", 5, false, false;
    CloseRefl = "close_refl", 1, false, true;
    CloseSym = "close_sym", 2, false, true;
    Refl = "refl", 2, false, true;
    PNotPSym = "p_not_p_sym", 2, false, true;
    Definition = "definition", 2, false, false;
    Notall = "notall", 1, false, false;
    Notallex = "notallex", 1, false, false;
}

/// A rule application. A relation rule names its relation; `definition` unfolds its definition.
#[derive(Clone, Debug)]
pub struct Rule {
    pub name: RuleName,
    pub relation: Option<Rc<str>>,
    pub definition: Option<Rc<Definition>>,
    pub args: Vec<Expr>,
}

impl Rule {
    /// `makeRule`: a rule that names neither a relation nor a definition.
    pub fn new(name: RuleName, args: Vec<Expr>) -> Rule {
        debug_assert!(!name.is_relation() && name != RuleName::Definition);
        debug_assert!(if name.is_variadic() {
            args.len() >= name.arity()
        } else {
            args.len() == name.arity()
        });
        Rule {
            name,
            relation: None,
            definition: None,
            args,
        }
    }

    /// `makeRelationRule`.
    pub fn relation(name: RuleName, relation: &str, args: Vec<Expr>) -> Rule {
        debug_assert!(name.is_relation() && args.len() == name.arity());
        Rule {
            name,
            relation: Some(relation.into()),
            definition: None,
            args,
        }
    }

    /// The rule that unfolds `definition` in the first argument, giving the second.
    pub fn definition(definition: Rc<Definition>, folded: Expr, unfolded: Expr) -> Rule {
        Rule {
            name: RuleName::Definition,
            relation: None,
            definition: Some(definition),
            args: vec![folded, unfolded],
        }
    }
}

/// A proof of the formulas in `conclusions`: the node's rule applied to `uses`, with a subproof for
/// each of its branches. Proofs are shared, and compared by identity where the search reuses one.
#[derive(Debug)]
pub struct Proof {
    pub conclusions: Vec<Expr>,
    pub rule: Rule,
    pub uses: Vec<Expr>,
    pub subproofs: Vec<Rc<Proof>>,
}

/// A proof as a key, by identity, as a JavaScript `Set` of proofs holds them.
#[derive(Clone, Debug)]
pub struct ProofKey(pub Rc<Proof>);

impl PartialEq for ProofKey {
    fn eq(&self, other: &ProofKey) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for ProofKey {}

impl std::hash::Hash for ProofKey {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.0).hash(state);
    }
}
