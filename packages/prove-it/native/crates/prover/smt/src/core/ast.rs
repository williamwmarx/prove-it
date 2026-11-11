//! Ported from Z3 (src/ast/ast.h, src/ast/ast.cpp), MIT license, through `ast.ts`. A hash-consed
//! DAG of applications, de Bruijn variables and quantifiers, as in Z3's ast_manager.
//!
//! Expressions, declarations and sorts are `i32` handles, since the TypeScript stores -1 in each
//! (a null expression, the declaration of a variable, the range of ite). Where the TypeScript
//! throws, the methods return `Result`; a callback that may create expressions cannot borrow the
//! manager, so `map_args`, `some_arg` and `every_arg` only read, and a caller that creates
//! expressions per argument loops over `get_arg`. `mk_app` takes the arguments as a slice, which
//! stands for the TypeScript's `start` offset into the caller's array.

use std::collections::{HashMap, HashSet};
use std::fmt;

use prove_num::{Int, Rational};

use crate::core::flat_literals::FlatLiterals;
use crate::util::error::SmtError;
use crate::util::hash::{
    ast_array_hash, bytes_hash, combine_hash, get_composite_hash, mk_mix, string_hash,
};
use crate::util::hashtable::ObjMap;
use crate::util::rlimit::ResourceLimit;

/// An expression: an index into the manager's tables, -1 for Z3's null pointer.
pub type Expr = i32;
/// A declaration: an index into `func_decls`, -1 for a variable or quantifier.
pub type Decl = i32;
/// A sort: an index into `sort_names`.
pub type Sort = i32;

pub const KIND_APP: u8 = 0;
pub const KIND_VAR: u8 = 1;
pub const KIND_QUANTIFIER: u8 = 2;

pub const SORT_BOOL: Sort = 0;
pub const SORT_INT: Sort = 1;
pub const SORT_REAL: Sort = 2;

pub const FAMILY_BASIC: i32 = 0;
pub const FAMILY_ARITH: i32 = 1;
pub const FAMILY_USER: i32 = 2;
// Model values: the elements that a model gives to an uninterpreted sort.
pub const FAMILY_MODEL_VALUE: i32 = 3;

pub const OP_TRUE: i32 = 0;
pub const OP_FALSE: i32 = 1;
pub const OP_EQ: i32 = 2;
pub const OP_DISTINCT: i32 = 3;
pub const OP_ITE: i32 = 4;
pub const OP_AND: i32 = 5;
pub const OP_OR: i32 = 6;
pub const OP_XOR: i32 = 7;
pub const OP_NOT: i32 = 8;
pub const OP_IMPLIES: i32 = 9;
pub const OP_NUM: i32 = 10;
pub const OP_LE: i32 = 11;
pub const OP_GE: i32 = 12;
pub const OP_LT: i32 = 13;
pub const OP_GT: i32 = 14;
pub const OP_ADD: i32 = 15;
pub const OP_SUB: i32 = 16;
pub const OP_UMINUS: i32 = 17;
pub const OP_MUL: i32 = 18;
pub const OP_IDIV: i32 = 19;
pub const OP_MOD: i32 = 20;
pub const OP_ABS: i32 = 21;
pub const OP_PATTERN: i32 = 22;
pub const OP_DIV: i32 = 23;
pub const OP_TO_REAL: i32 = 24;
pub const OP_TO_INT: i32 = 25;
pub const OP_IS_INT: i32 = 26;
// Z3's div0, idiv0 and mod0: division by zero, which theory_lra's found_underspecified equates with
// the division it stands for.
pub const OP_DIV0: i32 = 27;
pub const OP_IDIV0: i32 = 28;
pub const OP_MOD0: i32 = 29;
pub const OP_UNINTERPRETED: i32 = 30;
const OP_MODEL_VALUE: i32 = 31;

/// A Z3 symbol: a string, or a number for a numerical symbol, which Z3 prints as k!n.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SmtSymbol {
    Name(String),
    Number(u64),
}

/// The symbol as JavaScript's `String(symbol)` prints it.
impl fmt::Display for SmtSymbol {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SmtSymbol::Name(name) => formatter.write_str(name),
            SmtSymbol::Number(number) => write!(formatter, "{number}"),
        }
    }
}

pub fn get_symbol_name(symbol: &SmtSymbol) -> String {
    match symbol {
        SmtSymbol::Number(number) => format!("k!{number}"),
        SmtSymbol::Name(name) => name.clone(),
    }
}

#[derive(Clone, Debug)]
pub struct FuncDecl {
    pub name: SmtSymbol,
    pub family: i32,
    pub op: i32,
    pub domain: Vec<Sort>,
    pub range: Sort,
    pub is_skolem: bool,
    /// Z3's small id of the declaration, which its matcher hashes.
    pub small_id: i32,
}

#[derive(Clone, Debug)]
pub struct QuantifierData {
    pub is_forall: bool,
    pub sorts: Vec<Sort>,
    /// The names of the variables, which tell apart quantifiers that differ only in them, as in Z3.
    pub names: Vec<SmtSymbol>,
    pub body: Expr,
    /// Applications of the pattern declaration to the terms of each multi-pattern.
    pub patterns: Vec<Expr>,
    pub weight: i32,
    pub qid: String,
}

const BUILTIN_DECLS: [(&str, i32, i32, Sort); 30] = [
    ("true", FAMILY_BASIC, OP_TRUE, SORT_BOOL),
    ("false", FAMILY_BASIC, OP_FALSE, SORT_BOOL),
    ("=", FAMILY_BASIC, OP_EQ, SORT_BOOL),
    ("distinct", FAMILY_BASIC, OP_DISTINCT, SORT_BOOL),
    ("ite", FAMILY_BASIC, OP_ITE, -1),
    ("and", FAMILY_BASIC, OP_AND, SORT_BOOL),
    ("or", FAMILY_BASIC, OP_OR, SORT_BOOL),
    ("xor", FAMILY_BASIC, OP_XOR, SORT_BOOL),
    ("not", FAMILY_BASIC, OP_NOT, SORT_BOOL),
    ("=>", FAMILY_BASIC, OP_IMPLIES, SORT_BOOL),
    ("num", FAMILY_ARITH, OP_NUM, SORT_INT),
    ("<=", FAMILY_ARITH, OP_LE, SORT_BOOL),
    (">=", FAMILY_ARITH, OP_GE, SORT_BOOL),
    ("<", FAMILY_ARITH, OP_LT, SORT_BOOL),
    (">", FAMILY_ARITH, OP_GT, SORT_BOOL),
    ("+", FAMILY_ARITH, OP_ADD, SORT_INT),
    ("-", FAMILY_ARITH, OP_SUB, SORT_INT),
    ("-", FAMILY_ARITH, OP_UMINUS, SORT_INT),
    ("*", FAMILY_ARITH, OP_MUL, SORT_INT),
    ("div", FAMILY_ARITH, OP_IDIV, SORT_INT),
    ("mod", FAMILY_ARITH, OP_MOD, SORT_INT),
    ("abs", FAMILY_ARITH, OP_ABS, SORT_INT),
    ("pattern", FAMILY_BASIC, OP_PATTERN, SORT_BOOL),
    ("/", FAMILY_ARITH, OP_DIV, SORT_REAL),
    ("to_real", FAMILY_ARITH, OP_TO_REAL, SORT_REAL),
    ("to_int", FAMILY_ARITH, OP_TO_INT, SORT_INT),
    ("is_int", FAMILY_ARITH, OP_IS_INT, SORT_BOOL),
    ("/0", FAMILY_ARITH, OP_DIV0, SORT_REAL),
    ("div0", FAMILY_ARITH, OP_IDIV0, SORT_INT),
    ("mod0", FAMILY_ARITH, OP_MOD0, SORT_INT),
];

// Z3's family ids and decl kinds, which its AST hashes include.
const Z3_BASIC_FAMILY: u32 = 0;
const Z3_PATTERN_FAMILY: u32 = 2;
const Z3_MODEL_VALUE_FAMILY: u32 = 3;
const Z3_USER_SORT_FAMILY: u32 = 4;
const Z3_ARITH_FAMILY: u32 = 5;
const Z3_RECFUN_FAMILY: u32 = 10;
const Z3_NULL: u32 = 0xffff_ffff;

// The name, Z3 decl kind and arity of each builtin, whose Z3 declaration has this many arguments
// whatever the number of arguments of the application (-1 for the arguments' own number).
fn get_z3_builtin(op: i32) -> Option<(&'static str, u32, i32)> {
    Some(match op {
        OP_TRUE => ("true", 0, 0),
        OP_FALSE => ("false", 1, 0),
        OP_EQ => ("=", 2, 2),
        OP_DISTINCT => ("distinct", 3, -1),
        OP_ITE => ("if", 4, 3),
        OP_AND => ("and", 5, 2),
        OP_OR => ("or", 6, 2),
        OP_XOR => ("xor", 7, 2),
        OP_NOT => ("not", 8, 1),
        OP_IMPLIES => ("=>", 9, 2),
        OP_LE => ("<=", 2, 2),
        OP_GE => (">=", 3, 2),
        OP_LT => ("<", 4, 2),
        OP_GT => (">", 5, 2),
        OP_ADD => ("+", 6, 2),
        OP_SUB => ("-", 7, 2),
        OP_UMINUS => ("-", 8, 1),
        OP_MUL => ("*", 9, 2),
        OP_IDIV => ("div", 11, 2),
        OP_MOD => ("mod", 16, 2),
        OP_ABS => ("abs", 21, 1),
        OP_PATTERN => ("pattern", 0, -1),
        OP_DIV => ("/", 10, 2),
        OP_TO_REAL => ("to_real", 18, 1),
        OP_TO_INT => ("to_int", 19, 1),
        OP_IS_INT => ("is_int", 20, 1),
        OP_DIV0 => ("/0", 12, 2),
        OP_IDIV0 => ("div0", 13, 2),
        OP_MOD0 => ("mod0", 17, 2),
        _ => return None,
    })
}

// The small ids of the Int declarations Z3 makes when it starts, from arith_decl_plugin::set_manager,
// which Real terms share. The declarations of Real terms only have the ids of Real's /, Int's
// to_real, Real's to_int and is_int. Z3 makes =, ite, distinct, pattern, numeral, /0, div0 and mod0
// declarations per signature on first use, so they get -1 here, and their small ids are kept by
// signature.
fn get_z3_small_id(op: i32) -> i32 {
    match op {
        OP_TRUE => 1,
        OP_FALSE => 2,
        OP_AND => 3,
        OP_OR => 4,
        OP_XOR => 5,
        OP_NOT => 6,
        OP_IMPLIES => 7,
        OP_LE => 17,
        OP_GE => 18,
        OP_LT => 19,
        OP_GT => 20,
        OP_ADD => 36,
        OP_SUB => 37,
        OP_MUL => 38,
        OP_IDIV => 39,
        OP_MOD => 41,
        OP_UMINUS => 42,
        OP_ABS => 50,
        OP_DIV => 24,
        OP_TO_REAL => 43,
        OP_TO_INT => 45,
        OP_IS_INT => 47,
        _ => -1,
    }
}

// The small id of the first sort or declaration a problem declares, after Z3's own.
const FIRST_DECLARED_SMALL_ID: i32 = 143;

// The ids of Z3's own expressions when it starts: the undef proof, true and false, then pi, euler, a
// bit-vector numeral, fifteen real variables and a sum of two of them, which no problem shares.
const FIRST_FREE_ID: i32 = 22;
// MAX_SMALL_NUM_TO_CACHE: arith_decl_plugin holds the numerals below it once it makes them.
const MAX_SMALL_NUM_TO_CACHE: usize = 16;
// The sorts that finite_set_decl_plugin::init makes.
const NUM_FINITE_SET_PLUGIN_SORTS: usize = 7;

// The multiplier of the hashes of the application table and of the builtin hashes' cache.
const GOLDEN_MULTIPLIER: i32 = 0x9e37_79b1_u32 as i32;

// symbol::hash: a numerical symbol hashes to its number.
fn get_symbol_hash(symbol: &SmtSymbol) -> u32 {
    match symbol {
        SmtSymbol::Number(number) => *number as u32,
        SmtSymbol::Name(name) => string_hash(name, 17),
    }
}

/// Whether a sort is Int or Real.
pub fn is_arith_sort(sort: Sort) -> bool {
    sort == SORT_INT || sort == SORT_REAL
}

// mpz_manager::hash: the absolute value of an integer below 2^32, else the hash of its 32-bit digits,
// least significant first.
fn get_integer_hash(value: &Int) -> u32 {
    let magnitude = value.abs();
    if magnitude <= 0xffff_ffff_i64 {
        return magnitude.to_i64().map_or(0, |small| small as u32);
    }
    let mask = Int::from(0xffff_ffff_u32);
    let mut bytes = Vec::new();
    let mut rest = magnitude;
    while rest > 0 {
        let digit = (&rest & &mask).to_i64().map_or(0, |digit| digit as u32);
        bytes.extend_from_slice(&digit.to_le_bytes());
        rest = &rest >> 32;
    }
    bytes_hash(&bytes, 17)
}

// decl_info::hash.
fn get_info_hash(family: u32, kind: u32, parameter_hashes: &[u32]) -> u32 {
    mk_mix(
        family,
        kind,
        if parameter_hashes.is_empty() {
            0
        } else {
            get_composite_hash(parameter_hashes, 17)
        },
    )
}

// astArrayHash over handles, whose hashes `hashes` holds.
fn get_array_hash(items: &[i32], hashes: &[u32], init_value: u32) -> u32 {
    let items: Vec<u32> = items.iter().map(|item| *item as u32).collect();
    ast_array_hash(&items, |item| hashes[item as usize], init_value)
}

// The kinds of an integer signature, in its low three bits.
const SIGNATURE_EQ: i64 = 0;
const SIGNATURE_ITE: i64 = 1;
const SIGNATURE_DIV0: i64 = 2;
const SIGNATURE_MODEL_VALUE: i64 = 3;
const SIGNATURE_NUMERAL: i64 = 4;

/// The signature of a builtin declaration that Z3 makes on first use: an integer whose low three
/// bits tell its kind, or a distinct or pattern by its domain (the TypeScript's string key).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum SignatureKey {
    Number(i64),
    Domain(Decl, Vec<Sort>),
}

impl fmt::Display for SignatureKey {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SignatureKey::Number(number) => write!(formatter, "{number}"),
            SignatureKey::Domain(decl, sorts) => {
                let sorts: Vec<String> = sorts.iter().map(Sort::to_string).collect();
                write!(formatter, "{decl}:{}", sorts.join(","))
            }
        }
    }
}

fn get_not_held_error(key: &SignatureKey) -> SmtError {
    SmtError::Invariant(format!("the signature {key} is not held"))
}

// A builtin declaration that Z3 makes once per signature: its small id, and the references that
// applications and model values hold to it.
struct SignatureDecl {
    small_id: i32,
    ref_count: i32,
}

/// The key of a numeral, model value, variable or quantifier in the table: the TypeScript's
/// string keys, `n<value>`, `r<value>`, `m<sort>:<index>`, `v<index>:<sort>` and `q…` (which leaves
/// out the qid).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum TableKey {
    Int(Int),
    Real(Rational),
    ModelValue(Sort, i32),
    Var(i32, Sort),
    Quantifier {
        is_forall: bool,
        sorts: Vec<Sort>,
        names: Vec<SmtSymbol>,
        body: Expr,
        patterns: Vec<Expr>,
        weight: i32,
    },
}

/// The name, Z3 decl kind and domain of the Z3 declaration of a builtin application.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BuiltinSignature {
    pub name: &'static str,
    pub kind: u32,
    pub domain: Vec<Sort>,
}

pub struct AstManager {
    // The tables of the expressions, indexed by expression.
    pub kinds: Vec<u8>,
    // The declaration of an application.
    pub decls: Vec<Decl>,
    // The arguments of every expression end to end: those of expr are arg_pool[arg_starts[expr]] up
    // to arg_pool[arg_starts[expr + 1]]. Variables and constants take an empty range and a
    // quantifier takes its body.
    arg_pool: Vec<Expr>,
    arg_starts: Vec<u32>,
    pub sorts: Vec<Sort>,
    // The index of a variable or model value, or of a numeral's value in numeral_values.
    pub values: Vec<i32>,
    numeral_values: Vec<Rational>,
    // The integer numerals by value, which finds one without building its key in the table.
    int_numerals: HashMap<Int, Expr>,
    // One more than the largest free de Bruijn index, so 0 means the expression is ground.
    pub free_var_bounds: Vec<i32>,
    pub has_quantifier_flags: Vec<u8>,
    pub depths: Vec<i32>,
    // Z3's hash of each expression, which orders Z3's hash tables.
    pub hashes: Vec<u32>,
    pub quantifiers: HashMap<Expr, QuantifierData>,
    // The marks that the rewriters of this manager share to flatten conjunctions and disjunctions.
    pub flat_literals: FlatLiterals,
    pub func_decls: Vec<FuncDecl>,
    pub sort_names: Vec<String>,
    sort_hashes: Vec<u32>,
    // The hash of each uninterpreted declaration, and of each builtin by its Z3 declaration.
    decl_hashes: Vec<u32>,
    // The hash of each builtin declaration other than pattern by op, argument sort, range and number
    // of arguments: open addressing with linear probing, with the four keys of slot i at 4 i in
    // builtin_keys and -1 for an empty slot.
    builtin_keys: Vec<i32>,
    builtin_hashes: Vec<u32>,
    num_builtin_hashes: usize,
    // The hash of each pattern declaration by its domain and range.
    pattern_hashes: HashMap<(Vec<Sort>, Sort), u32>,
    table: HashMap<TableKey, Expr>,
    // The hash-consing table of applications: open addressing with linear probing over the handles,
    // -1 for an empty slot, which takes a few bytes per application where a map of buckets takes
    // dozens. Applications stay in it when they are deleted, so a lookup can create them again.
    app_handles: Vec<i32>,
    app_hashes: Vec<i32>,
    num_apps: usize,
    // id_gen for sorts and declarations: the small id of the next one, and the ids of deleted ones,
    // which Z3 reuses the last freed first. Z3 keeps the declarations of = and ite, and deletes the
    // others with their last reference.
    next_small_id: i32,
    free_small_ids: Vec<i32>,
    num_decls: i64,
    // The small id and the number of live applications of each builtin declaration that Z3 makes
    // per signature, by its signature.
    signature_decls: HashMap<SignatureKey, SignatureDecl>,
    // The references to each user declaration: the script holds the declared ones, and applications
    // and models hold the fresh ones. A deleted declaration keeps its small id here, in case an
    // application of it is created again.
    decl_ref_counts: Vec<i32>,
    // The named expressions of the recfun plugin, by declaration, hashed by `get_decl_hash`.
    pub macros: ObjMap<Expr>,
    deleted_decls: HashSet<Decl>,
    // ast_manager::m_fresh_id, which numbers fresh declarations and variable names.
    fresh_id: u64,
    // Z3's id of each expression, which orders Z3's sorts. Like Z3, the manager counts references and
    // gives the id of a deleted expression to the next expression it creates, so its ids follow
    // Z3's. A deleted expression stays in the tables with the id -1 until it is created again.
    pub ids: Vec<i32>,
    ref_counts: Vec<i32>,
    free_ids: Vec<i32>,
    next_id: i32,
    num_live: i64,
    // The expressions that the open with_temporaries hold, like the expr_ref temporaries of Z3
    // functions on the C++ stack: the innermost holds those from temporaries_mark on, and -1 marks
    // that no temporaries are held.
    temporaries: Vec<Expr>,
    temporaries_mark: isize,
    // m_small_ints and m_small_reals: the numerals below MAX_SMALL_NUM_TO_CACHE, which are held.
    small_ints: [Option<Expr>; MAX_SMALL_NUM_TO_CACHE],
    small_reals: [Option<Expr>; MAX_SMALL_NUM_TO_CACHE],
    is_finite_set_plugin_initialized: bool,
    pub true_expr: Expr,
    pub false_expr: Expr,
    pub limit: ResourceLimit,
}

impl AstManager {
    pub fn new(limit: ResourceLimit) -> AstManager {
        let mut manager = AstManager {
            kinds: Vec::new(),
            decls: Vec::new(),
            arg_pool: Vec::new(),
            arg_starts: vec![0],
            sorts: Vec::new(),
            values: Vec::new(),
            numeral_values: Vec::new(),
            int_numerals: HashMap::new(),
            free_var_bounds: Vec::new(),
            has_quantifier_flags: Vec::new(),
            depths: Vec::new(),
            hashes: Vec::new(),
            quantifiers: HashMap::new(),
            flat_literals: FlatLiterals::new(),
            func_decls: Vec::new(),
            sort_names: vec!["Bool".into(), "Int".into(), "Real".into()],
            sort_hashes: vec![
                combine_hash(
                    string_hash("Bool", 17),
                    get_info_hash(Z3_BASIC_FAMILY, 0, &[]),
                ),
                combine_hash(
                    string_hash("Int", 17),
                    get_info_hash(Z3_ARITH_FAMILY, 1, &[]),
                ),
                combine_hash(
                    string_hash("Real", 17),
                    get_info_hash(Z3_ARITH_FAMILY, 0, &[]),
                ),
            ],
            decl_hashes: Vec::new(),
            builtin_keys: vec![-1; 4 * 256],
            builtin_hashes: vec![0; 256],
            num_builtin_hashes: 0,
            pattern_hashes: HashMap::new(),
            table: HashMap::new(),
            app_handles: vec![-1; 1024],
            app_hashes: vec![0; 1024],
            num_apps: 0,
            next_small_id: FIRST_DECLARED_SMALL_ID,
            free_small_ids: Vec::new(),
            num_decls: i64::from(FIRST_DECLARED_SMALL_ID),
            signature_decls: HashMap::new(),
            decl_ref_counts: Vec::new(),
            macros: ObjMap::new(),
            deleted_decls: HashSet::new(),
            fresh_id: 0,
            ids: Vec::new(),
            ref_counts: Vec::new(),
            free_ids: Vec::new(),
            next_id: 1,
            num_live: 0,
            temporaries: Vec::new(),
            temporaries_mark: -1,
            small_ints: [None; MAX_SMALL_NUM_TO_CACHE],
            small_reals: [None; MAX_SMALL_NUM_TO_CACHE],
            is_finite_set_plugin_initialized: false,
            true_expr: -1,
            false_expr: -1,
            limit,
        };
        for builtin in BUILTIN_DECLS {
            manager.func_decls.push(FuncDecl {
                name: SmtSymbol::Name(builtin.0.into()),
                family: builtin.1,
                op: builtin.2,
                domain: Vec::new(),
                range: builtin.3,
                is_skolem: false,
                small_id: get_z3_small_id(builtin.2),
            });
        }
        let (Ok(true_expr), Ok(false_expr)) = (
            manager.mk_app(OP_TRUE, &[], SORT_BOOL),
            manager.mk_app(OP_FALSE, &[], SORT_BOOL),
        ) else {
            unreachable!("true and false have Z3 declarations");
        };
        manager.true_expr = true_expr;
        manager.false_expr = false_expr;
        manager.inc_ref(true_expr);
        manager.inc_ref(false_expr);
        manager.next_id = FIRST_FREE_ID;
        manager
    }

    pub fn get_ref_count(&self, expr: Expr) -> i32 {
        self.ref_counts[expr as usize]
    }

    /// get_num_asts: the live expressions, declarations and sorts, with Z3's own expressions.
    pub fn get_num_asts(&self) -> i64 {
        self.num_live + i64::from(FIRST_FREE_ID) - 2 + self.num_decls
    }

    // The declaration that a held signature names.
    fn get_signature_decl(&mut self, key: &SignatureKey) -> Result<&mut SignatureDecl, SmtError> {
        self.signature_decls
            .get_mut(key)
            .ok_or_else(|| get_not_held_error(key))
    }

    fn mk_small_id(&mut self) -> i32 {
        self.num_decls += 1;
        match self.free_small_ids.pop() {
            Some(small_id) => small_id,
            None => {
                let small_id = self.next_small_id;
                self.next_small_id += 1;
                small_id
            }
        }
    }

    /// finite_set_decl_plugin::init, which the first final check of theory_finite_set runs when it
    /// makes a set.range declaration: the plugin makes the sorts A and B, three FiniteSet sorts and
    /// two Array sorts, which the manager keeps. The set.range declaration is released at once.
    pub fn init_finite_set_plugin(&mut self) {
        if self.is_finite_set_plugin_initialized {
            return;
        }
        self.is_finite_set_plugin_initialized = true;
        for _ in 0..NUM_FINITE_SET_PLUGIN_SORTS {
            self.mk_small_id();
        }
        let small_id = self.mk_small_id();
        self.free_small_id(small_id);
    }

    // Sets the hash and the reference count of a new declaration, past the end of either table.
    fn set_decl_hash(&mut self, decl: Decl, hash: u32) {
        let index = decl as usize;
        if self.decl_hashes.len() <= index {
            self.decl_hashes.resize(index + 1, 0);
        }
        self.decl_hashes[index] = hash;
    }

    fn set_decl_ref_count(&mut self, decl: Decl, count: i32) {
        let index = decl as usize;
        if self.decl_ref_counts.len() <= index {
            self.decl_ref_counts.resize(index + 1, 0);
        }
        self.decl_ref_counts[index] = count;
    }

    /// insert_macro: cmd_context keeps a named expression as a recursive function with one case,
    /// whose declaration and case predicate it holds. The recfun plugin maps the declaration to the
    /// expression, which a model of the context takes as the declaration's interpretation.
    pub fn mk_macro(&mut self, name: &str, expr: Expr) {
        let decl = self.func_decls.len() as Decl;
        let name = SmtSymbol::Name(name.into());
        let range = self.sorts[expr as usize];
        let hash =
            self.get_func_decl_hash(&name, &[], range, get_info_hash(Z3_RECFUN_FAMILY, 0, &[0]));
        self.set_decl_hash(decl, hash);
        let small_id = self.mk_small_id();
        self.func_decls.push(FuncDecl {
            name,
            family: FAMILY_USER,
            op: OP_UNINTERPRETED,
            domain: Vec::new(),
            range,
            is_skolem: false,
            small_id,
        });
        self.set_decl_ref_count(decl, 1);
        self.mk_small_id();
        self.macros
            .insert(decl as u32, self.get_decl_hash(decl), expr);
    }

    // The signature of a builtin declaration that Z3 makes on first use, or None for a declaration
    // that is not one. The low three bits of an integer signature tell its kind: an equality or ite
    // by sort, a division by zero or model value by declaration, or a numeral by its value, which a
    // numeral expression has alone. A distinct or pattern is keyed by its domain.
    fn get_signature(&self, expr: Expr) -> Option<SignatureKey> {
        let decl = self.decls[expr as usize];
        if decl == OP_NUM {
            return Some(SignatureKey::Number(
                8 * i64::from(self.values[expr as usize]) + SIGNATURE_NUMERAL,
            ));
        }
        if decl == OP_EQ {
            return Some(SignatureKey::Number(
                8 * i64::from(self.sorts[self.get_arg(expr, 0) as usize]) + SIGNATURE_EQ,
            ));
        }
        if decl == OP_ITE {
            return Some(SignatureKey::Number(
                8 * i64::from(self.sorts[expr as usize]) + SIGNATURE_ITE,
            ));
        }
        if decl == OP_DISTINCT || decl == OP_PATTERN {
            return Some(SignatureKey::Domain(
                decl,
                self.map_args(expr, |arg, _| self.sorts[arg as usize]),
            ));
        }
        self.get_decl_signature(decl)
    }

    // The signature of a builtin declaration that each of its applications shares, a division by
    // zero or a model value, or None for any other declaration.
    fn get_decl_signature(&self, decl: Decl) -> Option<SignatureKey> {
        if decl == OP_DIV0 || decl == OP_IDIV0 || decl == OP_MOD0 {
            return Some(SignatureKey::Number(8 * i64::from(decl) + SIGNATURE_DIV0));
        }
        if self.func_decls[decl as usize].family == FAMILY_MODEL_VALUE {
            return Some(SignatureKey::Number(
                8 * i64::from(decl) + SIGNATURE_MODEL_VALUE,
            ));
        }
        None
    }

    /// The id that Z3 gives the declaration of an application.
    pub fn get_decl_id(&self, expr: Expr) -> Result<i32, SmtError> {
        let decl = self.decls[expr as usize];
        if decl < 0 {
            return Err(SmtError::Invariant(
                "the expression is not an application".into(),
            ));
        }
        match self.get_signature(expr) {
            None => Ok(self.func_decls[decl as usize].small_id),
            Some(signature) => self
                .signature_decls
                .get(&signature)
                .map(|signature_decl| signature_decl.small_id)
                .ok_or_else(|| get_not_held_error(&signature)),
        }
    }

    // An application holds its declaration, which Z3 makes with its first application.
    fn hold_decl(&mut self, expr: Expr) {
        let decl = self.decls[expr as usize];
        if self.func_decls[decl as usize].family == FAMILY_USER {
            self.inc_decl_ref(decl);
            return;
        }
        if let Some(key) = self.get_signature(expr) {
            self.hold_signature(decl, key);
        }
    }

    // Holds the declaration of a signature, which Z3 makes when it is first held.
    fn hold_signature(&mut self, decl: Decl, key: SignatureKey) {
        if let Some(signature_decl) = self.signature_decls.get_mut(&key) {
            signature_decl.ref_count += 1;
            return;
        }
        let small_id = self.mk_small_id();
        // Z3 keeps the equality and ite declarations once it makes them.
        self.signature_decls.insert(
            key,
            SignatureDecl {
                small_id,
                ref_count: if decl == OP_EQ || decl == OP_ITE {
                    2
                } else {
                    1
                },
            },
        );
        if decl != OP_NUM && self.func_decls[decl as usize].family == FAMILY_MODEL_VALUE {
            self.func_decls[decl as usize].small_id = small_id;
        }
    }

    // The small id of the declaration a deleted application releases for good, or -1 when the
    // declaration stays.
    fn release_decl(&mut self, expr: Expr) -> Result<i32, SmtError> {
        let decl = self.decls[expr as usize];
        if self.func_decls[decl as usize].family == FAMILY_USER {
            self.decl_ref_counts[decl as usize] -= 1;
            if self.decl_ref_counts[decl as usize] > 0 {
                return Ok(-1);
            }
            self.deleted_decls.insert(decl);
            return Ok(self.func_decls[decl as usize].small_id);
        }
        match self.get_signature(expr) {
            Some(key) => self.release_signature(&key),
            None => Ok(-1),
        }
    }

    // The small id of the declaration of a signature that loses its last reference, or -1.
    fn release_signature(&mut self, key: &SignatureKey) -> Result<i32, SmtError> {
        let signature_decl = self.get_signature_decl(key)?;
        signature_decl.ref_count -= 1;
        if signature_decl.ref_count > 0 {
            return Ok(-1);
        }
        let small_id = signature_decl.small_id;
        self.signature_decls.remove(key);
        Ok(small_id)
    }

    pub fn inc_ref(&mut self, expr: Expr) {
        self.ref_counts[expr as usize] += 1;
    }

    /// A model holds a declaration as an application does: Z3 counts the references to a func_decl
    /// together, so a builtin declaration with a signature (a model's div0 or model value) is
    /// counted under it, with the applications that hold it. Z3's plugins keep the other builtin
    /// declarations.
    pub fn inc_decl_ref(&mut self, decl: Decl) {
        if self.func_decls[decl as usize].family == FAMILY_USER {
            if self.deleted_decls.remove(&decl) {
                self.func_decls[decl as usize].small_id = self.mk_small_id();
            }
            self.decl_ref_counts[decl as usize] += 1;
            return;
        }
        if let Some(key) = self.get_decl_signature(decl) {
            self.hold_signature(decl, key);
        }
    }

    pub fn dec_decl_ref(&mut self, decl: Decl) -> Result<(), SmtError> {
        if self.func_decls[decl as usize].family == FAMILY_USER {
            self.decl_ref_counts[decl as usize] -= 1;
            if self.decl_ref_counts[decl as usize] > 0 {
                return Ok(());
            }
            self.deleted_decls.insert(decl);
            self.free_small_id(self.func_decls[decl as usize].small_id);
            return Ok(());
        }
        let small_id = match self.get_decl_signature(decl) {
            Some(key) => self.release_signature(&key)?,
            None => -1,
        };
        if small_id != -1 {
            self.free_small_id(small_id);
        }
        Ok(())
    }

    fn free_small_id(&mut self, small_id: i32) {
        self.free_small_ids.push(small_id);
        self.num_decls -= 1;
    }

    /// Runs body, holding each expression it creates until it returns, then releases them, the last
    /// created first. The caller gets a reference to the result, and releases it.
    pub fn with_temporaries(
        &mut self,
        body: impl FnOnce(&mut Self) -> Result<Expr, SmtError>,
    ) -> Result<Expr, SmtError> {
        self.with_temporaries_keeping(body, |result| vec![*result])
    }

    /// `withTemporaries` with its `getKept`: the caller gets a reference to each expression that
    /// get_kept picks from the result.
    pub fn with_temporaries_keeping<T>(
        &mut self,
        body: impl FnOnce(&mut Self) -> Result<T, SmtError>,
        get_kept: impl FnOnce(&T) -> Vec<Expr>,
    ) -> Result<T, SmtError> {
        let outer = self.begin_temporaries();
        let result = body(self)?;
        for kept in get_kept(&result) {
            self.inc_ref(kept);
        }
        self.end_temporaries(outer)?;
        Ok(result)
    }

    /// with_temporaries without closures, for the hot paths: the caller passes what
    /// begin_temporaries returns to end_temporaries, and takes its references before it.
    pub fn begin_temporaries(&mut self) -> isize {
        let outer = self.temporaries_mark;
        self.temporaries_mark = self.temporaries.len() as isize;
        outer
    }

    pub fn end_temporaries(&mut self, outer: isize) -> Result<(), SmtError> {
        // A mark of -1 releases them all, as the TypeScript's loop down to -1 does.
        let mark = self.temporaries_mark.max(0) as usize;
        self.temporaries_mark = outer;
        for index in (mark..self.temporaries.len()).rev() {
            self.dec_ref(self.temporaries[index])?;
        }
        self.temporaries.truncate(mark);
        Ok(())
    }

    /// Runs body without temporaries, for code whose references are counted explicitly.
    pub fn without_temporaries<T>(
        &mut self,
        body: impl FnOnce(&mut Self) -> Result<T, SmtError>,
    ) -> Result<T, SmtError> {
        let outer = self.temporaries_mark;
        self.temporaries_mark = -1;
        let result = body(self)?;
        self.temporaries_mark = outer;
        Ok(result)
    }

    /// without_temporaries without a closure, for a body that needs more than the manager: the
    /// caller passes what suspend_temporaries returns to restore_temporaries.
    pub fn suspend_temporaries(&mut self) -> isize {
        let outer = self.temporaries_mark;
        self.temporaries_mark = -1;
        outer
    }

    pub fn restore_temporaries(&mut self, outer: isize) {
        self.temporaries_mark = outer;
    }

    /// Hands a reference the caller owns to the innermost with_temporaries, or releases it now.
    pub fn release_later(&mut self, expr: Expr) -> Result<(), SmtError> {
        if self.temporaries_mark == -1 {
            return self.dec_ref(expr);
        }
        self.temporaries.push(expr);
        Ok(())
    }

    /// dec_ref and delete_node: an expression without references is deleted, and so are its
    /// children and declaration that lose their last reference, in the order of Z3's worklist. A
    /// released declaration's small id goes on the worklist as -1 - id.
    pub fn dec_ref(&mut self, expr: Expr) -> Result<(), SmtError> {
        if self.ids[expr as usize] == -1 {
            return Ok(());
        }
        self.ref_counts[expr as usize] -= 1;
        if self.ref_counts[expr as usize] > 0 {
            return Ok(());
        }
        let mut worklist = vec![expr];
        while let Some(node) = worklist.pop() {
            if node < 0 {
                self.free_small_id(-1 - node);
                continue;
            }
            self.delete_node(node);
            if self.kinds[node as usize] == KIND_APP {
                let small_id = self.release_decl(node)?;
                if small_id != -1 {
                    worklist.push(-1 - small_id);
                }
            }
            // The children: the arguments of an application, and the body and then the patterns
            // of a quantifier.
            if self.kinds[node as usize] != KIND_QUANTIFIER {
                let end = self.arg_starts[node as usize + 1] as usize;
                for index in self.arg_starts[node as usize] as usize..end {
                    self.release_child(self.arg_pool[index], &mut worklist);
                }
                continue;
            }
            let data = self.get_quantifier(node)?;
            let (body, patterns) = (data.body, data.patterns.clone());
            self.release_child(body, &mut worklist);
            for pattern in patterns {
                self.release_child(pattern, &mut worklist);
            }
        }
        Ok(())
    }

    fn release_child(&mut self, child: Expr, worklist: &mut Vec<Expr>) {
        self.ref_counts[child as usize] -= 1;
        if self.ref_counts[child as usize] == 0 {
            worklist.push(child);
        }
    }

    fn delete_node(&mut self, expr: Expr) {
        self.num_live -= 1;
        self.free_ids.push(self.ids[expr as usize]);
        self.ids[expr as usize] = -1;
    }

    // The child of a node at index: the arguments of an application, and the body and then the
    // patterns of a quantifier.
    fn get_child(&self, expr: Expr, index: usize) -> Option<Expr> {
        if self.kinds[expr as usize] != KIND_QUANTIFIER {
            return (index < self.get_num_args(expr)).then(|| self.get_arg(expr, index));
        }
        let data = self.quantifier_of(expr);
        match index {
            0 => Some(data.body),
            _ => data.patterns.get(index - 1).copied(),
        }
    }

    // register_node_core: a new expression takes an id and a reference to each child. A deleted
    // child is created again first, as the TypeScript's recursion through revive does, here with a
    // stack of its own, so that a deep chain of deleted terms does not exhaust the call stack.
    fn register_node(&mut self, expr: Expr) {
        self.enter_node(expr);
        let mut stack = vec![(expr, 0)];
        while let Some(frame) = stack.last_mut() {
            let (node, index) = *frame;
            if let Some(child) = self.get_child(node, index) {
                frame.1 += 1;
                if self.ids[child as usize] == -1 {
                    self.enter_node(child);
                    stack.push((child, 0));
                } else {
                    self.inc_ref(child);
                }
                continue;
            }
            stack.pop();
            if self.kinds[node as usize] == KIND_APP {
                self.hold_decl(node);
            }
            if self.temporaries_mark != -1 {
                self.inc_ref(node);
                self.temporaries.push(node);
            }
            // The parent's reference to the child it revived.
            if !stack.is_empty() {
                self.inc_ref(node);
            }
        }
    }

    fn enter_node(&mut self, expr: Expr) {
        self.ids[expr as usize] = match self.free_ids.pop() {
            Some(id) => id,
            None => {
                let id = self.next_id;
                self.next_id += 1;
                id
            }
        };
        self.num_live += 1;
        self.ref_counts[expr as usize] = 0;
    }

    /// The arguments of an application, and the body of a quantifier as its one argument.
    pub fn get_num_args(&self, expr: Expr) -> usize {
        (self.arg_starts[expr as usize + 1] - self.arg_starts[expr as usize]) as usize
    }

    pub fn get_arg(&self, expr: Expr, index: usize) -> Expr {
        self.arg_pool[self.arg_starts[expr as usize] as usize + index]
    }

    /// The arguments as a slice.
    pub fn get_arg_slice(&self, expr: Expr) -> &[Expr] {
        &self.arg_pool
            [self.arg_starts[expr as usize] as usize..self.arg_starts[expr as usize + 1] as usize]
    }

    /// Appends the arguments to target, for a caller that needs them as an array.
    pub fn push_args(&self, expr: Expr, target: &mut Vec<Expr>) {
        target.extend_from_slice(self.get_arg_slice(expr));
    }

    /// A new array of the arguments.
    pub fn get_args(&self, expr: Expr) -> Vec<Expr> {
        self.get_arg_slice(expr).to_vec()
    }

    pub fn map_args<T>(&self, expr: Expr, mut map: impl FnMut(Expr, usize) -> T) -> Vec<T> {
        (0..self.get_num_args(expr))
            .map(|index| map(self.get_arg(expr, index), index))
            .collect()
    }

    pub fn some_arg(&self, expr: Expr, mut predicate: impl FnMut(Expr, usize) -> bool) -> bool {
        (0..self.get_num_args(expr)).any(|index| predicate(self.get_arg(expr, index), index))
    }

    pub fn every_arg(&self, expr: Expr, mut predicate: impl FnMut(Expr, usize) -> bool) -> bool {
        (0..self.get_num_args(expr)).all(|index| predicate(self.get_arg(expr, index), index))
    }

    // A lookup that finds a deleted expression creates it again.
    fn revive(&mut self, expr: Expr) -> Expr {
        if self.ids[expr as usize] == -1 {
            self.register_node(expr);
        }
        expr
    }

    pub fn mk_sort(&mut self, name: &str) -> Sort {
        self.sort_hashes.push(combine_hash(
            string_hash(name, 17),
            get_info_hash(Z3_USER_SORT_FAMILY, (self.sort_names.len() - 3) as u32, &[]),
        ));
        self.sort_names.push(name.into());
        self.mk_small_id();
        (self.sort_names.len() - 1) as Sort
    }

    // The hash of a func_decl node: its name, range, info and domain.
    fn get_func_decl_hash(
        &self,
        name: &SmtSymbol,
        domain: &[Sort],
        range: Sort,
        info_hash: u32,
    ) -> u32 {
        get_array_hash(
            domain,
            &self.sort_hashes,
            combine_hash(
                combine_hash(get_symbol_hash(name), self.sort_hashes[range as usize]),
                info_hash,
            ),
        )
    }

    /// The name, Z3 decl kind and domain of the Z3 declaration of a builtin application.
    pub fn get_builtin_signature(
        &self,
        op: i32,
        args: &[Expr],
    ) -> Result<BuiltinSignature, SmtError> {
        let Some(builtin) = get_z3_builtin(op) else {
            return Err(SmtError::Invariant(format!(
                "the operator {op} has no Z3 declaration"
            )));
        };
        let arg_sort = args
            .get(if op == OP_ITE { 1 } else { 0 })
            .map(|arg| self.sorts[*arg as usize]);
        let arity = if builtin.2 == -1 {
            args.len()
        } else {
            builtin.2 as usize
        };
        let domain = (0..arity)
            .map(|index| {
                if op == OP_PATTERN {
                    Some(self.sorts[args[index] as usize])
                } else if op == OP_ITE && index == 0 {
                    Some(SORT_BOOL)
                } else {
                    arg_sort
                }
            })
            .collect::<Option<Vec<Sort>>>()
            .ok_or_else(|| {
                SmtError::Invariant(format!("the operator {op} has too few arguments"))
            })?;
        Ok(BuiltinSignature {
            name: builtin.0,
            kind: builtin.1,
            domain,
        })
    }

    // The hash of a pattern's Z3 declaration.
    fn get_pattern_hash(&mut self, args: &[Expr], range: Sort) -> Result<u32, SmtError> {
        let key = (
            args.iter()
                .map(|arg| self.sorts[*arg as usize])
                .collect::<Vec<Sort>>(),
            range,
        );
        if let Some(existing) = self.pattern_hashes.get(&key) {
            return Ok(*existing);
        }
        let hash = self.mk_builtin_hash(OP_PATTERN, args, range)?;
        self.pattern_hashes.insert(key, hash);
        Ok(hash)
    }

    // The slot in builtin_hashes of the hash of a builtin's Z3 declaration, other than a pattern's.
    // The domain depends only on the sort of an argument and the number of arguments, which key the
    // cache with the op and range.
    fn get_builtin_slot(&mut self, op: i32, args: &[Expr], range: Sort) -> Result<usize, SmtError> {
        let arg_sort = if args.is_empty() {
            0
        } else {
            let arg = args.get(if op == OP_ITE { 1 } else { 0 }).ok_or_else(|| {
                SmtError::Invariant(format!("the operator {op} has too few arguments"))
            })?;
            self.sorts[*arg as usize]
        };
        let count = args.len() as i32;
        let slot = self.find_builtin_slot(op, arg_sort, range, count);
        if self.builtin_keys[4 * slot] != -1 {
            return Ok(slot);
        }
        let hash = self.mk_builtin_hash(op, args, range)?;
        if 2 * (self.num_builtin_hashes + 1) > self.builtin_hashes.len() {
            let keys = std::mem::take(&mut self.builtin_keys);
            let hashes = std::mem::take(&mut self.builtin_hashes);
            self.builtin_keys = vec![-1; 2 * keys.len()];
            self.builtin_hashes = vec![0; 2 * hashes.len()];
            self.num_builtin_hashes = 0;
            for index in (0..4 * hashes.len()).step_by(4) {
                if keys[index] != -1 {
                    self.insert_builtin_hash(
                        keys[index],
                        keys[index + 1],
                        keys[index + 2],
                        keys[index + 3],
                        hashes[index / 4],
                    );
                }
            }
        }
        Ok(self.insert_builtin_hash(op, arg_sort, range, count, hash))
    }

    // The slot of the builtin hash with these keys, or the free slot where it goes.
    fn find_builtin_slot(&self, op: i32, arg_sort: Sort, range: Sort, count: i32) -> usize {
        let keys = &self.builtin_keys;
        let mask = self.builtin_hashes.len() - 1;
        let hash = op
            .wrapping_mul(GOLDEN_MULTIPLIER)
            .wrapping_add(arg_sort)
            .wrapping_mul(GOLDEN_MULTIPLIER)
            .wrapping_add(range)
            .wrapping_mul(GOLDEN_MULTIPLIER)
            .wrapping_add(count);
        let mut slot = hash as usize & mask;
        while keys[4 * slot] != -1
            && (keys[4 * slot] != op
                || keys[4 * slot + 1] != arg_sort
                || keys[4 * slot + 2] != range
                || keys[4 * slot + 3] != count)
        {
            slot = (slot + 1) & mask;
        }
        slot
    }

    fn insert_builtin_hash(
        &mut self,
        op: i32,
        arg_sort: Sort,
        range: Sort,
        count: i32,
        hash: u32,
    ) -> usize {
        let slot = self.find_builtin_slot(op, arg_sort, range, count);
        self.builtin_keys[4 * slot..4 * slot + 4].copy_from_slice(&[op, arg_sort, range, count]);
        self.builtin_hashes[slot] = hash;
        self.num_builtin_hashes += 1;
        slot
    }

    fn mk_builtin_hash(&self, op: i32, args: &[Expr], range: Sort) -> Result<u32, SmtError> {
        let signature = self.get_builtin_signature(op, args)?;
        let family = if op == OP_PATTERN {
            Z3_PATTERN_FAMILY
        } else if op < OP_NUM {
            Z3_BASIC_FAMILY
        } else {
            Z3_ARITH_FAMILY
        };
        Ok(self.get_func_decl_hash(
            &SmtSymbol::Name(signature.name.into()),
            &signature.domain,
            range,
            get_info_hash(family, signature.kind, &[]),
        ))
    }

    /// The hash of a user declaration, which Z3's tables of declarations hash; 0 for a builtin, as
    /// the TypeScript's `undefined` hashes in its tables.
    pub fn get_decl_hash(&self, decl: Decl) -> u32 {
        self.decl_hashes.get(decl as usize).copied().unwrap_or(0)
    }

    pub fn mk_func_decl(
        &mut self,
        name: SmtSymbol,
        domain: &[Sort],
        range: Sort,
        is_skolem: bool,
    ) -> Decl {
        let decl = self.func_decls.len() as Decl;
        let hash = self.get_func_decl_hash(
            &name,
            domain,
            range,
            if is_skolem {
                get_info_hash(Z3_NULL, Z3_NULL, &[])
            } else {
                0
            },
        );
        self.set_decl_hash(decl, hash);
        let small_id = self.mk_small_id();
        self.func_decls.push(FuncDecl {
            name,
            family: FAMILY_USER,
            op: OP_UNINTERPRETED,
            domain: domain.to_vec(),
            range,
            is_skolem,
            small_id,
        });
        self.set_decl_ref_count(decl, 1);
        decl
    }

    /// mk_fresh_func_decl: without a prefix the name is the numerical symbol of the fresh id.
    pub fn mk_fresh_func_decl(
        &mut self,
        prefix: Option<&SmtSymbol>,
        domain: &[Sort],
        range: Sort,
        is_skolem: bool,
    ) -> Decl {
        let name = match prefix {
            None => SmtSymbol::Number(self.fresh_id),
            Some(prefix) => {
                SmtSymbol::Name(format!("{}!{}", get_symbol_name(prefix), self.fresh_id))
            }
        };
        self.fresh_id += 1;
        let decl = self.mk_func_decl(name, domain, range, is_skolem);
        self.set_decl_ref_count(decl, 0);
        decl
    }

    /// mk_fresh_var_name.
    pub fn mk_fresh_var_name(&mut self, prefix: Option<&str>) -> String {
        let name = format!("{}!{}", prefix.unwrap_or("var"), self.fresh_id);
        self.fresh_id += 1;
        name
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "the arguments of the TypeScript's intern"
    )]
    fn intern(
        &mut self,
        key: TableKey,
        kind: u8,
        decl: Decl,
        args: &[Expr],
        sort: Sort,
        value: i32,
        get_hash: impl FnOnce(&Self) -> u32,
    ) -> Expr {
        if let Some(existing) = self.table.get(&key) {
            let existing = *existing;
            return self.revive(existing);
        }
        let hash = get_hash(self);
        let id = self.create(kind, decl, args, sort, value, hash);
        self.table.insert(key, id);
        self.register_node(id);
        id
    }

    fn create(
        &mut self,
        kind: u8,
        decl: Decl,
        args: &[Expr],
        sort: Sort,
        value: i32,
        hash: u32,
    ) -> Expr {
        let id = self.kinds.len();
        self.hashes.push(hash);
        self.kinds.push(kind);
        self.decls.push(decl);
        // Like Z3, a node keeps its own copy of the arguments, so callers may reuse their arrays.
        self.arg_pool.extend_from_slice(args);
        self.arg_starts.push(self.arg_pool.len() as u32);
        self.sorts.push(sort);
        self.values.push(value);
        let mut free_var_bound = if kind == KIND_VAR { value + 1 } else { 0 };
        let mut has_quantifier = kind == KIND_QUANTIFIER;
        let mut depth = 1;
        for arg in args {
            let arg = *arg as usize;
            if self.free_var_bounds[arg] > free_var_bound {
                free_var_bound = self.free_var_bounds[arg];
            }
            if self.has_quantifier_flags[arg] != 0 {
                has_quantifier = true;
            }
            if self.depths[arg] + 1 > depth {
                depth = self.depths[arg] + 1;
            }
        }
        self.free_var_bounds.push(free_var_bound);
        self.has_quantifier_flags.push(u8::from(has_quantifier));
        self.depths.push(depth);
        self.ids.push(0);
        self.ref_counts.push(0);
        id as Expr
    }

    /// The op of a builtin declaration doubles as its index in func_decls. The arguments may be a
    /// slice of the caller's stack, as a rewriter passes its result stack without copying it.
    pub fn mk_app(&mut self, decl: Decl, args: &[Expr], sort: Sort) -> Result<Expr, SmtError> {
        let func_decl = &self.func_decls[decl as usize];
        let (family, op) = (func_decl.family, func_decl.op);
        // Numerals and model values carry their value, so only mk_numeral and mk_model_value create
        // them.
        if decl == OP_NUM || family == FAMILY_MODEL_VALUE {
            return Err(SmtError::Invariant(format!(
                "{} needs a value",
                func_decl.name
            )));
        }
        let mut hash = decl;
        for arg in args {
            hash = hash.wrapping_mul(GOLDEN_MULTIPLIER).wrapping_add(*arg);
        }
        let mask = self.app_handles.len() - 1;
        let mut slot = hash as usize & mask;
        while self.app_handles[slot] != -1 {
            let candidate = self.app_handles[slot];
            if self.app_hashes[slot] == hash
                && self.decls[candidate as usize] == decl
                && self.get_arg_slice(candidate) == args
            {
                return Ok(self.revive(candidate));
            }
            slot = (slot + 1) & mask;
        }
        // The slot comes first, since finding it may replace builtin_hashes with one twice the
        // size.
        let builtin_slot = if family == FAMILY_USER || op == OP_PATTERN {
            None
        } else {
            Some(self.get_builtin_slot(op, args, sort)?)
        };
        let decl_hash = match builtin_slot {
            _ if family == FAMILY_USER => self.get_decl_hash(decl),
            None => self.get_pattern_hash(args, sort)?,
            Some(builtin_slot) => self.builtin_hashes[builtin_slot],
        };
        let id = self.create(
            KIND_APP,
            decl,
            args,
            sort,
            0,
            get_array_hash(args, &self.hashes, decl_hash),
        );
        // The lookup ended at a free slot, which the application takes unless the table doubles.
        if 2 * (self.num_apps + 1) > self.app_handles.len() {
            let handles = std::mem::take(&mut self.app_handles);
            let hashes = std::mem::take(&mut self.app_hashes);
            self.app_handles = vec![-1; 2 * handles.len()];
            self.app_hashes = vec![0; 2 * handles.len()];
            self.num_apps = 0;
            for index in 0..handles.len() {
                if handles[index] != -1 {
                    self.insert_app(hashes[index], handles[index]);
                }
            }
            self.insert_app(hash, id);
        } else {
            self.app_handles[slot] = id;
            self.app_hashes[slot] = hash;
            self.num_apps += 1;
        }
        self.register_node(id);
        Ok(id)
    }

    fn insert_app(&mut self, hash: i32, id: Expr) {
        let mask = self.app_handles.len() - 1;
        let mut slot = hash as usize & mask;
        while self.app_handles[slot] != -1 {
            slot = (slot + 1) & mask;
        }
        self.app_handles[slot] = id;
        self.app_hashes[slot] = hash;
        self.num_apps += 1;
    }

    // A numeral's declaration has the parameters (value, is_int), and a rational hashes as
    // hash(numerator) + 3 hash(denominator).
    fn intern_numeral(&mut self, key: TableKey, value: Rational, sort: Sort) -> Expr {
        if let Some(existing) = self.table.get(&key) {
            let existing = *existing;
            return self.revive(existing);
        }
        let value_hash = (u64::from(get_integer_hash(value.num()))
            + 3 * u64::from(get_integer_hash(value.den()))) as u32;
        self.numeral_values.push(value);
        let is_int = sort == SORT_INT;
        let index = (self.numeral_values.len() - 1) as i32;
        self.intern(key, KIND_APP, OP_NUM, &[], sort, index, |manager| {
            manager.get_func_decl_hash(
                &SmtSymbol::Name(if is_int { "Int" } else { "Real" }.into()),
                &[],
                sort,
                get_info_hash(Z3_ARITH_FAMILY, 0, &[value_hash, u32::from(is_int)]),
            )
        })
    }

    pub fn mk_real_numeral(&mut self, value: &Rational) -> Expr {
        let numeral = self.intern_numeral(TableKey::Real(value.clone()), value.clone(), SORT_REAL);
        if value.is_int() {
            self.hold_small_numeral(numeral, value.num(), true)
        } else {
            numeral
        }
    }

    pub fn mk_numeral(&mut self, value: &Int) -> Expr {
        if let Some(existing) = self.int_numerals.get(value) {
            let existing = *existing;
            let numeral = self.revive(existing);
            return self.hold_small_numeral(numeral, value, false);
        }
        let numeral = self.intern_numeral(
            TableKey::Int(value.clone()),
            Rational::from_int(value.clone()),
            SORT_INT,
        );
        self.int_numerals.insert(value.clone(), numeral);
        self.hold_small_numeral(numeral, value, false)
    }

    fn hold_small_numeral(&mut self, numeral: Expr, value: &Int, is_real: bool) -> Expr {
        let Some(index) = value
            .to_i64()
            .filter(|index| (0..MAX_SMALL_NUM_TO_CACHE as i64).contains(index))
        else {
            return numeral;
        };
        let cache = if is_real {
            &mut self.small_reals
        } else {
            &mut self.small_ints
        };
        if cache[index as usize].is_some() {
            return numeral;
        }
        cache[index as usize] = Some(numeral);
        self.inc_ref(numeral);
        numeral
    }

    /// mk_numeral(value, is_int).
    pub fn mk_numeral_of_sort(&mut self, value: &Rational, sort: Sort) -> Expr {
        if sort == SORT_INT {
            self.mk_numeral(value.num())
        } else {
            self.mk_real_numeral(value)
        }
    }

    /// mk_model_value: the element with this index in the universe of an uninterpreted sort.
    pub fn mk_model_value(&mut self, index: i32, sort: Sort) -> Expr {
        let key = TableKey::ModelValue(sort, index);
        if let Some(existing) = self.table.get(&key) {
            let existing = *existing;
            return self.revive(existing);
        }
        let name = SmtSymbol::Name(format!("{}!val!{index}", self.sort_names[sort as usize]));
        let hash = self.get_func_decl_hash(
            &name,
            &[],
            sort,
            get_info_hash(
                Z3_MODEL_VALUE_FAMILY,
                0,
                &[index as u32, self.sort_hashes[sort as usize]],
            ),
        );
        self.func_decls.push(FuncDecl {
            name,
            family: FAMILY_MODEL_VALUE,
            op: OP_MODEL_VALUE,
            domain: Vec::new(),
            range: sort,
            is_skolem: false,
            small_id: -1,
        });
        let decl = (self.func_decls.len() - 1) as Decl;
        self.set_decl_hash(decl, hash);
        self.intern(key, KIND_APP, decl, &[], sort, index, |_| hash)
    }

    pub fn mk_fresh_const(
        &mut self,
        prefix: Option<&SmtSymbol>,
        sort: Sort,
    ) -> Result<Expr, SmtError> {
        let decl = self.mk_fresh_func_decl(prefix, &[], sort, true);
        self.mk_app(decl, &[], sort)
    }

    pub fn mk_var(&mut self, index: i32, sort: Sort) -> Expr {
        self.intern(
            TableKey::Var(index, sort),
            KIND_VAR,
            -1,
            &[],
            sort,
            index,
            |manager| combine_hash(index as u32, manager.sort_hashes[sort as usize]),
        )
    }

    pub fn mk_quantifier(&mut self, data: QuantifierData) -> Result<Expr, SmtError> {
        if data.names.len() != data.sorts.len() {
            return Err(SmtError::Invariant(
                "a quantifier needs a name for each variable".into(),
            ));
        }
        let key = TableKey::Quantifier {
            is_forall: data.is_forall,
            sorts: data.sorts.clone(),
            names: data.names.clone(),
            body: data.body,
            patterns: data.patterns.clone(),
            weight: data.weight,
        };
        if let Some(existing) = self.table.get(&key) {
            let existing = *existing;
            return Ok(self.revive(existing));
        }
        let hash = mk_mix(
            get_array_hash(
                &data.sorts,
                &self.sort_hashes,
                if data.is_forall { 31 } else { 19 },
            ),
            data.patterns.len() as u32,
            self.hashes[data.body as usize],
        );
        let id = self.create(KIND_QUANTIFIER, -1, &[data.body], SORT_BOOL, 0, hash);
        self.table.insert(key, id);
        let body_bound = self.free_var_bounds[data.body as usize];
        self.free_var_bounds[id as usize] = (body_bound - data.sorts.len() as i32).max(0);
        self.quantifiers.insert(id, data);
        self.register_node(id);
        Ok(id)
    }

    /// mk_pattern: a multi-pattern of a quantifier.
    pub fn mk_pattern(&mut self, terms: &[Expr]) -> Result<Expr, SmtError> {
        self.mk_app(OP_PATTERN, terms, SORT_BOOL)
    }

    pub fn get_quantifier(&self, expr: Expr) -> Result<&QuantifierData, SmtError> {
        self.quantifiers
            .get(&expr)
            .ok_or_else(|| SmtError::Invariant("the expression is not a quantifier".into()))
    }

    // The data of an expression whose kind is a quantifier, which mk_quantifier sets before it
    // registers the expression.
    fn quantifier_of(&self, expr: Expr) -> &QuantifierData {
        match self.quantifiers.get(&expr) {
            Some(data) => data,
            None => unreachable!("a quantifier's data is set when it is created"),
        }
    }

    pub fn is_app(&self, expr: Expr) -> bool {
        self.kinds[expr as usize] == KIND_APP
    }

    pub fn is_var(&self, expr: Expr) -> bool {
        self.kinds[expr as usize] == KIND_VAR
    }

    pub fn is_ground(&self, expr: Expr) -> bool {
        self.free_var_bounds[expr as usize] == 0
    }

    /// Z3's is_ground: an application without variables or quantifiers.
    pub fn is_ground_app(&self, expr: Expr) -> bool {
        self.kinds[expr as usize] == KIND_APP
            && self.free_var_bounds[expr as usize] == 0
            && self.has_quantifier_flags[expr as usize] == 0
    }

    pub fn get_op(&self, expr: Expr) -> i32 {
        if self.kinds[expr as usize] == KIND_APP {
            self.func_decls[self.decls[expr as usize] as usize].op
        } else {
            -1
        }
    }

    pub fn get_family(&self, expr: Expr) -> i32 {
        if self.kinds[expr as usize] == KIND_APP {
            self.func_decls[self.decls[expr as usize] as usize].family
        } else {
            -1
        }
    }

    pub fn is_bool(&self, expr: Expr) -> bool {
        self.sorts[expr as usize] == SORT_BOOL
    }

    pub fn is_int(&self, expr: Expr) -> bool {
        self.sorts[expr as usize] == SORT_INT
    }

    pub fn is_real(&self, expr: Expr) -> bool {
        self.sorts[expr as usize] == SORT_REAL
    }

    pub fn is_true(&self, expr: Expr) -> bool {
        expr == self.true_expr
    }

    pub fn is_false(&self, expr: Expr) -> bool {
        expr == self.false_expr
    }

    pub fn is_not(&self, expr: Expr) -> bool {
        self.get_op(expr) == OP_NOT
    }

    pub fn is_complement(&self, first: Expr, second: Expr) -> bool {
        (self.is_not(first) && self.get_arg(first, 0) == second)
            || (self.is_not(second) && self.get_arg(second, 0) == first)
            || (first == self.true_expr && second == self.false_expr)
            || (first == self.false_expr && second == self.true_expr)
    }

    pub fn is_numeral(&self, expr: Expr) -> bool {
        self.get_op(expr) == OP_NUM
    }

    /// The value of an integer numeral.
    pub fn get_numeral(&self, expr: Expr) -> Option<&Int> {
        (self.is_numeral(expr) && self.sorts[expr as usize] == SORT_INT)
            .then(|| self.get_numeral_value(expr))
    }

    /// The value of an expression that is an integer numeral.
    pub fn get_numeral_value(&self, expr: Expr) -> &Int {
        self.numeral_values[self.values[expr as usize] as usize].num()
    }

    /// The value of an expression that is a numeral of either sort.
    pub fn get_rational_value(&self, expr: Expr) -> &Rational {
        &self.numeral_values[self.values[expr as usize] as usize]
    }

    /// Unique values are interpreted constants that are distinct from each other, as in Z3.
    pub fn is_unique_value(&self, expr: Expr) -> bool {
        let op = self.get_op(expr);
        op == OP_NUM || op == OP_TRUE || op == OP_FALSE || op == OP_MODEL_VALUE
    }

    /// are_distinct: the plugin of the first term's family, or of the second's for a user term,
    /// tells two terms apart. Every plugin separates distinct unique values, and arith also
    /// separates b from (+ b k) and (+ k b) for a nonzero numeral k.
    pub fn are_distinct(&self, first: Expr, second: Expr) -> bool {
        if self.kinds[first as usize] != KIND_APP || self.kinds[second as usize] != KIND_APP {
            return false;
        }
        if first != second && self.is_unique_value(first) && self.is_unique_value(second) {
            return true;
        }
        let family = self.func_decls[self.decls[first as usize] as usize].family;
        let family = if family == FAMILY_USER {
            self.func_decls[self.decls[second as usize] as usize].family
        } else {
            family
        };
        if family != FAMILY_ARITH {
            return false;
        }
        let is_offset_of = |sum: Expr, term: Expr| {
            if self.get_op(sum) != OP_ADD || self.get_num_args(sum) != 2 {
                return false;
            }
            let first = self.get_arg(sum, 0);
            let second = self.get_arg(sum, 1);
            let is_non_zero =
                |expr: Expr| self.is_numeral(expr) && !self.get_rational_value(expr).is_zero();
            (first == term && is_non_zero(second)) || (second == term && is_non_zero(first))
        };
        is_offset_of(first, second) || is_offset_of(second, first)
    }

    pub fn is_model_value(&self, expr: Expr) -> bool {
        self.get_op(expr) == OP_MODEL_VALUE
    }

    pub fn is_uninterpreted_sort(&self, sort: Sort) -> bool {
        sort > SORT_REAL
    }

    /// An uninterpreted constant, such as a declared constant or a Skolem constant.
    pub fn is_uninterpreted_const(&self, expr: Expr) -> bool {
        self.is_uninterpreted(expr) && self.get_num_args(expr) == 0
    }

    pub fn is_uninterpreted(&self, expr: Expr) -> bool {
        self.get_family(expr) == FAMILY_USER
    }

    /// arith_util::is_times_minus_one: the t of (* -1 t).
    pub fn get_times_minus_one_arg(&self, expr: Expr) -> Option<Expr> {
        if self.get_op(expr) != OP_MUL || self.get_num_args(expr) != 2 {
            return None;
        }
        let coefficient = self.get_arg(expr, 0);
        (self.is_numeral(coefficient)
            && *self.get_rational_value(coefficient) == Rational::minus_one())
        .then(|| self.get_arg(expr, 1))
    }

    /// occurs: decl is applied somewhere in expr.
    pub fn is_occurring(&self, decl: Decl, expr: Expr) -> bool {
        self.some_subterm(expr, |current| self.decls[current as usize] == decl)
    }

    pub fn contains_model_value(&self, expr: Expr) -> bool {
        self.some_subterm(expr, |current| self.is_model_value(current))
    }

    // for_each_expr: visits the subterms with a stack of its own, so deep terms do not exhaust the
    // call stack.
    fn some_subterm(&self, expr: Expr, predicate: impl Fn(Expr) -> bool) -> bool {
        // Only looked up, never iterated.
        let mut visited = HashSet::new();
        let mut todo = vec![expr];
        while let Some(current) = todo.pop() {
            if !visited.insert(current) {
                continue;
            }
            let kind = self.kinds[current as usize];
            if kind == KIND_QUANTIFIER {
                todo.push(self.quantifier_of(current).body);
            } else if kind != KIND_VAR {
                if predicate(current) {
                    return true;
                }
                self.push_args(current, &mut todo);
            }
        }
        false
    }

    pub fn mk_not(&mut self, expr: Expr) -> Result<Expr, SmtError> {
        if expr == self.true_expr {
            return Ok(self.false_expr);
        }
        if expr == self.false_expr {
            return Ok(self.true_expr);
        }
        self.mk_app(OP_NOT, &[expr], SORT_BOOL)
    }

    pub fn mk_eq(&mut self, left: Expr, right: Expr) -> Result<Expr, SmtError> {
        self.mk_app(OP_EQ, &[left, right], SORT_BOOL)
    }

    pub fn mk_or(&mut self, args: &[Expr]) -> Result<Expr, SmtError> {
        match args {
            [] => Ok(self.false_expr),
            [arg] => Ok(*arg),
            _ => self.mk_app(OP_OR, args, SORT_BOOL),
        }
    }

    pub fn mk_and(&mut self, args: &[Expr]) -> Result<Expr, SmtError> {
        match args {
            [] => Ok(self.true_expr),
            [arg] => Ok(*arg),
            _ => self.mk_app(OP_AND, args, SORT_BOOL),
        }
    }

    pub fn get_decl_name(&self, expr: Expr) -> String {
        get_symbol_name(&self.func_decls[self.decls[expr as usize] as usize].name)
    }

    pub fn to_string(&self, expr: Expr) -> String {
        let kind = self.kinds[expr as usize];
        if kind == KIND_VAR {
            return format!("(:var {})", self.values[expr as usize]);
        }
        if kind == KIND_QUANTIFIER {
            let data = self.quantifier_of(expr);
            return format!(
                "({} ({}) {})",
                if data.is_forall { "forall" } else { "exists" },
                data.sorts.len(),
                self.to_string(data.body)
            );
        }
        if self.get_op(expr) == OP_NUM {
            let value = self.get_rational_value(expr);
            if self.sorts[expr as usize] == SORT_INT {
                return value.num().to_string();
            }
            return if value.is_int() {
                format!("{}.0", value.num())
            } else {
                format!("(/ {}.0 {}.0)", value.num(), value.den())
            };
        }
        let name = self.get_decl_name(expr);
        if self.get_num_args(expr) == 0 {
            return name;
        }
        let args = self.map_args(expr, |inner_arg, _| self.to_string(inner_arg));
        format!("({name} {})", args.join(" "))
    }
}
