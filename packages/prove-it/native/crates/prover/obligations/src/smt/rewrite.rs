//! encode/n_rewrite.ml, type/t_synth.ml, and encode/n_standardize.ml: a TLA+ expression as an
//! SMT-LIB term over the sort Idv. Set extensionality is in extensionality.rs, and the axioms each
//! flattened symbol brings are in instances.rs. A port of `src/prover/smt/rewrite.ts`.
//!
//! The encoder's state is an explicit struct; the TypeScript closes over it in `createEncoder`.

use std::collections::HashMap;
use std::rc::Rc;

use crate::errors::{ObligationError, Result};
use crate::expression::is_js_space;
use crate::expression::{
    Bound, BoundDomain, Builtin, Bullet, CaseArm, ExceptPoint, ExceptSpec, Expr, ExprCore, HypCore,
    Level, Quantifier, Sequent, Visibility, expr,
};
use crate::ocaml::int_of_string;
use crate::smt::axioms::get_integers;
use crate::smt::context::{Context, Identifier, create_context};
use crate::smt::extensionality::{Polarity, get_equality, resolve_triggers};
use crate::smt::flatten::{
    Entry, FlattenedSymbols, Flattener, Site, UNPRIMABLE, create_flattener, get_depth,
    get_variable, remove_unprimable,
};
use crate::smt::format::{
    BOOL_SET, BUILTIN_SYMBOLS, CAST_BOOL, CAST_INT, FUN_APP, FUN_EXCEPT, FUN_SET, INT_LTEQ,
    INT_SET, MEM, NAT_SET, STR_SET, SUBSET_EQ, TT_IDV, call, conjoin, disjoin, get_binders, tla,
};
use crate::smt::instances::{
    get_choose_axioms, get_function_axioms, get_select_seq_axioms, get_set_of_axioms,
    get_set_st_axioms,
};
use crate::substitution::{normalize_apply, shift_expr};

#[derive(Clone, Debug, PartialEq, Eq)]
struct Term {
    is_bool: bool,
    text: String,
    // Type.Synthesize: the Int-sorted form of a term that is an integer before it's cast to Idv.
    integer: Option<String>,
}

// What tlapm keeps across the obligations of one run.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EncodingSession {
    pub case_errors: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mode {
    // Whether the text encodes a fact that tlapm leaves out, which may declare operators.
    pub is_omitted: bool,
    pub polarity: Polarity,
    pub at: Option<String>,
    pub depth: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Binding {
    Constant {
        symbol: String,
    },
    Variable {
        name: String,
        symbol: String,
        primed: String,
    },
    Operator {
        symbol: String,
        arity: usize,
    },
    SecondOrder {
        name: String,
        shapes: Vec<usize>,
    },
    Unsupported {
        reason: String,
    },
}

#[derive(Debug)]
pub struct Env {
    pub binding: Binding,
    pub rest: EnvRef,
}

/// `Env | undefined`.
pub type EnvRef = Option<Rc<Env>>;

// One of a nested ASSUME's wrappers around the goal: a quantifier, or an implication.
enum Wrapper {
    Forall {
        variable: String,
        guard: Option<String>,
    },
    Implies {
        fact: String,
    },
}

impl Wrapper {
    fn wrap(&self, body: String) -> String {
        match self {
            Self::Forall {
                variable,
                guard: None,
            } => format!("(forall (({variable} Idv)) {body})"),
            Self::Forall {
                variable,
                guard: Some(guard),
            } => format!("(forall (({variable} Idv)) (=> {guard} {body}))"),
            Self::Implies { fact } => format!("(=> {fact} {body})"),
        }
    }
}

// A nested ASSUME's declarations and facts so far: each wraps the goal in a quantifier or an
// implication.
struct NestedContext {
    env: EnvRef,
    mode: Mode,
    wrappers: Vec<Wrapper>,
}

struct BoundVariables {
    variables: Vec<String>,
    env: EnvRef,
    mode: Mode,
}

struct Operand {
    is_first_order: bool,
    text: String,
}

/// The encoder `createEncoder` returns.
pub struct Encoder<'session> {
    session: &'session mut EncodingSession,
    flattener: Flattener,
    // The arity of each anonymous operator Coalesce introduces.
    pub anonymous: HashMap<String, usize>,
    // The fields of each record symbol.
    pub record_fields: HashMap<String, Vec<String>>,
    context: Context,
    // The salted name of each declared user symbol, for the printer's context.
    pub declared: HashMap<String, Identifier>,
}

pub fn create_encoder(session: &mut EncodingSession) -> Encoder<'_> {
    Encoder {
        session,
        flattener: create_flattener(),
        anonymous: HashMap::new(),
        record_fields: HashMap::new(),
        context: create_context(),
        declared: HashMap::new(),
    }
}

// Standardize wraps a cast term in an application, and set_extensionality_visitor visits the
// arguments of an application with neither polarity, so a cast triggers every set equality in it.
fn to_bool(term: &Term) -> String {
    if term.is_bool {
        term.text.clone()
    } else {
        format!("(= {} {TT_IDV})", resolve_triggers(&term.text, true))
    }
}

fn to_idv(term: &Term) -> String {
    if term.is_bool {
        format!("({CAST_BOOL} {})", resolve_triggers(&term.text, true))
    } else {
        term.text.clone()
    }
}

fn bool_term(text: String) -> Term {
    Term {
        is_bool: true,
        text,
        integer: None,
    }
}

fn idv_term(text: String) -> Term {
    Term {
        is_bool: false,
        text,
        integer: None,
    }
}

fn get_binding(env: &EnvRef, index: isize) -> Result<Binding> {
    let mut found = env.clone();
    for _ in 1..index {
        found = found.and_then(|current| current.rest.clone());
    }
    found
        .map(|current| current.binding.clone())
        .ok_or_else(|| ObligationError::unsupported("a reference outside the obligation"))
}

fn push(env: &EnvRef, binding: Binding) -> EnvRef {
    Some(Rc::new(Env {
        binding,
        rest: env.clone(),
    }))
}

/// `/[^\s()]+#\d+/g`: in each run of other characters, the longest prefix that a `#` and digits
/// follow, through all the digits.
fn get_numbered_variables(text: &str) -> Vec<&str> {
    text.split(|character: char| is_js_space(character) || character == '(' || character == ')')
        .filter_map(|run| {
            let (hash, _) = run.char_indices().rev().find(|(position, character)| {
                *character == '#'
                    && *position > 0
                    && run[position + 1..].starts_with(|next: char| next.is_ascii_digit())
            })?;
            let end = run[hash + 1..]
                .find(|other: char| !other.is_ascii_digit())
                .map_or(run.len(), |offset| hash + 1 + offset);
            Some(&run[..end])
        })
        .collect()
}

// The variables bound outside depth that text uses, outermost first.
fn get_free(text: &str, depth: usize) -> Vec<String> {
    let mut free: Vec<String> = Vec::new();
    for variable in get_numbered_variables(text) {
        if !free.iter().any(|known| known == variable) {
            free.push(variable.to_string());
        }
    }
    free.retain(|variable| get_depth(variable) < depth);
    free.sort_by_key(|variable| get_depth(variable));
    free
}

fn neither(mode: &Mode) -> Mode {
    Mode {
        polarity: Polarity::Neither,
        ..mode.clone()
    }
}

fn invert(mode: &Mode) -> Mode {
    Mode {
        polarity: match mode.polarity {
            Polarity::Positive => Polarity::Negative,
            Polarity::Negative => Polarity::Positive,
            Polarity::Neither => Polarity::Neither,
        },
        ..mode.clone()
    }
}

fn get_site(mode: &Mode) -> Site {
    Site {
        depth: mode.depth,
        is_omitted: mode.is_omitted,
    }
}

/// The TypeScript reads an application's arguments by position whatever its arity, and throws a
/// `TypeError` on a missing one; an application of the wrong arity is a bug in tlapm's terms.
fn get_arg(args: &[Expr], index: usize) -> Result<&Expr> {
    args.get(index).ok_or_else(ObligationError::assert_failure)
}

fn bind_variables(names: &[String], env: &EnvRef, mode: &Mode) -> BoundVariables {
    let variables: Vec<String> = names
        .iter()
        .enumerate()
        .map(|(index, name)| get_variable(name, mode.depth + index))
        .collect();
    let inner = variables.iter().fold(env.clone(), |current, symbol| {
        push(
            &current,
            Binding::Constant {
                symbol: symbol.clone(),
            },
        )
    });
    BoundVariables {
        variables,
        env: inner,
        mode: Mode {
            depth: mode.depth + names.len(),
            ..mode.clone()
        },
    }
}

// Rewrite.elim_flex: the Action frontend's name#prime is the primed copy of the variable it
// names, which tlapm finds by name.
fn get_primed(env: &EnvRef, name: &str) -> Result<String> {
    let mut current = env.clone();
    while let Some(node) = current {
        if let Binding::Variable {
            name: variable,
            primed,
            ..
        } = &node.binding
            && variable == name
        {
            return Ok(primed.clone());
        }
        current = node.rest.clone();
    }
    Err(ObligationError::unsupported(
        "a primed declaration that isn't a variable",
    ))
}

/// An integer as tlapm's SMT encoding reads it: `int_of_string m` (encode/n_standardize.ml:246,
/// 251), which raises `Failure "int_of_string"` past OCaml's ints. The SMT backend reports that
/// failure as not tried (backend/prep.ml:485-489), which a `TlaProverError` stands for. The
/// literal prints as `pp_print_int` writes the int (backend/smtlib.ml:122-123).
fn get_smt_integer(text: &str) -> Result<String> {
    int_of_string(text)
        .map(|value| value.to_string())
        .ok_or_else(|| ObligationError::prover("int_of_string"))
}

/// An expression's `kind`, as the TypeScript names it.
fn get_kind(core: &ExprCore) -> &'static str {
    match core {
        ExprCore::Ix { .. } => "Ix",
        ExprCore::Opaque { .. } => "Opaque",
        ExprCore::Internal { .. } => "Internal",
        ExprCore::Lambda { .. } => "Lambda",
        ExprCore::Sequent { .. } => "Sequent",
        ExprCore::Bang { .. } => "Bang",
        ExprCore::Apply { .. } => "Apply",
        ExprCore::With { .. } => "With",
        ExprCore::If { .. } => "If",
        ExprCore::List { .. } => "List",
        ExprCore::Let { .. } => "Let",
        ExprCore::Quant { .. } => "Quant",
        ExprCore::Tquant { .. } => "Tquant",
        ExprCore::Choose { .. } => "Choose",
        ExprCore::SetSt { .. } => "SetSt",
        ExprCore::SetOf { .. } => "SetOf",
        ExprCore::SetEnum { .. } => "SetEnum",
        ExprCore::Product { .. } => "Product",
        ExprCore::Tuple { .. } => "Tuple",
        ExprCore::Fcn { .. } => "Fcn",
        ExprCore::FcnApp { .. } => "FcnApp",
        ExprCore::Arrow { .. } => "Arrow",
        ExprCore::Rect { .. } => "Rect",
        ExprCore::Record { .. } => "Record",
        ExprCore::Except { .. } => "Except",
        ExprCore::Dot { .. } => "Dot",
        ExprCore::Sub { .. } => "Sub",
        ExprCore::Tsub { .. } => "Tsub",
        ExprCore::Fair { .. } => "Fair",
        ExprCore::Case { .. } => "Case",
        ExprCore::String { .. } => "String",
        ExprCore::Num { .. } => "Num",
        ExprCore::At { .. } => "At",
        ExprCore::Parens { .. } => "Parens",
    }
}

impl Encoder<'_> {
    pub fn flattened(&self) -> &FlattenedSymbols {
        &self.flattener.flattened
    }

    // Smtlib.adj: the Action frontend's name, salted while it's taken.
    pub fn get_unique_name(&mut self, name: &str) -> String {
        let identifier = self.context.adjoin(name);
        self.context.enter(&identifier);
        let symbol = identifier.name.clone();
        self.declared.insert(symbol.clone(), identifier);
        symbol
    }

    pub fn push(&self, env: &EnvRef, binding: Binding) -> EnvRef {
        push(env, binding)
    }

    pub fn encode_idv(&mut self, expression: &Expr, env: &EnvRef, mode: &Mode) -> Result<String> {
        Ok(to_idv(&self.encode(expression, env, &neither(mode))?))
    }

    pub fn encode_bool(&mut self, expression: &Expr, env: &EnvRef, mode: &Mode) -> Result<String> {
        Ok(to_bool(&self.encode(expression, env, mode)?))
    }

    fn encode_idvs(
        &mut self,
        expressions: &[Expr],
        env: &EnvRef,
        mode: &Mode,
    ) -> Result<Vec<String>> {
        expressions
            .iter()
            .map(|expression| self.encode_idv(expression, env, mode))
            .collect()
    }

    fn encode_bools(
        &mut self,
        expressions: &[Expr],
        env: &EnvRef,
        mode: &Mode,
    ) -> Result<Vec<String>> {
        expressions
            .iter()
            .map(|expression| self.encode_bool(expression, env, mode))
            .collect()
    }

    // The domains of bounds, each in the scope outside them. A Ditto copies the last domain, and
    // tlapm's Rewrite encodes each copy, so each one flattens again.
    fn encode_domains(
        &mut self,
        bounds: &[Bound],
        env: &EnvRef,
        mode: &Mode,
    ) -> Result<Vec<Option<String>>> {
        let mut domains: Vec<Option<Expr>> = Vec::with_capacity(bounds.len());
        for bound in bounds {
            let domain = match &bound.domain {
                BoundDomain::Ditto => domains.last().cloned().flatten(),
                BoundDomain::NoDomain => None,
                BoundDomain::Domain(expression) => Some(expression.clone()),
            };
            domains.push(domain);
        }
        domains
            .iter()
            .map(|domain| match domain {
                None => Ok(None),
                Some(domain) => self.encode_idv(domain, env, mode).map(Some),
            })
            .collect()
    }

    fn get_domains(
        &mut self,
        bounds: &[Bound],
        env: &EnvRef,
        mode: &Mode,
        construct: &str,
    ) -> Result<Vec<String>> {
        self.encode_domains(bounds, env, mode)?
            .into_iter()
            .map(|domain| {
                domain.ok_or_else(|| {
                    ObligationError::unsupported(format!("{construct} without a domain"))
                })
            })
            .collect()
    }

    fn encode_quantifier(
        &mut self,
        quantifier: Quantifier,
        bounds: &[Bound],
        body: &Expr,
        env: &EnvRef,
        mode: &Mode,
    ) -> Result<String> {
        let domains = self.encode_domains(bounds, env, mode)?;
        let names: Vec<String> = bounds.iter().map(|bound| bound.name.clone()).collect();
        let bound = bind_variables(&names, env, mode);
        let body = self.encode_bool(body, &bound.env, &bound.mode)?;
        let guards: Vec<String> = bound
            .variables
            .iter()
            .enumerate()
            .filter_map(|(index, variable)| {
                domains
                    .get(index)
                    .cloned()
                    .flatten()
                    .map(|domain| format!("({MEM} {variable} {domain})"))
            })
            .collect();
        let binders = get_binders(&bound.variables, "Idv");
        Ok(match quantifier {
            Quantifier::Forall if guards.is_empty() => format!("(forall ({binders}) {body})"),
            Quantifier::Forall => format!("(forall ({binders}) (=> {} {body}))", conjoin(&guards)),
            Quantifier::Exists => {
                let mut items = guards;
                items.push(body);
                format!("(exists ({binders}) {})", conjoin(&items))
            }
        })
    }

    fn encode_set_st(
        &mut self,
        name: &str,
        domain: &Expr,
        body: &Expr,
        env: &EnvRef,
        mode: &Mode,
    ) -> Result<Term> {
        let domain = self.encode_idv(domain, env, mode)?;
        let bound = bind_variables(&[name.to_string()], env, &neither(mode));
        let body = self.encode_bool(body, &bound.env, &bound.mode)?;
        let free = get_free(&body, mode.depth);
        let variable = bound.variables[0].clone();
        let axioms_free = free.clone();
        let axioms_body = body.clone();
        let symbol = self.flattener.flatten(
            "SetSt",
            &body,
            get_site(mode),
            Rc::new(move |name, _| get_set_st_axioms(name, &axioms_free, &axioms_body, &variable)),
            free.len() + 1,
            None,
        );
        let mut args = vec![domain];
        args.extend(free);
        Ok(idv_term(call(&symbol, &args)))
    }

    fn encode_set_of(
        &mut self,
        element: &Expr,
        bounds: &[Bound],
        env: &EnvRef,
        mode: &Mode,
    ) -> Result<Term> {
        let domains = self.get_domains(bounds, env, mode, "a set of values")?;
        let names: Vec<String> = bounds.iter().map(|bound| bound.name.clone()).collect();
        let bound = bind_variables(&names, env, &neither(mode));
        let element = self.encode_idv(element, &bound.env, &bound.mode)?;
        let free = get_free(&element, mode.depth);
        let count = domains.len();
        let axioms_free = free.clone();
        let axioms_element = element.clone();
        let variables = bound.variables;
        let symbol = self.flattener.flatten(
            &format!("SetOf_{count}"),
            &element,
            get_site(mode),
            Rc::new(move |name, _| {
                get_set_of_axioms(name, &axioms_free, &axioms_element, &variables)
            }),
            count + free.len(),
            None,
        );
        let mut args = domains;
        args.extend(free);
        Ok(idv_term(call(&symbol, &args)))
    }

    // Rewrite.elim_multiarg: a function of several arguments is a function of a tuple.
    fn encode_function(
        &mut self,
        bounds: &[Bound],
        body: &Expr,
        env: &EnvRef,
        mode: &Mode,
    ) -> Result<Term> {
        let domains = self.get_domains(bounds, env, mode, "a function")?;
        let domain = if domains.len() == 1 {
            domains[0].clone()
        } else {
            call(&tla(&format!("Product_{}", domains.len())), &domains)
        };
        let variable = get_variable(
            if domains.len() == 1 {
                bounds.first().map_or("", |bound| bound.name.as_str())
            } else {
                "x"
            },
            mode.depth,
        );
        let inner = Mode {
            depth: mode.depth + 1,
            ..neither(mode)
        };
        let body_env = if domains.len() == 1 {
            push(
                env,
                Binding::Constant {
                    symbol: variable.clone(),
                },
            )
        } else {
            get_integers(domains.len())
                .iter()
                .fold(env.clone(), |current, key| {
                    push(
                        &current,
                        Binding::Constant {
                            symbol: format!("({FUN_APP} {variable} {key})"),
                        },
                    )
                })
        };
        let body = self.encode_idv(body, &body_env, &inner)?;
        let free = get_free(&body, mode.depth);
        let axioms_free = free.clone();
        let axioms_body = body.clone();
        let axioms_variable = variable.clone();
        let symbol = self.flattener.flatten(
            "FunFcn",
            &body,
            get_site(mode),
            Rc::new(move |name, axioms| {
                get_function_axioms(name, &axioms_free, &axioms_body, &axioms_variable, axioms)
            }),
            free.len() + 1,
            None,
        );
        let mut args = vec![domain];
        args.extend(free);
        Ok(idv_term(call(&symbol, &args)))
    }

    // Elab: CHOOSE x \in S : P is CHOOSE x : x \in S /\ P.
    fn encode_choose(
        &mut self,
        name: &str,
        domain: Option<&Expr>,
        body: &Expr,
        env: &EnvRef,
        mode: &Mode,
    ) -> Result<Term> {
        let bound = bind_variables(&[name.to_string()], env, &neither(mode));
        let variable = bound.variables[0].clone();
        let domain = match domain {
            Some(domain) => Some(format!(
                "({MEM} {variable} {})",
                self.encode_idv(domain, env, mode)?
            )),
            None => None,
        };
        let predicate = self.encode_bool(body, &bound.env, &bound.mode)?;
        let body = match domain {
            None => predicate,
            Some(domain) => conjoin(&[domain, predicate]),
        };
        let free = get_free(&body, mode.depth);
        let axioms_free = free.clone();
        let axioms_body = body.clone();
        let symbol = self.flattener.flatten(
            "Choose",
            &body,
            get_site(mode),
            Rc::new(move |name, _| get_choose_axioms(name, &axioms_free, &axioms_body, &variable)),
            free.len(),
            None,
        );
        Ok(idv_term(call(&symbol, &free)))
    }

    // Type.Synthesize compares values of the same sort only above type level 1, so two formulas are
    // compared as values.
    fn encode_equality(
        &mut self,
        args: &[Expr],
        env: &EnvRef,
        mode: &Mode,
        is_negated: bool,
    ) -> Result<String> {
        let left = self.encode_idv(get_arg(args, 0)?, env, mode)?;
        let right = self.encode_idv(get_arg(args, 1)?, env, mode)?;
        Ok(get_equality(&left, &right, mode.polarity, is_negated))
    }

    // Type.Synthesize: SelectSeq's test becomes the predicate LAMBDA x1 : Test(x1), its body the
    // text Flatten compares.
    fn get_selection_test(
        &mut self,
        test: &Expr,
        env: &EnvRef,
        mode: &Mode,
    ) -> Result<(String, String)> {
        let lambda = match &test.core {
            ExprCore::Lambda { params, body } if params.len() == 1 => Some((params, body)),
            _ => None,
        };
        let name = lambda.map_or_else(|| "x1".to_string(), |lambda| lambda.0[0].name.clone());
        let bound = bind_variables(&[name], env, &neither(mode));
        let predicate = match lambda {
            Some(lambda) => lambda.1.clone(),
            None => expr(ExprCore::Apply {
                operator: shift_expr(1, test)?,
                args: vec![expr(ExprCore::Ix { index: 1 })],
            }),
        };
        let body = self.encode_bool(&predicate, &bound.env, &bound.mode)?;
        Ok((body, bound.variables[0].clone()))
    }

    fn encode_builtin(
        &mut self,
        builtin: Builtin,
        args: &[Expr],
        env: &EnvRef,
        mode: &Mode,
    ) -> Result<Term> {
        Ok(match builtin {
            Builtin::Conj => bool_term(conjoin(&self.encode_bools(args, env, mode)?)),
            Builtin::Disj => bool_term(disjoin(&self.encode_bools(args, env, mode)?)),
            Builtin::Implies => {
                let premise = self.encode_bool(get_arg(args, 0)?, env, &invert(mode))?;
                let conclusion = self.encode_bool(get_arg(args, 1)?, env, mode)?;
                bool_term(format!("(=> {premise} {conclusion})"))
            }
            Builtin::Equiv => bool_term(format!(
                "(= {})",
                self.encode_bools(args, env, &neither(mode))?.join(" ")
            )),
            Builtin::Neg => bool_term(format!(
                "(not {})",
                self.encode_bool(get_arg(args, 0)?, env, &invert(mode))?
            )),
            Builtin::Eq => bool_term(self.encode_equality(args, env, mode, false)?),
            Builtin::Neq => bool_term(self.encode_equality(args, env, mode, true)?),
            Builtin::Mem => bool_term(call(MEM, &self.encode_idvs(args, env, mode)?)),
            // Rewrite.elim_notmem: a \notin S is ~(a \in S).
            Builtin::Notmem => bool_term(format!(
                "(not {})",
                call(MEM, &self.encode_idvs(args, env, mode)?)
            )),
            Builtin::Subseteq => bool_term(call(SUBSET_EQ, &self.encode_idvs(args, env, mode)?)),
            // Rewrite.elim_compare: a < b is a <= b /\ a # b, and a > b is b < a.
            Builtin::Lteq => bool_term(call(INT_LTEQ, &self.encode_idvs(args, env, mode)?)),
            Builtin::Gteq => {
                let mut operands = self.encode_idvs(args, env, mode)?;
                operands.reverse();
                bool_term(call(INT_LTEQ, &operands))
            }
            Builtin::Lt | Builtin::Gt => {
                // Rewrite copies the operands before Flatten, which flattens each copy again.
                let get_operands = |encoder: &mut Self| -> Result<Vec<String>> {
                    let mut operands = encoder.encode_idvs(args, env, mode)?;
                    if builtin == Builtin::Gt {
                        operands.reverse();
                    }
                    Ok(operands)
                };
                let first = get_operands(self)?;
                let second = get_operands(self)?;
                bool_term(format!(
                    "(and {} (distinct {}))",
                    call(INT_LTEQ, &first),
                    second.join(" ")
                ))
            }
            // Flatten: SelectSeq(s, Test) is a fresh operator of s and the bound variables Test uses.
            Builtin::SelectSeq => {
                let (body, variable) = self.get_selection_test(get_arg(args, 1)?, env, mode)?;
                let free = get_free(&body, mode.depth);
                let axioms_free = free.clone();
                let axioms_body = body.clone();
                let symbol = self.flattener.flatten(
                    "SelectSeq",
                    &body,
                    get_site(mode),
                    Rc::new(move |name, _| {
                        get_select_seq_axioms(name, &axioms_free, &axioms_body, &variable)
                    }),
                    free.len() + 1,
                    None,
                );
                let mut operands = vec![self.encode_idv(get_arg(args, 0)?, env, mode)?];
                operands.extend(free);
                idv_term(call(&symbol, &operands))
            }
            Builtin::Unprimable => {
                let term = self.encode(get_arg(args, 0)?, env, &neither(mode))?;
                Term {
                    text: format!("({UNPRIMABLE} {})", term.text),
                    ..term
                }
            }
            _ => {
                let symbol = BUILTIN_SYMBOLS
                    .iter()
                    .find(|entry| entry.0 == builtin)
                    .map(|entry| entry.1)
                    .ok_or_else(|| {
                        ObligationError::unsupported(format!("the operator {}", builtin.name()))
                    })?;
                idv_term(call(symbol, &self.encode_idvs(args, env, mode)?))
            }
        })
    }

    fn encode_reference(
        &mut self,
        binding: &Binding,
        args: &[Expr],
        env: &EnvRef,
        mode: &Mode,
    ) -> Result<Term> {
        match binding {
            Binding::Constant { symbol } | Binding::Variable { symbol, .. } => {
                if !args.is_empty() {
                    let kind = if matches!(binding, Binding::Constant { .. }) {
                        "constant"
                    } else {
                        "variable"
                    };
                    return Err(ObligationError::unsupported(format!("an applied {kind}")));
                }
                Ok(idv_term(symbol.clone()))
            }
            Binding::Operator { symbol, arity } => {
                if args.len() != *arity {
                    return Err(ObligationError::unsupported(
                        "an operator applied to the wrong number of arguments",
                    ));
                }
                Ok(idv_term(call(symbol, &self.encode_idvs(args, env, mode)?)))
            }
            // Flatten: an application of a second-order operator, which has no axioms, is a fresh
            // operator of its first-order arguments and the bound variables its others use.
            Binding::SecondOrder { name, shapes } => {
                if args.len() != shapes.len() {
                    return Err(ObligationError::unsupported(
                        "an operator applied to the wrong number of arguments",
                    ));
                }
                let mut operands = Vec::with_capacity(args.len());
                for (index, arg) in args.iter().enumerate() {
                    operands.push(self.encode_operand(arg, shapes[index], env, mode)?);
                }
                let first_order: Vec<String> = operands
                    .iter()
                    .filter(|operand| operand.is_first_order)
                    .map(|operand| operand.text.clone())
                    .collect();
                let higher_order = operands
                    .iter()
                    .filter(|operand| !operand.is_first_order)
                    .map(|operand| operand.text.as_str())
                    .collect::<Vec<_>>()
                    .join(" ");
                let free = get_free(&higher_order, mode.depth);
                let symbol = self.flattener.flatten(
                    "",
                    &higher_order,
                    get_site(mode),
                    Rc::new(|_, _| Vec::new()),
                    first_order.len() + free.len(),
                    Some(name),
                );
                let mut operands = first_order;
                operands.extend(free);
                Ok(idv_term(call(&symbol, &operands)))
            }
            Binding::Unsupported { reason } => Err(ObligationError::unsupported(reason.clone())),
        }
    }

    fn encode_operand(
        &mut self,
        arg: &Expr,
        shape: usize,
        env: &EnvRef,
        mode: &Mode,
    ) -> Result<Operand> {
        if shape == 0 {
            return Ok(Operand {
                is_first_order: true,
                text: self.encode_idv(arg, env, mode)?,
            });
        }
        let not_lambda =
            || ObligationError::unsupported("an operator argument that isn't a LAMBDA");
        match &arg.core {
            // An operator's name as the argument stands for the operator, which compare_expr
            // matches by name.
            ExprCore::Ix { index } => match get_binding(env, *index)? {
                Binding::Operator { symbol, .. } => Ok(Operand {
                    is_first_order: false,
                    text: symbol,
                }),
                _ => Err(not_lambda()),
            },
            ExprCore::Lambda { params, body } => {
                let names: Vec<String> = params.iter().map(|param| param.name.clone()).collect();
                let bound = bind_variables(&names, env, &neither(mode));
                Ok(Operand {
                    is_first_order: false,
                    text: self.encode_idv(body, &bound.env, &bound.mode)?,
                })
            }
            _ => Err(not_lambda()),
        }
    }

    // Standardize: an opaque name the Action frontend introduces is an anonymous operator, named
    // OPAQUE_ when it has no arguments.
    fn encode_opaque(
        &mut self,
        name: &str,
        args: &[Expr],
        env: &EnvRef,
        mode: &Mode,
    ) -> Result<Term> {
        if args.is_empty()
            && let Some(variable) = name.strip_suffix("#prime")
        {
            return Ok(idv_term(get_primed(env, variable)?));
        }
        let anonymous_name = if args.is_empty() {
            format!("Anon_OPAQUE_{name}")
        } else {
            format!("Anon_{name}")
        };
        self.anonymous.insert(anonymous_name.clone(), args.len());
        Ok(idv_term(call(
            &tla(&anonymous_name),
            &self.encode_idvs(args, env, mode)?,
        )))
    }

    // Elab.desugar: @ is the value at the whole trail.
    fn update(
        &mut self,
        spec: &ExceptSpec,
        value: String,
        trail: &[ExceptPoint],
        env: &EnvRef,
        mode: &Mode,
    ) -> Result<String> {
        let Some(point) = trail.first() else {
            return self.encode_idv(
                &spec.value,
                env,
                &Mode {
                    at: Some(value),
                    ..mode.clone()
                },
            );
        };
        let encode_key = |encoder: &mut Self| match point {
            ExceptPoint::Dot(field) => Ok(tla(&format!("StrLit_{field}"))),
            ExceptPoint::Apply(expression) => encoder.encode_idv(expression, env, mode),
        };
        let key = encode_key(self)?;
        // Elab.desugar repeats the key in the value it updates, and Flatten counts both.
        let repeated = if trail.len() > 1 {
            encode_key(self)?
        } else {
            key.clone()
        };
        let inner = self.update(
            spec,
            format!("({FUN_APP} {value} {repeated})"),
            &trail[1..],
            env,
            mode,
        )?;
        Ok(format!("({FUN_EXCEPT} {value} {key} {inner})"))
    }

    fn encode_except(
        &mut self,
        function: &Expr,
        specs: &[ExceptSpec],
        env: &EnvRef,
        mode: &Mode,
    ) -> Result<String> {
        let mut base = self.encode_idv(function, env, mode)?;
        for spec in specs {
            base = self.update(spec, base, &spec.trail, env, mode)?;
        }
        Ok(base)
    }

    // Standardize names each CASE with no OTHER by a count that tlapm never resets.
    fn get_case_error(&mut self) -> String {
        self.session.case_errors += 1;
        let name = format!("Anon_incomplete_case_error_{}", self.session.case_errors);
        let symbol = tla(&name);
        self.anonymous.insert(name, 0);
        symbol
    }

    fn encode_case(
        &mut self,
        arms: &[CaseArm],
        other: Option<&Expr>,
        env: &EnvRef,
        mode: &Mode,
    ) -> Result<Term> {
        let bodies = arms
            .iter()
            .map(|arm| self.encode(&arm.body, env, mode))
            .collect::<Result<Vec<_>>>()?;
        // Standardize: a CASE with no OTHER ends in an unknown value.
        let other = match other {
            Some(other) => self.encode(other, env, mode)?,
            None => idv_term(self.get_case_error()),
        };
        let is_bool = other.is_bool && bodies.iter().all(|body| body.is_bool);
        let is_integer =
            other.integer.is_some() && bodies.iter().all(|body| body.integer.is_some());
        if is_integer {
            let mut integer = other.integer.clone().unwrap_or_default();
            for (index, arm) in arms.iter().enumerate().rev() {
                let condition = self.encode_bool(&arm.condition, env, &neither(mode))?;
                integer = format!(
                    "(ite {condition} {} {integer})",
                    bodies[index].integer.as_deref().unwrap_or("")
                );
            }
            return Ok(Term {
                is_bool: false,
                text: format!("({CAST_INT} {integer})"),
                integer: Some(integer),
            });
        }
        let convert = |term: &Term| {
            if is_bool {
                term.text.clone()
            } else {
                to_idv(term)
            }
        };
        let mut text = convert(&other);
        for (index, arm) in arms.iter().enumerate().rev() {
            let condition = self.encode_bool(&arm.condition, env, mode)?;
            text = format!("(ite {condition} {} {text})", convert(&bodies[index]));
        }
        Ok(Term {
            is_bool,
            text,
            integer: None,
        })
    }

    fn encode_sequent(&mut self, sequent: &Sequent, env: &EnvRef, mode: &Mode) -> Result<String> {
        let mut state = NestedContext {
            env: env.clone(),
            mode: mode.clone(),
            wrappers: Vec::new(),
        };
        for hyp in &sequent.context {
            state = match &hyp.core {
                HypCore::Fresh {
                    name,
                    shape,
                    level,
                    domain,
                    ..
                } => {
                    if *shape > 0 {
                        if !state.mode.is_omitted {
                            return Err(ObligationError::unsupported("a second-order ASSUME"));
                        }
                        let variable = get_variable(name, state.mode.depth);
                        let mut wrappers = state.wrappers;
                        wrappers.push(Wrapper::Forall {
                            variable: variable.clone(),
                            guard: None,
                        });
                        NestedContext {
                            env: push(
                                &state.env,
                                Binding::Operator {
                                    symbol: variable,
                                    arity: *shape,
                                },
                            ),
                            mode: Mode {
                                depth: state.mode.depth + 1,
                                ..state.mode
                            },
                            wrappers,
                        }
                    } else {
                        if *level != Level::Constant {
                            return Err(ObligationError::unsupported(
                                "a NEW declaration that isn't constant",
                            ));
                        }
                        let domain = match domain {
                            Some(domain) => {
                                Some(self.encode_idv(domain, &state.env, &state.mode)?)
                            }
                            None => None,
                        };
                        let bound =
                            bind_variables(std::slice::from_ref(name), &state.env, &state.mode);
                        let variable = bound.variables[0].clone();
                        let guard = domain.map(|domain| format!("({MEM} {variable} {domain})"));
                        let mut wrappers = state.wrappers;
                        wrappers.push(Wrapper::Forall { variable, guard });
                        NestedContext {
                            env: bound.env,
                            mode: bound.mode,
                            wrappers,
                        }
                    }
                }
                HypCore::Fact {
                    expression,
                    visibility,
                    ..
                } => {
                    let fact = if *visibility == Visibility::Visible {
                        Some(self.encode_bool(expression, &state.env, &invert(&state.mode))?)
                    } else {
                        None
                    };
                    let mut wrappers = state.wrappers;
                    if let Some(fact) = fact {
                        wrappers.push(Wrapper::Implies { fact });
                    }
                    NestedContext {
                        env: push(
                            &state.env,
                            Binding::Unsupported {
                                reason: "a reference to a fact".to_string(),
                            },
                        ),
                        mode: state.mode,
                        wrappers,
                    }
                }
                HypCore::Flex { .. } => {
                    return Err(ObligationError::unsupported("a Flex in a nested ASSUME"));
                }
                HypCore::Defn { .. } => {
                    return Err(ObligationError::unsupported("a Defn in a nested ASSUME"));
                }
            };
        }
        let body = self.encode_bool(&sequent.active, &state.env, &state.mode)?;
        Ok(state
            .wrappers
            .iter()
            .rev()
            .fold(body, |body, wrapper| wrapper.wrap(body)))
    }

    fn encode(&mut self, expression: &Expr, env: &EnvRef, mode: &Mode) -> Result<Term> {
        match &expression.core {
            ExprCore::Ix { index } => {
                let binding = get_binding(env, *index)?;
                self.encode_reference(&binding, &[], env, mode)
            }
            ExprCore::Internal { builtin } => match builtin {
                Builtin::TRUE => Ok(bool_term("true".to_string())),
                Builtin::FALSE => Ok(bool_term("false".to_string())),
                Builtin::BOOLEAN => Ok(idv_term(BOOL_SET.to_string())),
                Builtin::STRING => Ok(idv_term(STR_SET.to_string())),
                Builtin::Nat => Ok(idv_term(NAT_SET.to_string())),
                Builtin::Int => Ok(idv_term(INT_SET.to_string())),
                _ => Err(ObligationError::unsupported(format!(
                    "the operator {}",
                    builtin.name()
                ))),
            },
            ExprCore::Apply { operator, args } => match &operator.core {
                ExprCore::Internal { builtin } => self.encode_builtin(*builtin, args, env, mode),
                ExprCore::Ix { index } => {
                    let binding = get_binding(env, *index)?;
                    self.encode_reference(&binding, args, env, mode)
                }
                ExprCore::Opaque { name } => self.encode_opaque(name, args, env, mode),
                ExprCore::Lambda { .. } => {
                    let normalized = expr(normalize_apply(operator, args.clone())?);
                    self.encode(&normalized, env, mode)
                }
                other => Err(ObligationError::unsupported(format!(
                    "an application of {}",
                    get_kind(other)
                ))),
            },
            ExprCore::Sequent { sequent } => {
                Ok(bool_term(self.encode_sequent(sequent, env, mode)?))
            }
            ExprCore::With { expression, .. } | ExprCore::Parens { expression, .. } => {
                self.encode(expression, env, mode)
            }
            ExprCore::If {
                condition,
                consequent,
                alternative,
            } => {
                let condition = self.encode_bool(condition, env, mode)?;
                let consequent = self.encode(consequent, env, mode)?;
                let alternative = self.encode(alternative, env, mode)?;
                if let (Some(then_integer), Some(else_integer)) =
                    (&consequent.integer, &alternative.integer)
                {
                    let integer = format!(
                        "(ite {} {then_integer} {else_integer})",
                        resolve_triggers(&condition, true)
                    );
                    return Ok(Term {
                        is_bool: false,
                        text: format!("({CAST_INT} {integer})"),
                        integer: Some(integer),
                    });
                }
                Ok(if consequent.is_bool && alternative.is_bool {
                    bool_term(format!(
                        "(ite {condition} {} {})",
                        consequent.text, alternative.text
                    ))
                } else {
                    idv_term(format!(
                        "(ite {condition} {} {})",
                        to_idv(&consequent),
                        to_idv(&alternative)
                    ))
                })
            }
            ExprCore::List { bullet, items } => {
                let items = self.encode_bools(items, env, mode)?;
                Ok(bool_term(if *bullet == Bullet::Or {
                    disjoin(&items)
                } else {
                    conjoin(&items)
                }))
            }
            ExprCore::Opaque { name } => self.encode_opaque(name, &[], env, mode),
            ExprCore::Quant {
                quantifier,
                bounds,
                body,
            } => Ok(bool_term(self.encode_quantifier(
                *quantifier,
                bounds,
                body,
                env,
                mode,
            )?)),
            ExprCore::Choose { name, domain, body } => {
                self.encode_choose(name, domain.as_ref(), body, env, mode)
            }
            ExprCore::SetSt { name, domain, body } => {
                self.encode_set_st(name, domain, body, env, mode)
            }
            ExprCore::SetOf { element, bounds } => self.encode_set_of(element, bounds, env, mode),
            ExprCore::SetEnum { elements } => Ok(idv_term(call(
                &tla(&format!("SetEnum_{}", elements.len())),
                &self.encode_idvs(elements, env, mode)?,
            ))),
            ExprCore::Product { factors } => Ok(idv_term(call(
                &tla(&format!("Product_{}", factors.len())),
                &self.encode_idvs(factors, env, mode)?,
            ))),
            ExprCore::Tuple { elements } => Ok(idv_term(call(
                &tla(&format!("Tuple_{}", elements.len())),
                &self.encode_idvs(elements, env, mode)?,
            ))),
            ExprCore::Fcn { bounds, body } => self.encode_function(bounds, body, env, mode),
            // Rewrite.elim_multiarg: f[a, b] applies f to the tuple <<a, b>>.
            ExprCore::FcnApp { function, args } => {
                let encoded_function = self.encode_idv(function, env, mode)?;
                let args = self.encode_idvs(args, env, mode)?;
                let argument = if args.len() == 1 {
                    args[0].clone()
                } else {
                    call(&tla(&format!("Tuple_{}", args.len())), &args)
                };
                Ok(idv_term(format!(
                    "({FUN_APP} {encoded_function} {argument})"
                )))
            }
            ExprCore::Arrow { domain, range } => {
                let domain = self.encode_idv(domain, env, mode)?;
                let range = self.encode_idv(range, env, mode)?;
                Ok(idv_term(call(FUN_SET, &[domain, range])))
            }
            ExprCore::Record { fields } | ExprCore::Rect { fields } => {
                let names: Vec<String> = fields.iter().map(|field| field.name.clone()).collect();
                let suffix = names.join("_");
                self.record_fields
                    .insert(format!("Record_{suffix}"), names.clone());
                self.record_fields
                    .insert(format!("RecordSet_{suffix}"), names);
                let head = if matches!(expression.core, ExprCore::Record { .. }) {
                    "Record"
                } else {
                    "RecordSet"
                };
                let values = fields
                    .iter()
                    .map(|field| self.encode_idv(&field.value, env, mode))
                    .collect::<Result<Vec<_>>>()?;
                Ok(idv_term(call(&tla(&format!("{head}_{suffix}")), &values)))
            }
            ExprCore::Except { function, specs } => {
                Ok(idv_term(self.encode_except(function, specs, env, mode)?))
            }
            ExprCore::Dot { expression, field } => Ok(idv_term(format!(
                "({FUN_APP} {} {})",
                self.encode_idv(expression, env, mode)?,
                tla(&format!("StrLit_{field}"))
            ))),
            ExprCore::Case { arms, other } => self.encode_case(arms, other.as_ref(), env, mode),
            ExprCore::String { value } => Ok(idv_term(tla(&format!("StrLit_{value}")))),
            ExprCore::Num { integer, fraction } => {
                if !fraction.is_empty() {
                    return Err(ObligationError::unsupported("a real number"));
                }
                Ok(Term {
                    is_bool: false,
                    text: format!("({CAST_INT} {})", get_smt_integer(integer)?),
                    integer: Some(get_smt_integer(integer)?),
                })
            }
            ExprCore::At { .. } => match &mode.at {
                None => Err(ObligationError::unsupported("@ outside EXCEPT")),
                Some(at) => Ok(idv_term(at.clone())),
            },
            ExprCore::Tquant { .. } | ExprCore::Tsub { .. } | ExprCore::Fair { .. } => {
                Err(ObligationError::unsupported("a temporal formula"))
            }
            other => Err(ObligationError::unsupported(format!(
                "the expression {}",
                get_kind(other)
            ))),
        }
    }

    // One fact or the goal, after the declarations of the symbols it flattens.
    pub fn get_entries(&mut self, line: &str) -> Vec<Entry> {
        let mut entries: Vec<Entry> = self
            .flattener
            .take_introduced()
            .into_iter()
            .map(Entry::Flattened)
            .collect();
        entries.push(Entry::Text(remove_unprimable(&resolve_triggers(
            line, false,
        ))));
        entries
    }
}

// Expected values from running the TypeScript.
#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;
    use crate::expression::Field;

    fn ix(index: isize) -> Expr {
        expr(ExprCore::Ix { index })
    }

    fn apply(builtin: Builtin, args: Vec<Expr>) -> Expr {
        expr(ExprCore::Apply {
            operator: expr(ExprCore::Internal { builtin }),
            args,
        })
    }

    fn num(integer: &str) -> Expr {
        expr(ExprCore::Num {
            integer: integer.to_string(),
            fraction: String::new(),
        })
    }

    fn mode(polarity: Polarity, at: Option<&str>, depth: usize) -> Mode {
        Mode {
            is_omitted: false,
            polarity,
            at: at.map(str::to_string),
            depth,
        }
    }

    fn neither_mode() -> Mode {
        mode(Polarity::Neither, None, 0)
    }

    fn get_env(encoder: &Encoder) -> EnvRef {
        let constant = encoder.push(
            &None,
            Binding::Constant {
                symbol: "smt__S".to_string(),
            },
        );
        encoder.push(
            &constant,
            Binding::Variable {
                name: "v".to_string(),
                symbol: "smt__v".to_string(),
                primed: "smt__v__prime".to_string(),
            },
        )
    }

    fn get_set_equality(builtin: Builtin) -> Expr {
        apply(
            builtin,
            vec![apply(Builtin::Cup, vec![ix(2), ix(2)]), ix(2)],
        )
    }

    fn get_texts(entries: &[Entry]) -> Vec<String> {
        entries
            .iter()
            .map(|entry| match entry {
                Entry::Text(text) => text.clone(),
                Entry::Flattened(flat) => format!("{} {} {}", flat.symbol, flat.kind, flat.visit),
                Entry::Omitted(fact) => fact.omitted.clone(),
            })
            .collect()
    }

    #[test]
    fn salts_unique_names() {
        let mut session = EncodingSession::default();
        let mut encoder = create_encoder(&mut session);
        let names: Vec<String> = ["x", "x", "x_1", "a b"]
            .iter()
            .map(|name| encoder.get_unique_name(name))
            .collect();
        assert_eq!(names, ["smt__x", "smt__x_1", "smt__x__1", "smt__aspace__b"]);
        assert_eq!(
            encoder.declared.get("smt__x_1"),
            Some(&Identifier {
                base: "smt__x".to_string(),
                salt: 1,
                name: "smt__x_1".to_string(),
            })
        );
    }

    #[test]
    fn encodes_set_equalities_by_polarity() -> Result<()> {
        let mut session = EncodingSession::default();
        let mut encoder = create_encoder(&mut session);
        let env = get_env(&encoder);
        let equality = get_set_equality(Builtin::Eq);
        let disequality = get_set_equality(Builtin::Neq);
        let negative = mode(Polarity::Negative, None, 0);
        let positive = mode(Polarity::Positive, None, 0);
        assert_eq!(
            encoder.encode_bool(&equality, &env, &negative)?,
            "(?trigger (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____Cup smt__S smt__S) smt__S) (= (smt__TLA____Cup smt__S smt__S) smt__S))"
        );
        assert_eq!(
            encoder.encode_bool(&equality, &env, &positive)?,
            "(smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____Cup smt__S smt__S) smt__S)"
        );
        assert_eq!(
            encoder.encode_idv(&equality, &env, &negative)?,
            "(smt__TLA____Cast__Bool (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____Cup smt__S smt__S) smt__S))"
        );
        assert_eq!(
            encoder.encode_bool(&disequality, &env, &negative)?,
            "(not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____Cup smt__S smt__S) smt__S))"
        );
        assert_eq!(
            encoder.encode_bool(&disequality, &env, &positive)?,
            "(?trigger (not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____Cup smt__S smt__S) smt__S)) (distinct (smt__TLA____Cup smt__S smt__S) smt__S))"
        );
        let fact = format!(
            "(assert {})",
            encoder.encode_bool(&equality, &env, &negative)?
        );
        assert_eq!(
            get_texts(&encoder.get_entries(&fact)),
            ["(assert (= (smt__TLA____Cup smt__S smt__S) smt__S))"]
        );
        Ok(())
    }

    #[test]
    fn counts_case_errors_in_the_session() -> Result<()> {
        let mut session = EncodingSession { case_errors: 4 };
        let mut encoder = create_encoder(&mut session);
        let env = get_env(&encoder);
        let case = expr(ExprCore::Case {
            arms: vec![CaseArm {
                condition: apply(Builtin::Eq, vec![ix(1), num("1")]),
                body: num("2"),
            }],
            other: None,
        });
        assert_eq!(
            encoder.encode_idv(&case, &env, &neither_mode())?,
            "(ite (= smt__v (smt__TLA____Cast__Int 1)) (smt__TLA____Cast__Int 2) smt__TLA____Anon__incomplete__case__error__5)"
        );
        assert_eq!(
            encoder.anonymous.get("Anon_incomplete_case_error_5"),
            Some(&0)
        );
        assert_eq!(session.case_errors, 5);
        Ok(())
    }

    #[test]
    fn encodes_primes_at_and_records() -> Result<()> {
        let mut session = EncodingSession::default();
        let mut encoder = create_encoder(&mut session);
        let env = get_env(&encoder);
        let primed = expr(ExprCore::Opaque {
            name: "v#prime".to_string(),
        });
        assert_eq!(
            encoder.encode_idv(&primed, &env, &neither_mode())?,
            "smt__v__prime"
        );
        let at = expr(ExprCore::At { is_except: true });
        assert_eq!(
            encoder.encode_idv(&at, &env, &mode(Polarity::Neither, Some("smt__f"), 0))?,
            "smt__f"
        );
        let record = expr(ExprCore::Record {
            fields: vec![
                Field {
                    name: "b".to_string(),
                    value: ix(1),
                },
                Field {
                    name: "a".to_string(),
                    value: ix(1),
                },
            ],
        });
        encoder.encode_idv(&record, &env, &neither_mode())?;
        let fields = Some(vec!["b".to_string(), "a".to_string()]);
        assert_eq!(encoder.record_fields.get("Record_b_a").cloned(), fields);
        assert_eq!(encoder.record_fields.get("RecordSet_b_a").cloned(), fields);
        Ok(())
    }

    #[test]
    fn flattens_before_the_fact() -> Result<()> {
        let mut session = EncodingSession::default();
        let mut encoder = create_encoder(&mut session);
        let env = get_env(&encoder);
        let set = expr(ExprCore::SetSt {
            name: "e".to_string(),
            domain: ix(2),
            body: apply(Builtin::Mem, vec![ix(1), ix(3)]),
        });
        assert_eq!(
            encoder.encode_idv(&set, &env, &mode(Polarity::Neither, None, 2))?,
            "(smt__TLA____SetSt__flatnd__1 smt__S)"
        );
        let entries = encoder.get_entries("(assert (?unprimable true))");
        assert_eq!(
            get_texts(&entries),
            [
                "smt__TLA____SetSt__flatnd__1 SetSt (smt__TLA____Mem e#2 smt__S)",
                "(assert true)"
            ]
        );
        let lines = encoder
            .flattened()
            .get("smt__TLA____SetSt__flatnd__1")
            .map(|flat| flat.get_lines(&HashSet::new()));
        assert_eq!(
            lines,
            Some(vec![
                "(declare-fun smt__TLA____SetSt__flatnd__1 (Idv) Idv)".to_string(),
                "(assert (! (forall ((a Idv) (x Idv)) (! (= (smt__TLA____Mem x (smt__TLA____SetSt__flatnd__1 a)) (and (smt__TLA____Mem x a) (smt__TLA____Mem x smt__S))) :pattern ((smt__TLA____Mem x (smt__TLA____SetSt__flatnd__1 a))) :pattern ((smt__TLA____Mem x a) (smt__TLA____SetSt__flatnd__1 a)))) :named |SetStDef TLA__SetSt_flatnd_1|))".to_string(),
            ])
        );
        Ok(())
    }

    #[test]
    fn reports_what_it_cannot_encode() {
        let mut session = EncodingSession::default();
        let mut encoder = create_encoder(&mut session);
        let env = get_env(&encoder);
        let applied = apply(
            Builtin::Mem,
            vec![
                expr(ExprCore::Apply {
                    operator: ix(2),
                    args: vec![num("1")],
                }),
                ix(1),
            ],
        );
        assert_eq!(
            encoder.encode_idv(&applied, &env, &neither_mode()),
            Err(ObligationError::unsupported("an applied constant"))
        );
        assert_eq!(
            encoder.encode_idv(&ix(3), &env, &neither_mode()),
            Err(ObligationError::unsupported(
                "a reference outside the obligation"
            ))
        );
        // The TypeScript throws a TypeError reading the missing argument.
        assert_eq!(
            encoder.encode_bool(&apply(Builtin::Neg, Vec::new()), &env, &neither_mode()),
            Err(ObligationError::assert_failure())
        );
    }

    // encode/n_standardize.ml:246, 251: the digits as an OCaml int, written back in decimal.
    #[test]
    fn reads_integers_as_int_of_string_does() {
        let cases = [
            ("007", Ok("7".to_owned())),
            ("4611686018427387903", Ok("4611686018427387903".to_owned())),
            // A \h numeral past max_int, as the lexer wraps it.
            (
                "-4611686018427387904",
                Ok("-4611686018427387904".to_owned()),
            ),
            (
                "4611686018427387904",
                Err(ObligationError::prover("int_of_string")),
            ),
            (
                "123456789012345678901234567890",
                Err(ObligationError::prover("int_of_string")),
            ),
        ];
        for (text, expected) in cases {
            assert_eq!(get_smt_integer(text), expected, "{text}");
        }
    }
}
