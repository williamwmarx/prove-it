//! Encodes a prepared proof obligation in SMT-LIB as tlapm's SMT backend does (encode/ and
//! backend/smtlib.ml): TLA+ values share one sort Idv, set membership is the predicate TLA__Mem,
//! and each symbol the obligation uses brings the symbols and axioms encode/n_data.ml lists for it.
//! A port of `src/prover/smt/encode.ts`.

use std::collections::{HashMap, HashSet};

use crate::errors::Result;
use crate::expression::is_js_space;
use crate::expression::{
    Builtin, DefnCore, Expr, ExprCore, Field, Hyp, HypCore, Sequent, Visibility, apply_builtin,
    at_expr, expr, map_children,
};
use crate::ocaml::compare_strings;
use crate::smt::context::create_printer;
use crate::smt::data::{CollectState, SymbolSpec, get_symbol_spec};
use crate::smt::extensionality::Polarity;
use crate::smt::flatten::{Entry, OmittedFact};
use crate::smt::format::{MEM, declare, get_tla_name};
use crate::smt::rewrite::{Binding, Encoder, EncodingSession, EnvRef, Mode, create_encoder};
use crate::smt::table::{Axiom, compare_axioms, get_axiom_key};

fn is_same_field_set(left: &[Field], right: &[Field]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .all(|field| right.iter().any(|other| other.name == field.name))
        && right
            .iter()
            .all(|field| left.iter().any(|other| other.name == field.name))
}

// mk_conj: e1 /\ (e2 /\ ...).
fn conjoin_right(items: &[Expr]) -> Expr {
    match items {
        [item] => item.clone(),
        [first, rest @ ..] => apply_builtin(
            Builtin::Conj,
            vec![first.clone(), conjoin_right(rest)],
            &first.props(),
        ),
        // The TypeScript never conjoins no items: a record has a field.
        [] => expr(ExprCore::Internal {
            builtin: Builtin::TRUE,
        }),
    }
}

fn decompose(left: &Expr, right: &Expr, from: &Expr) -> Expr {
    let (
        ExprCore::Record {
            fields: left_fields,
        },
        ExprCore::Record {
            fields: right_fields,
        },
    ) = (&left.core, &right.core)
    else {
        return apply_builtin(
            Builtin::Eq,
            vec![left.clone(), right.clone()],
            &from.props(),
        );
    };
    if !is_same_field_set(left_fields, right_fields) {
        return apply_builtin(
            Builtin::Eq,
            vec![left.clone(), right.clone()],
            &from.props(),
        );
    }
    conjoin_right(
        &left_fields
            .iter()
            .map(|field| {
                let other = right_fields
                    .iter()
                    .find(|other| other.name == field.name)
                    .map_or(&field.value, |other| &other.value);
                decompose(&field.value, other, from)
            })
            .collect::<Vec<_>>(),
    )
}

// N_rewrite.simpl_receq, before Type.Synthesize: an equality of two record constructors with the
// same fields is the conjunction of the equalities of their fields, paired by name.
fn simplify_record_equalities(expression: &Expr) -> Result<Expr> {
    let inner = map_children(expression, &mut simplify_record_equalities)?;
    let ExprCore::Apply { operator, args } = &inner.core else {
        return Ok(inner);
    };
    let is_record_equality = matches!(
        operator.core,
        ExprCore::Internal {
            builtin: Builtin::Eq
        }
    ) && args.len() == 2
        && matches!(args[0].core, ExprCore::Record { .. })
        && matches!(args[1].core, ExprCore::Record { .. });
    if !is_record_equality {
        return Ok(inner);
    }
    Ok(at_expr(
        &decompose(&args[0], &args[1], &inner),
        &inner.props(),
    ))
}

// N_rewrite.sort_recfields: a record's or a record set's fields in order. Like tlapm, it doesn't
// visit the field values, so a record inside a record keeps the order it's written in.
fn sort_record_fields(expression: &Expr) -> Result<Expr> {
    let sorted = |fields: &[Field]| {
        let mut sorted = fields.to_vec();
        sorted.sort_by(|left, right| compare_strings(&left.name, &right.name).cmp(&0));
        sorted
    };
    match &expression.core {
        ExprCore::Record { fields } => Ok(expression.with_core(ExprCore::Record {
            fields: sorted(fields),
        })),
        ExprCore::Rect { fields } => Ok(expression.with_core(ExprCore::Rect {
            fields: sorted(fields),
        })),
        _ => map_children(expression, &mut sort_record_fields),
    }
}

/// `/[()]|[^\s()]+/g`.
fn get_tokens(text: &str) -> Vec<&str> {
    let mut tokens = Vec::new();
    let mut run_start: Option<usize> = None;
    for (index, character) in text.char_indices() {
        let is_separator = is_js_space(character) || character == '(' || character == ')';
        if !is_separator {
            run_start.get_or_insert(index);
            continue;
        }
        if let Some(start) = run_start.take() {
            tokens.push(&text[start..index]);
        }
        if character != '(' && character != ')' {
            continue;
        }
        tokens.push(&text[index..index + 1]);
    }
    if let Some(start) = run_start {
        tokens.push(&text[start..]);
    }
    tokens
}

// N_axiomatize.collect's state: the symbols and the axioms collected so far, each in the order
// it was first set.
struct Collector<'encoder> {
    encoder: &'encoder Encoder<'encoder>,
    state: CollectState<'encoder>,
    symbols: Vec<(String, SymbolSpec)>,
    symbol_names: HashSet<String>,
    axioms: Vec<(String, Axiom)>,
    axiom_positions: HashMap<String, usize>,
}

impl Collector<'_> {
    fn add(&mut self, name: &str) -> Result<()> {
        let mut work = vec![name.to_string()];
        while !work.is_empty() {
            let mut smallest = 0;
            for (index, candidate) in work.iter().enumerate() {
                if compare_strings(candidate, &work[smallest]) < 0 {
                    smallest = index;
                }
            }
            let next = work.remove(smallest);
            if self.symbol_names.contains(&next) {
                continue;
            }
            let spec = get_symbol_spec(&next, &mut self.state)?;
            for dep in &spec.deps {
                if !work.contains(dep) {
                    work.push(dep.clone());
                }
            }
            for entry in &spec.axioms {
                let key = get_axiom_key(entry);
                match self.axiom_positions.get(&key) {
                    Some(position) => self.axioms[*position].1 = entry.clone(),
                    None => {
                        self.axiom_positions.insert(key.clone(), self.axioms.len());
                        self.axioms.push((key, entry.clone()));
                    }
                }
            }
            self.symbol_names.insert(next.clone());
            self.symbols.push((next, spec));
        }
        Ok(())
    }

    // A flattened symbol stands for a builtin applied to its first-order arguments and then its
    // higher-order ones, so its higher-order text is visited after its arguments.
    fn visit(&mut self, text: &str) -> Result<()> {
        let tokens = get_tokens(text);
        let mut pending: Vec<(i64, String)> = Vec::new();
        let mut depth = 0i64;
        for (index, token) in tokens.iter().enumerate() {
            if *token == "(" {
                depth += 1;
                continue;
            }
            if *token == ")" {
                if pending.last().map(|entry| entry.0) == Some(depth) {
                    let popped = pending.pop().map(|entry| entry.1).unwrap_or_default();
                    self.visit(&popped)?;
                }
                depth -= 1;
                continue;
            }
            let Some(flat) = self.encoder.flattened().get(token).cloned() else {
                if let Some(builtin) = get_tla_name(token) {
                    self.add(&builtin)?;
                }
                continue;
            };
            if !flat.kind.is_empty() {
                self.add(&flat.kind)?;
            }
            if index > 0 && tokens[index - 1] == "(" {
                pending.push((depth, flat.visit.clone()));
            } else {
                self.visit(&flat.visit)?;
            }
        }
        Ok(())
    }
}

// N_axiomatize.collect: each symbol the obligation uses, in the order tlapm visits them, brings
// the symbols and axioms it depends on, smallest name first.
fn collect_symbols<'encoder>(
    entries: &[Entry],
    encoder: &'encoder Encoder<'encoder>,
) -> Result<Collector<'encoder>> {
    let mut collector = Collector {
        encoder,
        state: CollectState {
            record_fields: &encoder.record_fields,
            strings: Vec::new(),
            is_fun_constr: false,
            is_fun_set: false,
            is_except: false,
            tuples: Vec::new(),
            records: Vec::new(),
            anonymous: &encoder.anonymous,
        },
        symbols: Vec::new(),
        symbol_names: HashSet::new(),
        axioms: Vec::new(),
        axiom_positions: HashMap::new(),
    };
    for entry in entries {
        match entry {
            Entry::Text(text) => collector.visit(text)?,
            Entry::Omitted(fact) => collector.visit(&fact.omitted)?,
            Entry::Flattened(_) => {}
        }
    }
    Ok(collector)
}

fn hypothesis() -> Mode {
    Mode {
        is_omitted: false,
        polarity: Polarity::Negative,
        at: None,
        depth: 0,
    }
}

// Prep.expand_defs substitutes visible definitions and pragmas, so they declare nothing.
fn is_expanded(definition: &DefnCore, visibility: Visibility) -> bool {
    matches!(definition, DefnCore::Bpragma { .. })
        || (matches!(definition, DefnCore::Operator { .. }) && visibility == Visibility::Visible)
}

// Smtlib.is_sndord_fact: an ASSUME that declares an operator, which tlapm leaves out.
fn is_second_order(expression: &Expr) -> bool {
    match &expression.core {
        ExprCore::Sequent { sequent } => sequent
            .context
            .iter()
            .any(|hyp| matches!(hyp.core, HypCore::Fresh { shape, .. } if shape > 0)),
        _ => false,
    }
}

struct EncodedContext {
    env: EnvRef,
    entries: Vec<Entry>,
}

fn unsupported(reason: &str) -> Binding {
    Binding::Unsupported {
        reason: reason.to_string(),
    }
}

// Declares each hypothesis's names and asserts its facts, in order, as Smtlib.pp_print_obligation.
fn encode_context(context: &[Hyp], encoder: &mut Encoder) -> Result<EncodedContext> {
    let mut state = EncodedContext {
        env: None,
        entries: Vec::new(),
    };
    for hyp in context {
        let (binding, entries) = match &hyp.core {
            HypCore::Fresh {
                name,
                shape,
                domain,
                domain_visibility,
                ..
            } => {
                let symbol = encoder.get_unique_name(name);
                let declaration = declare(&symbol, *shape, "Idv", "Idv");
                let binding = if *shape == 0 {
                    Binding::Constant {
                        symbol: symbol.clone(),
                    }
                } else {
                    Binding::Operator {
                        symbol: symbol.clone(),
                        arity: *shape,
                    }
                };
                match domain {
                    Some(domain) if *domain_visibility != Visibility::Hidden => {
                        // Rewrite.elim_bounds: NEW x \in S is NEW x and the fact x \in S.
                        let fact = format!(
                            "(assert ({MEM} {symbol} {}))",
                            encoder.encode_idv(domain, &state.env, &hypothesis())?
                        );
                        let mut entries = vec![Entry::Text(declaration)];
                        entries.extend(encoder.get_entries(&fact));
                        (binding, entries)
                    }
                    _ => (binding, vec![Entry::Text(declaration)]),
                }
            }
            // Rewrite.elim_flex: a variable is two constants, the second for its primed value.
            HypCore::Flex { name } => {
                let symbol = encoder.get_unique_name(name);
                let primed = encoder.get_unique_name(&format!("{name}_prime"));
                let entries = vec![
                    Entry::Text(declare(&symbol, 0, "Idv", "Idv")),
                    Entry::Text(declare(&primed, 0, "Idv", "Idv")),
                ];
                (
                    Binding::Variable {
                        name: name.clone(),
                        symbol,
                        primed,
                    },
                    entries,
                )
            }
            HypCore::Defn {
                definition,
                visibility,
                ..
            } => match &definition.core {
                core if is_expanded(core, *visibility) => {
                    (unsupported("an expanded definition"), Vec::new())
                }
                DefnCore::Instance { .. } => (unsupported("an instance"), Vec::new()),
                DefnCore::Recursive { name, shape } => {
                    let symbol = encoder.get_unique_name(&format!("CONSTANT_{name}_"));
                    let declaration = declare(&symbol, *shape, "Idv", "Idv");
                    (
                        Binding::Operator {
                            symbol,
                            arity: *shape,
                        },
                        vec![Entry::Text(declaration)],
                    )
                }
                DefnCore::Operator { name, body } => {
                    let params = match &body.core {
                        ExprCore::Lambda { params, .. } => params.as_slice(),
                        _ => &[],
                    };
                    if params.iter().any(|param| param.shape > 0) {
                        (
                            Binding::SecondOrder {
                                name: name.clone(),
                                shapes: params.iter().map(|param| param.shape).collect(),
                            },
                            Vec::new(),
                        )
                    } else {
                        let symbol = encoder.get_unique_name(name);
                        let declaration = declare(&symbol, params.len(), "Idv", "Idv");
                        (
                            Binding::Operator {
                                symbol,
                                arity: params.len(),
                            },
                            vec![Entry::Text(declaration)],
                        )
                    }
                }
                DefnCore::Bpragma { .. } => (unsupported("a definition"), Vec::new()),
            },
            HypCore::Fact {
                expression,
                visibility,
                ..
            } => {
                let binding = unsupported("a reference to a fact");
                if *visibility == Visibility::Hidden {
                    (binding, Vec::new())
                } else {
                    let is_omitted = is_second_order(expression);
                    let fact = encoder.encode_bool(
                        expression,
                        &state.env,
                        &Mode {
                            is_omitted,
                            ..hypothesis()
                        },
                    )?;
                    let entries = encoder.get_entries(&format!("(assert {fact})"));
                    let entries = if is_omitted {
                        entries
                            .into_iter()
                            .map(|entry| match entry {
                                Entry::Text(omitted) => Entry::Omitted(OmittedFact { omitted }),
                                other => other,
                            })
                            .collect()
                    } else {
                        entries
                    };
                    (binding, entries)
                }
            }
        };
        state.env = encoder.push(&state.env, binding);
        state.entries.extend(entries);
    }
    Ok(state)
}

/// `/\bIdv\b/`: Idv between characters that aren't word characters.
fn has_idv_word(line: &str) -> bool {
    let is_word = |byte: u8| byte.is_ascii_alphanumeric() || byte == b'_';
    let bytes = line.as_bytes();
    line.match_indices("Idv").any(|(start, _)| {
        let end = start + 3;
        (start == 0 || !is_word(bytes[start - 1]))
            && bytes.get(end).is_none_or(|next| !is_word(*next))
    })
}

// Smtlib.pp_print_obligation: the logic, the sort, the builtin symbols by name, their axioms,
// then the hypotheses in order, the goal last. It fails with an unsupported error for what the
// encoding can't express, where tlapm's encoder fails.
pub fn encode_smt(prepared: &Sequent, session: &mut EncodingSession) -> Result<String> {
    let simplified = sort_record_fields(&simplify_record_equalities(&expr(ExprCore::Sequent {
        sequent: prepared.clone(),
    }))?)?;
    let sequent = match &simplified.core {
        ExprCore::Sequent { sequent } => sequent,
        _ => prepared,
    };
    let mut encoder = create_encoder(session);
    let context = encode_context(&sequent.context, &mut encoder)?;
    let goal = if is_second_order(&sequent.active) {
        Vec::new()
    } else {
        let active = encoder.encode_bool(
            &sequent.active,
            &context.env,
            &Mode {
                polarity: Polarity::Positive,
                ..hypothesis()
            },
        )?;
        encoder.get_entries(&format!("(assert (! (not {active}) :named |Goal|))"))
    };
    let mut entries = context.entries;
    entries.extend(goal);
    let encoder = &encoder;
    let mut printer = create_printer(&encoder.declared);
    let collected = collect_symbols(&entries, encoder)?;
    let mut symbols: Vec<&(String, SymbolSpec)> = collected.symbols.iter().collect();
    symbols.sort_by(|left, right| compare_strings(&left.0, &right.0).cmp(&0));
    let mut axioms: Vec<&Axiom> = collected.axioms.iter().map(|entry| &entry.1).collect();
    axioms.sort_by(|left, right| compare_axioms(left, right).cmp(&0));
    let keys: HashSet<String> = collected
        .axioms
        .iter()
        .map(|entry| entry.0.clone())
        .collect();
    let mut lines: Vec<String> = symbols
        .iter()
        .filter_map(|symbol| symbol.1.declaration.clone())
        .collect();
    lines.extend(axioms.iter().filter_map(|entry| {
        entry
            .formula
            .as_ref()
            .map(|formula| format!("(assert (! {formula} :named |{}|))", entry.label))
    }));
    for entry in &entries {
        match entry {
            Entry::Text(text) => lines.push(text.clone()),
            Entry::Omitted(_) => {}
            Entry::Flattened(flat) => lines.extend(flat.get_lines(&keys)),
        }
    }
    // Smtlib.collect_sorts declares Idv only when a symbol or a bound variable has that sort.
    // Type.Synthesize gives that sort to each definition left in the context, though none is printed.
    let is_idv_used = lines.iter().any(|line| has_idv_word(line))
        || sequent.context.iter().any(|hyp| match &hyp.core {
            HypCore::Defn {
                definition,
                visibility,
                ..
            } => {
                matches!(
                    definition.core,
                    DefnCore::Operator { .. } | DefnCore::Recursive { .. }
                ) && !is_expanded(&definition.core, *visibility)
            }
            _ => false,
        });
    let mut header = vec!["(set-logic UFNIA)".to_string()];
    if is_idv_used {
        header.push("(declare-sort Idv 0)".to_string());
    }
    let mut printed = Vec::with_capacity(header.len() + lines.len() + 2);
    for line in header.iter().chain(&lines) {
        printed.push(printer.resolve(line)?);
    }
    printed.push("(check-sat)".to_string());
    printed.push("(exit)".to_string());
    Ok(printed.join("\n"))
}

// Expected values from running the TypeScript: each case is the session's count before, a sequent
// as the TypeScript's JSON without locations, the count after, and the text or the error.
#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::*;
    use crate::errors::ObligationError;
    use crate::expression::{
        Bound, BoundDomain, Bullet, CaseArm, Defn, ExceptPoint, ExceptSpec, ExprNode, Level, Modal,
        Param, ParenForm, Quantifier, Time, WhereDefined, XlabelIndex, hyp,
    };
    use crate::pragma::OldMethod;

    enum Json {
        Null,
        Bool(bool),
        Number(f64),
        Text(String),
        List(Vec<Json>),
        Object(Vec<(String, Json)>),
    }

    struct Parser<'text> {
        bytes: &'text [u8],
        index: usize,
    }

    impl Parser<'_> {
        fn skip_space(&mut self) {
            while self
                .bytes
                .get(self.index)
                .is_some_and(u8::is_ascii_whitespace)
            {
                self.index += 1;
            }
        }

        fn next_byte(&mut self) -> u8 {
            self.skip_space();
            self.index += 1;
            self.bytes[self.index - 1]
        }

        fn parse_text(&mut self) -> String {
            assert_eq!(self.next_byte(), b'"');
            let mut units: Vec<u16> = Vec::new();
            let mut run: Vec<u8> = Vec::new();
            loop {
                let byte = self.bytes[self.index];
                self.index += 1;
                if byte == b'"' {
                    break;
                }
                if byte != b'\\' {
                    run.push(byte);
                    continue;
                }
                let escape = self.bytes[self.index];
                self.index += 1;
                let unit = match escape {
                    b'n' => u16::from(b'\n'),
                    b't' => u16::from(b'\t'),
                    b'r' => u16::from(b'\r'),
                    b'b' => 8,
                    b'f' => 12,
                    b'u' => {
                        let hex = std::str::from_utf8(&self.bytes[self.index..self.index + 4])
                            .expect("hex digits");
                        self.index += 4;
                        u16::from_str_radix(hex, 16).expect("hex digits")
                    }
                    other => u16::from(other),
                };
                let text = String::from_utf8(std::mem::take(&mut run)).expect("UTF-8");
                units.extend(text.encode_utf16());
                units.push(unit);
            }
            units.extend(String::from_utf8(run).expect("UTF-8").encode_utf16());
            String::from_utf16(&units).expect("UTF-16")
        }

        fn parse(&mut self) -> Json {
            self.skip_space();
            match self.bytes[self.index] {
                b'"' => Json::Text(self.parse_text()),
                b'{' => {
                    self.index += 1;
                    let mut entries = Vec::new();
                    self.skip_space();
                    if self.bytes[self.index] == b'}' {
                        self.index += 1;
                        return Json::Object(entries);
                    }
                    loop {
                        let key = self.parse_text();
                        assert_eq!(self.next_byte(), b':');
                        entries.push((key, self.parse()));
                        if self.next_byte() == b'}' {
                            return Json::Object(entries);
                        }
                    }
                }
                b'[' => {
                    self.index += 1;
                    let mut items = Vec::new();
                    self.skip_space();
                    if self.bytes[self.index] == b']' {
                        self.index += 1;
                        return Json::List(items);
                    }
                    loop {
                        items.push(self.parse());
                        if self.next_byte() == b']' {
                            return Json::List(items);
                        }
                    }
                }
                b't' => {
                    self.index += 4;
                    Json::Bool(true)
                }
                b'f' => {
                    self.index += 5;
                    Json::Bool(false)
                }
                b'n' => {
                    self.index += 4;
                    Json::Null
                }
                _ => {
                    let start = self.index;
                    while self.bytes.get(self.index).is_some_and(|byte| {
                        byte.is_ascii_digit() || matches!(byte, b'-' | b'+' | b'.' | b'e' | b'E')
                    }) {
                        self.index += 1;
                    }
                    let text = std::str::from_utf8(&self.bytes[start..self.index]).expect("UTF-8");
                    Json::Number(text.parse().expect("a number"))
                }
            }
        }
    }

    fn parse_json(text: &str) -> Json {
        Parser {
            bytes: text.as_bytes(),
            index: 0,
        }
        .parse()
    }

    impl Json {
        fn get(&self, key: &str) -> Option<&Json> {
            match self {
                Json::Object(entries) => entries
                    .iter()
                    .find(|entry| entry.0 == key && !matches!(entry.1, Json::Null))
                    .map(|entry| &entry.1),
                _ => None,
            }
        }

        fn field(&self, key: &str) -> &Json {
            self.get(key).unwrap_or_else(|| panic!("no field {key}"))
        }

        fn text(&self) -> &str {
            match self {
                Json::Text(text) => text,
                _ => panic!("not a string"),
            }
        }

        fn number(&self) -> f64 {
            match self {
                Json::Number(number) => *number,
                _ => panic!("not a number"),
            }
        }

        fn items(&self) -> &[Json] {
            match self {
                Json::List(items) => items,
                _ => panic!("not a list"),
            }
        }

        fn name(&self) -> String {
            self.field("name").text().to_string()
        }

        fn kind(&self) -> &str {
            self.field("kind").text()
        }
    }

    const BUILTINS: [Builtin; 72] = [
        Builtin::TRUE,
        Builtin::FALSE,
        Builtin::Implies,
        Builtin::Equiv,
        Builtin::Conj,
        Builtin::Disj,
        Builtin::Neg,
        Builtin::Eq,
        Builtin::Neq,
        Builtin::STRING,
        Builtin::BOOLEAN,
        Builtin::SUBSET,
        Builtin::UNION,
        Builtin::DOMAIN,
        Builtin::Subseteq,
        Builtin::Mem,
        Builtin::Notmem,
        Builtin::Setminus,
        Builtin::Cap,
        Builtin::Cup,
        Builtin::Prime,
        Builtin::StrongPrime,
        Builtin::Leadsto,
        Builtin::ENABLED,
        Builtin::UNCHANGED,
        Builtin::Cdot,
        Builtin::Actplus,
        Builtin::BoxTrue,
        Builtin::BoxFalse,
        Builtin::Diamond,
        Builtin::Nat,
        Builtin::Int,
        Builtin::Real,
        Builtin::Plus,
        Builtin::Minus,
        Builtin::Uminus,
        Builtin::Times,
        Builtin::Ratio,
        Builtin::Quotient,
        Builtin::Remainder,
        Builtin::Exp,
        Builtin::Infinity,
        Builtin::Lteq,
        Builtin::Lt,
        Builtin::Gteq,
        Builtin::Gt,
        Builtin::Divides,
        Builtin::Range,
        Builtin::Seq,
        Builtin::Len,
        Builtin::BSeq,
        Builtin::Cat,
        Builtin::Append,
        Builtin::Head,
        Builtin::Tail,
        Builtin::SubSeq,
        Builtin::SelectSeq,
        Builtin::OneArg,
        Builtin::Extend,
        Builtin::Print,
        Builtin::PrintT,
        Builtin::Assert,
        Builtin::JavaTime,
        Builtin::TLCGet,
        Builtin::TLCSet,
        Builtin::Permutations,
        Builtin::SortSeq,
        Builtin::RandomElement,
        Builtin::Any,
        Builtin::ToString,
        Builtin::Unprimable,
        Builtin::Irregular,
    ];

    fn to_exprs(json: &Json) -> Vec<Expr> {
        json.items().iter().map(to_expr).collect()
    }

    fn to_level(json: &Json) -> Level {
        match json.text() {
            "Constant" => Level::Constant,
            "State" => Level::State,
            "Action" => Level::Action,
            "Temporal" => Level::Temporal,
            _ => Level::Unknown,
        }
    }

    fn to_quantifier(json: &Json) -> Quantifier {
        if json.text() == "Forall" {
            Quantifier::Forall
        } else {
            Quantifier::Exists
        }
    }

    fn to_bounds(json: &Json) -> Vec<Bound> {
        json.items()
            .iter()
            .map(|bound| {
                let domain = bound.field("domain");
                Bound {
                    name: bound.name(),
                    level: bound.get("level").map_or(Level::Unknown, to_level),
                    domain: match domain.kind() {
                        "Domain" => BoundDomain::Domain(to_expr(domain.field("expression"))),
                        "Ditto" => BoundDomain::Ditto,
                        _ => BoundDomain::NoDomain,
                    },
                }
            })
            .collect()
    }

    fn to_fields(json: &Json) -> Vec<Field> {
        json.items()
            .iter()
            .map(|field| Field {
                name: field.name(),
                value: to_expr(field.field("value")),
            })
            .collect()
    }

    fn to_except_specs(json: &Json) -> Vec<ExceptSpec> {
        json.items()
            .iter()
            .map(|spec| ExceptSpec {
                trail: spec
                    .field("trail")
                    .items()
                    .iter()
                    .map(|point| match point.kind() {
                        "Dot" => ExceptPoint::Dot(point.field("field").text().to_string()),
                        _ => ExceptPoint::Apply(to_expr(point.field("expression"))),
                    })
                    .collect(),
                value: to_expr(spec.field("value")),
            })
            .collect()
    }

    fn to_paren_form(json: &Json) -> ParenForm {
        match json.kind() {
            "Xlabel" => ParenForm::Xlabel {
                label: json.field("label").text().to_string(),
                indices: json
                    .field("indices")
                    .items()
                    .iter()
                    .map(|index| XlabelIndex {
                        name: index.name(),
                        index: index.field("index").number() as usize,
                    })
                    .collect(),
            },
            "Nlabel" => ParenForm::Nlabel {
                label: json.field("label").text().to_string(),
                names: json
                    .field("names")
                    .items()
                    .iter()
                    .map(|name| name.text().to_string())
                    .collect(),
            },
            _ => ParenForm::Syntax,
        }
    }

    fn to_modal(json: &Json) -> Modal {
        if json.text() == "Box" {
            Modal::Box
        } else {
            Modal::Dia
        }
    }

    fn to_expr(json: &Json) -> Expr {
        let core = match json.kind() {
            "Ix" => ExprCore::Ix {
                index: json.field("index").number() as isize,
            },
            "Opaque" => ExprCore::Opaque { name: json.name() },
            "Internal" => {
                let name = json.field("builtin").text();
                ExprCore::Internal {
                    builtin: BUILTINS
                        .iter()
                        .copied()
                        .find(|builtin| builtin.name() == name)
                        .unwrap_or_else(|| panic!("no builtin {name}")),
                }
            }
            "Lambda" => ExprCore::Lambda {
                params: json
                    .field("params")
                    .items()
                    .iter()
                    .map(|param| Param {
                        name: param.name(),
                        shape: param.field("shape").number() as usize,
                        location: None,
                    })
                    .collect(),
                body: to_expr(json.field("body")),
            },
            "Sequent" => ExprCore::Sequent {
                sequent: to_sequent(json.field("sequent")),
            },
            "Apply" => ExprCore::Apply {
                operator: to_expr(json.field("operator")),
                args: to_exprs(json.field("args")),
            },
            // The encoding never reads the method.
            "With" => ExprCore::With {
                expression: to_expr(json.field("expression")),
                method: OldMethod {
                    name: "auto".to_string(),
                    tactic: None,
                    timeout: None,
                },
            },
            "If" => ExprCore::If {
                condition: to_expr(json.field("condition")),
                consequent: to_expr(json.field("consequent")),
                alternative: to_expr(json.field("alternative")),
            },
            "List" => ExprCore::List {
                bullet: match json.field("bullet").text() {
                    "And" => Bullet::And,
                    "Or" => Bullet::Or,
                    _ => Bullet::Refs,
                },
                items: to_exprs(json.field("items")),
            },
            "Quant" => ExprCore::Quant {
                quantifier: to_quantifier(json.field("quantifier")),
                bounds: to_bounds(json.field("bounds")),
                body: to_expr(json.field("body")),
            },
            "Tquant" => ExprCore::Tquant {
                quantifier: to_quantifier(json.field("quantifier")),
                names: json
                    .field("names")
                    .items()
                    .iter()
                    .map(|name| name.text().to_string())
                    .collect(),
                body: to_expr(json.field("body")),
            },
            "Choose" => ExprCore::Choose {
                name: json.name(),
                domain: json.get("domain").map(to_expr),
                body: to_expr(json.field("body")),
            },
            "SetSt" => ExprCore::SetSt {
                name: json.name(),
                domain: to_expr(json.field("domain")),
                body: to_expr(json.field("body")),
            },
            "SetOf" => ExprCore::SetOf {
                element: to_expr(json.field("element")),
                bounds: to_bounds(json.field("bounds")),
            },
            "SetEnum" => ExprCore::SetEnum {
                elements: to_exprs(json.field("elements")),
            },
            "Product" => ExprCore::Product {
                factors: to_exprs(json.field("factors")),
            },
            "Tuple" => ExprCore::Tuple {
                elements: to_exprs(json.field("elements")),
            },
            "Fcn" => ExprCore::Fcn {
                bounds: to_bounds(json.field("bounds")),
                body: to_expr(json.field("body")),
            },
            "FcnApp" => ExprCore::FcnApp {
                function: to_expr(json.field("function")),
                args: to_exprs(json.field("args")),
            },
            "Arrow" => ExprCore::Arrow {
                domain: to_expr(json.field("domain")),
                range: to_expr(json.field("range")),
            },
            "Rect" => ExprCore::Rect {
                fields: to_fields(json.field("fields")),
            },
            "Record" => ExprCore::Record {
                fields: to_fields(json.field("fields")),
            },
            "Except" => ExprCore::Except {
                function: to_expr(json.field("function")),
                specs: to_except_specs(json.field("specs")),
            },
            "Dot" => ExprCore::Dot {
                expression: to_expr(json.field("expression")),
                field: json.field("field").text().to_string(),
            },
            "Sub" => ExprCore::Sub {
                modal: to_modal(json.field("modal")),
                action: to_expr(json.field("action")),
                subscript: to_expr(json.field("subscript")),
            },
            "Tsub" => ExprCore::Tsub {
                modal: to_modal(json.field("modal")),
                action: to_expr(json.field("action")),
                subscript: to_expr(json.field("subscript")),
            },
            "Fair" => ExprCore::Fair {
                fairness: if json.field("fairness").text() == "Weak" {
                    crate::expression::Fairness::Weak
                } else {
                    crate::expression::Fairness::Strong
                },
                subscript: to_expr(json.field("subscript")),
                action: to_expr(json.field("action")),
            },
            "Case" => ExprCore::Case {
                arms: json
                    .field("arms")
                    .items()
                    .iter()
                    .map(|arm| CaseArm {
                        condition: to_expr(arm.field("condition")),
                        body: to_expr(arm.field("body")),
                    })
                    .collect(),
                other: json.get("other").map(to_expr),
            },
            "String" => ExprCore::String {
                value: json.field("value").text().to_string(),
            },
            "Num" => ExprCore::Num {
                integer: json.field("integer").text().to_string(),
                fraction: json.field("fraction").text().to_string(),
            },
            "At" => ExprCore::At {
                is_except: matches!(json.get("isExcept"), Some(Json::Bool(true))),
            },
            "Parens" => ExprCore::Parens {
                expression: to_expr(json.field("expression")),
                form: to_paren_form(json.field("form")),
            },
            // The cases have neither definitions nor selectors here.
            "Let" => ExprCore::Let {
                definitions: Vec::new(),
                body: to_expr(json.field("body")),
            },
            "Bang" => ExprCore::Bang {
                expression: to_expr(json.field("expression")),
                selectors: Vec::new(),
            },
            other => panic!("no expression {other}"),
        };
        Rc::new(ExprNode {
            core,
            location: None,
            is_atomic: matches!(json.get("isAtomic"), Some(Json::Bool(true))),
        })
    }

    fn to_visibility(json: &Json) -> Visibility {
        if json.text() == "Hidden" {
            Visibility::Hidden
        } else {
            Visibility::Visible
        }
    }

    fn to_hyp(json: &Json) -> Hyp {
        hyp(match json.kind() {
            "Fresh" => HypCore::Fresh {
                name: json.name(),
                shape: json.field("shape").number() as usize,
                level: to_level(json.field("level")),
                domain: json.get("domain").map(to_expr),
                domain_visibility: to_visibility(json.field("domainVisibility")),
            },
            "Flex" => HypCore::Flex { name: json.name() },
            "Defn" => {
                let definition = json.field("definition");
                let name = definition.name();
                let core = match definition.kind() {
                    "Recursive" => DefnCore::Recursive {
                        name,
                        shape: definition.field("shape").number() as usize,
                    },
                    // The encoding never reads the methods.
                    "Bpragma" => DefnCore::Bpragma {
                        name,
                        body: to_expr(definition.field("body")),
                        methods: Vec::new(),
                    },
                    "Operator" => DefnCore::Operator {
                        name,
                        body: to_expr(definition.field("body")),
                    },
                    other => panic!("no definition {other}"),
                };
                HypCore::Defn {
                    definition: Defn {
                        core,
                        location: None,
                    },
                    where_defined: WhereDefined::User,
                    visibility: to_visibility(json.field("visibility")),
                    is_local: false,
                    is_constness_unset: false,
                }
            }
            "Fact" => HypCore::Fact {
                expression: to_expr(json.field("expression")),
                visibility: to_visibility(json.field("visibility")),
                time: Time::Now,
                use_location: None,
            },
            other => panic!("no hypothesis {other}"),
        })
    }

    fn to_sequent(json: &Json) -> Sequent {
        Sequent {
            context: json.field("context").items().iter().map(to_hyp).collect(),
            active: to_expr(json.field("active")),
        }
    }

    // One case: [before, sequent, after, the text or the error].
    fn check(case: &Json) {
        let items = case.items();
        let mut session = EncodingSession {
            case_errors: items[0].number() as usize,
        };
        // The TypeScript's own errors, such as BigInt's SyntaxError, are bugs here.
        let encoded =
            encode_smt(&to_sequent(&items[1]), &mut session).unwrap_or_else(|error| match error {
                ObligationError::Proof { exception, .. } => exception,
                other => format!("{}: {}", other.name(), other.message()),
            });
        assert_eq!(encoded, items[3].text());
        assert_eq!(session.case_errors, items[2].number() as usize);
    }

    // Obligations of tlapm's tests, examples and library after Prep, as the TypeScript prepares them.
    const TLAPM_CASES: &str = r###"[
[0,{"context":[],"active":{"kind":"Internal","builtin":"TRUE"}},0,"(set-logic UFNIA)\n(assert (! (not true) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[],"active":{"kind":"Internal","builtin":"FALSE"}},0,"(set-logic UFNIA)\n(assert (! (not false) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Hidden","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}},0,"(set-logic UFNIA)\n(assert (! (not true) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Flex","name":"VARIABLE_x_"}],"active":{"kind":"Internal","builtin":"TRUE"}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__VARIABLE__x__ () Idv)\n(declare-fun smt__VARIABLE__x____prime () Idv)\n(assert (! (not true) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Internal","builtin":"TRUE"},"action":{"kind":"Internal","builtin":"TRUE"}},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Internal","builtin":"TRUE"},"action":{"kind":"Internal","builtin":"TRUE"}}]}},0,"TlaUnsupportedError: a temporal formula"],
[0,{"context":[{"kind":"Fresh","name":"CONSTANT_C_","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Flex","name":"VARIABLE_v_"}],"active":{"kind":"Internal","builtin":"TRUE"}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__CONSTANT__C__ () Idv)\n(declare-fun smt__VARIABLE__v__ () Idv)\n(declare-fun smt__VARIABLE__v____prime () Idv)\n(assert (! (not true) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Defn","definition":{"kind":"Operator","name":"CONSTANT_Op_","body":{"kind":"Lambda","params":[{"name":"Unknown_x_","shape":0}],"body":{"kind":"Internal","builtin":"TRUE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Internal","builtin":"TRUE"}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__CONSTANT__Op__ (Idv) Idv)\n(assert (! (not true) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Flex","name":"VARIABLE_x_"}],"active":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"CONSTANT_y_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__VARIABLE__x__ () Idv)\n(declare-fun smt__VARIABLE__x____prime () Idv)\n(assert (! (not (exists ((smt__CONSTANT__y__ Idv)) (distinct smt__CONSTANT__y__ smt__VARIABLE__x__))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Flex","name":"VARIABLE_v_"},{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_I_","body":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_y_","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":1}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Ix","index":1},"visibility":"Visible","time":"Now"}],"active":{"kind":"Opaque","name":"hb9f01"}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Anon__OPAQUE__hb9f01 () Idv)\n(declare-fun smt__TLA____Tt__Idv () Idv)\n(declare-fun smt__VARIABLE__v__ () Idv)\n(declare-fun smt__VARIABLE__v____prime () Idv)\n(declare-fun smt__STATE__I__ () Idv)\n(assert (= smt__STATE__I__ smt__TLA____Tt__Idv))\n(assert (! (not (= smt__TLA____Anon__OPAQUE__hb9f01 smt__TLA____Tt__Idv)) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Flex","name":"VARIABLE_Y_"},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"List","bullet":"Refs","items":[]},"visibility":"Hidden","time":"Always"}],"active":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_z_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"If","condition":{"kind":"Opaque","name":"VARIABLE_Y_#prime"},"consequent":{"kind":"Ix","index":1},"alternative":{"kind":"Ix","index":1}},{"kind":"Ix","index":1}]}}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Tt__Idv () Idv)\n(declare-fun smt__VARIABLE__Y__ () Idv)\n(declare-fun smt__VARIABLE__Y____prime () Idv)\n(assert (! (not (forall ((smt__CONSTANT__z__ Idv)) (= (ite (= smt__VARIABLE__Y____prime smt__TLA____Tt__Idv) smt__CONSTANT__z__ smt__CONSTANT__z__) smt__CONSTANT__z__))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fact","expression":{"kind":"With","expression":{"kind":"Internal","builtin":"TRUE"},"method":{"name":"cooper"}},"visibility":"Hidden","time":"Always"},{"kind":"Fresh","name":"CONSTANT_XXX_","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"CONSTANT_i_","shape":0,"level":"Constant","domain":{"kind":"Internal","builtin":"Int"},"domainVisibility":"Visible"}],"active":{"kind":"With","expression":{"kind":"Internal","builtin":"TRUE"},"method":{"name":"cooper"}}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(declare-fun smt__CONSTANT__XXX__ () Idv)\n(declare-fun smt__CONSTANT__i__ () Idv)\n(assert (smt__TLA____Mem smt__CONSTANT__i__ smt__TLA____IntSet))\n(assert (! (not true) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fact","expression":{"kind":"With","expression":{"kind":"Internal","builtin":"TRUE"},"method":{"name":"cooper"}},"visibility":"Hidden","time":"Always"},{"kind":"Fresh","name":"CONSTANT_XXX_","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"CONSTANT_i_","shape":0,"level":"Constant","domain":{"kind":"Internal","builtin":"Int"},"domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"With","expression":{"kind":"Internal","builtin":"TRUE"},"method":{"name":"cooper"}},"visibility":"Visible","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":3},{"kind":"Internal","builtin":"Int"}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(declare-fun smt__CONSTANT__XXX__ () Idv)\n(declare-fun smt__CONSTANT__i__ () Idv)\n(assert (smt__TLA____Mem smt__CONSTANT__i__ smt__TLA____IntSet))\n(assert true)\n(assert (! (not (smt__TLA____Mem smt__CONSTANT__XXX__ smt__TLA____IntSet)) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[],"active":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_S_","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"CONSTANT_T_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":3}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}]}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]}]}}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (not (forall ((smt__CONSTANT__S__ Idv) (smt__CONSTANT__T__ Idv)) (=> (forall ((smt__CONSTANT__x__ Idv)) (= (smt__TLA____Mem smt__CONSTANT__x__ smt__CONSTANT__S__) (smt__TLA____Mem smt__CONSTANT__x__ smt__CONSTANT__T__))) (= smt__CONSTANT__S__ smt__CONSTANT__T__)))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Flex","name":"VARIABLE_Y_"},{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_P_","body":{"kind":"Lambda","params":[{"name":"Unknown_a_","shape":0},{"name":"Unknown_x_","shape":0}],"body":{"kind":"If","condition":{"kind":"Ix","index":3},"consequent":{"kind":"Ix","index":1},"alternative":{"kind":"Ix","index":1}}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_z_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Ix","index":1}]},{"kind":"Ix","index":1}]}},"visibility":"Hidden","time":"Always"}],"active":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_z_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Opaque","name":"h4b51f"},"args":[{"kind":"Opaque","name":"VARIABLE_Y_#prime"},{"kind":"Ix","index":1}]},{"kind":"Ix","index":1}]}}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Anon__h4b51f (Idv Idv) Idv)\n(declare-fun smt__VARIABLE__Y__ () Idv)\n(declare-fun smt__VARIABLE__Y____prime () Idv)\n(declare-fun smt__STATE__P__ (Idv Idv) Idv)\n(assert (! (not (forall ((smt__CONSTANT__z__ Idv)) (= (smt__TLA____Anon__h4b51f smt__VARIABLE__Y____prime smt__CONSTANT__z__) smt__CONSTANT__z__))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_S_","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"CONSTANT_T_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":3}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}]}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]}]}},"visibility":"Hidden","time":"Always"}],"active":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_S_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Notmem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (not (forall ((smt__CONSTANT__S__ Idv)) (exists ((smt__CONSTANT__x__ Idv)) (not (smt__TLA____Mem smt__CONSTANT__x__ smt__CONSTANT__S__))))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_S_","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"CONSTANT_T_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":3}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}]}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]}]}},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_S_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Notmem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}},"visibility":"Hidden","time":"Always"},{"kind":"Defn","definition":{"kind":"Operator","name":"CONSTANT_EnabledWrapper_","body":{"kind":"Lambda","params":[{"name":"Unknown_Op_","shape":1}],"body":{"kind":"Internal","builtin":"FALSE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"CONSTANT_CdotWrapper_","body":{"kind":"Lambda","params":[{"name":"Unknown_Op_","shape":1}],"body":{"kind":"Internal","builtin":"FALSE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neg"},"args":[{"kind":"Internal","builtin":"FALSE"}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(assert (! (not (not false)) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_S_","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"CONSTANT_T_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":3}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}]}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]}]}},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_S_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Notmem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}},"visibility":"Hidden","time":"Always"},{"kind":"Defn","definition":{"kind":"Operator","name":"CONSTANT_EnabledWrapper_","body":{"kind":"Lambda","params":[{"name":"Unknown_Op_","shape":1}],"body":{"kind":"Internal","builtin":"FALSE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"CONSTANT_CdotWrapper_","body":{"kind":"Lambda","params":[{"name":"Unknown_Op_","shape":1}],"body":{"kind":"Internal","builtin":"FALSE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Internal","builtin":"TRUE"},{"kind":"Internal","builtin":"TRUE"}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(assert (! (not (and true true)) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Flex","name":"VARIABLE_x_"},{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_R_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Internal","builtin":"TRUE"}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_A_","body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Ix","index":1}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"ACTION_B_","body":{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Internal","builtin":"TRUE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"FALSE"}]}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]},{"kind":"List","bullet":"And","items":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":4},{"kind":"Internal","builtin":"FALSE"}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]},{"kind":"Internal","builtin":"FALSE"}]}]}]},"visibility":"Hidden","time":"Now"}],"active":{"kind":"Internal","builtin":"TRUE"}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__VARIABLE__x__ () Idv)\n(declare-fun smt__VARIABLE__x____prime () Idv)\n(declare-fun smt__ACTION__R__ () Idv)\n(declare-fun smt__ACTION__A__ () Idv)\n(declare-fun smt__ACTION__B__ () Idv)\n(assert (! (not true) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_S_","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"CONSTANT_T_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":3}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}]}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]}]}},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_S_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Notmem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}},"visibility":"Hidden","time":"Always"},{"kind":"Defn","definition":{"kind":"Operator","name":"CONSTANT_EnabledWrapper_","body":{"kind":"Lambda","params":[{"name":"Unknown_Op_","shape":1}],"body":{"kind":"Internal","builtin":"FALSE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"CONSTANT_CdotWrapper_","body":{"kind":"Lambda","params":[{"name":"Unknown_Op_","shape":1}],"body":{"kind":"Internal","builtin":"FALSE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Num","integer":"2","fraction":""},{"kind":"Num","integer":"2","fraction":""}]},{"kind":"Num","integer":"4","fraction":""}]},"visibility":"Hidden","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(assert (! (not true) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Flex","name":"VARIABLE_z_"},{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_S_","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"CONSTANT_T_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":3}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}]}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]}]}},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_S_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Notmem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}},"visibility":"Hidden","time":"Always"},{"kind":"Defn","definition":{"kind":"Operator","name":"CONSTANT_M!EnabledWrapper_","body":{"kind":"Lambda","params":[{"name":"Unknown_Op_","shape":1}],"body":{"kind":"Internal","builtin":"FALSE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"CONSTANT_M!CdotWrapper_","body":{"kind":"Lambda","params":[{"name":"Unknown_Op_","shape":1}],"body":{"kind":"Internal","builtin":"FALSE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"STATE_M!A_","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Hidden","time":"Always"}],"active":{"kind":"Tquant","quantifier":"Exists","names":["x"],"body":{"kind":"Opaque","name":"x#prime"}}},0,"TlaUnsupportedError: a temporal formula"],
[0,{"context":[{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_S_","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"CONSTANT_T_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":3}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}]}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]}]}},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_S_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Notmem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}},"visibility":"Hidden","time":"Always"},{"kind":"Defn","definition":{"kind":"Operator","name":"CONSTANT_EnabledWrapper_","body":{"kind":"Lambda","params":[{"name":"Unknown_Op_","shape":1}],"body":{"kind":"Internal","builtin":"FALSE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"CONSTANT_CdotWrapper_","body":{"kind":"Lambda","params":[{"name":"Unknown_Op_","shape":1}],"body":{"kind":"Internal","builtin":"FALSE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Internal","builtin":"FALSE"},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Internal","builtin":"TRUE"},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Internal","builtin":"TRUE"},{"kind":"Internal","builtin":"FALSE"}]}]}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(assert (! (not (=> false (and true (or true false)))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_S_","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"CONSTANT_f_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"CONSTANT_A_","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"SUBSET"},"args":[{"kind":"Ix","index":2}]}}}],"body":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":3}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neq"},"args":[{"kind":"FcnApp","function":{"kind":"Ix","index":3},"args":[{"kind":"Ix","index":1}]},{"kind":"Ix","index":2}]}}}},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"CONSTANT_S_","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"FALSE"}}},"visibility":"Visible","time":"Always"}],"active":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_S_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Notmem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (forall ((smt__CONSTANT__S__ Idv)) (=> (forall ((smt__CONSTANT__x__ Idv)) (smt__TLA____Mem smt__CONSTANT__x__ smt__CONSTANT__S__)) false)))\n(assert (! (not (forall ((smt__CONSTANT__S__ Idv)) (exists ((smt__CONSTANT__x__ Idv)) (not (smt__TLA____Mem smt__CONSTANT__x__ smt__CONSTANT__S__))))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_S_","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"CONSTANT_T_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":3}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}]}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]}]}},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_S_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Notmem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}},"visibility":"Hidden","time":"Always"},{"kind":"Defn","definition":{"kind":"Operator","name":"CONSTANT_EnabledWrapper_","body":{"kind":"Lambda","params":[{"name":"Unknown_Op_","shape":1}],"body":{"kind":"Internal","builtin":"FALSE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"CONSTANT_CdotWrapper_","body":{"kind":"Lambda","params":[{"name":"Unknown_Op_","shape":1}],"body":{"kind":"Internal","builtin":"FALSE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fresh","name":"CONSTANT_x_","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"CONSTANT_y_","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Record","fields":[{"name":"foo","value":{"kind":"Ix","index":2}},{"name":"bar","value":{"kind":"Ix","index":1}}]},{"kind":"Record","fields":[{"name":"foo","value":{"kind":"Ix","index":1}},{"name":"bar","value":{"kind":"Ix","index":2}}]}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__CONSTANT__x__ () Idv)\n(declare-fun smt__CONSTANT__y__ () Idv)\n(assert (! (not (and (= smt__CONSTANT__x__ smt__CONSTANT__y__) (= smt__CONSTANT__y__ smt__CONSTANT__x__))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_S_","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"CONSTANT_T_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":3}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}]}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]}]}},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_S_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Notmem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}},"visibility":"Hidden","time":"Always"},{"kind":"Defn","definition":{"kind":"Operator","name":"CONSTANT_EnabledWrapper_","body":{"kind":"Lambda","params":[{"name":"Unknown_Op_","shape":1}],"body":{"kind":"Internal","builtin":"FALSE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"CONSTANT_CdotWrapper_","body":{"kind":"Lambda","params":[{"name":"Unknown_Op_","shape":1}],"body":{"kind":"Internal","builtin":"FALSE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Notmem"},"args":[{"kind":"Ix","index":1},{"kind":"SetEnum","elements":[]}]}}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____SetEnum__0 () Idv)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__x Idv)) (! (not (smt__TLA____Mem smt__x smt__TLA____SetEnum__0)) :pattern ((smt__TLA____Mem smt__x smt__TLA____SetEnum__0)))) :named |EnumDefElim 0|))\n(assert (! (not (forall ((smt__CONSTANT__x__ Idv)) (not (smt__TLA____Mem smt__CONSTANT__x__ smt__TLA____SetEnum__0)))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_S_","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"CONSTANT_T_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":3}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}]}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]}]}},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"CONSTANT_S_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"CONSTANT_x_","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Notmem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}},"visibility":"Hidden","time":"Always"},{"kind":"Defn","definition":{"kind":"Operator","name":"CONSTANT_EnabledWrapper_","body":{"kind":"Lambda","params":[{"name":"Unknown_Op_","shape":1}],"body":{"kind":"Internal","builtin":"FALSE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"CONSTANT_CdotWrapper_","body":{"kind":"Lambda","params":[{"name":"Unknown_Op_","shape":1}],"body":{"kind":"Internal","builtin":"FALSE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neq"},"args":[{"kind":"String","value":"foo"},{"kind":"String","value":"bar"}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(declare-fun smt__TLA____StrLit__bar () Idv)\n(declare-fun smt__TLA____StrLit__foo () Idv)\n(declare-fun smt__TLA____StrSet () Idv)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (smt__TLA____Mem smt__TLA____StrLit__bar smt__TLA____StrSet) :named |StrLitIsstr bar|))\n(assert (! (smt__TLA____Mem smt__TLA____StrLit__foo smt__TLA____StrSet) :named |StrLitIsstr foo|))\n(assert (! (distinct smt__TLA____StrLit__bar smt__TLA____StrLit__foo) :named |StrLitDistinct bar foo|))\n(assert (! (not (distinct smt__TLA____StrLit__foo smt__TLA____StrLit__bar)) :named |Goal|))\n(check-sat)\n(exit)"]
]"###;

    // Sequents built to reach each path of the encoding.
    const CONSTRUCTED_CASES: &str = r###"[
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"x","shape":0,"level":"Constant","domainVisibility":"Visible","domain":{"kind":"Internal","builtin":"Nat"}}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____NatSet () Idv)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__x Idv)) (! (= (smt__TLA____Mem smt__x smt__TLA____NatSet) (and (smt__TLA____Mem smt__x smt__TLA____IntSet) (smt__TLA____IntLteq (smt__TLA____Cast__Int 0) smt__x))) :pattern ((smt__TLA____Mem smt__x smt__TLA____NatSet)))) :named |NatSetDef|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(assert (! (forall ((smt__x1 Int) (smt__x2 Int)) (! (= (smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2)) (<= smt__x1 smt__x2)) :pattern ((smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2))))) :named |Typing TIntLteq|))\n(declare-fun smt__S () Idv)\n(declare-fun smt__x () Idv)\n(assert (smt__TLA____Mem smt__x smt__TLA____NatSet))\n(assert (! (not (smt__TLA____Mem smt__x smt__S)) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"a","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"b","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gt"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(assert (! (forall ((smt__x1 Int) (smt__x2 Int)) (! (= (smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2)) (<= smt__x1 smt__x2)) :pattern ((smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2))))) :named |Typing TIntLteq|))\n(declare-fun smt__a () Idv)\n(declare-fun smt__b () Idv)\n(assert (! (not (and (smt__TLA____IntLteq smt__b smt__a) (distinct smt__b smt__a))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"a","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"b","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Lt"},"args":[{"kind":"Ix","index":2},{"kind":"Num","integer":"3","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Gteq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"007","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Notmem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(assert (! (forall ((smt__x1 Int) (smt__x2 Int)) (! (= (smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2)) (<= smt__x1 smt__x2)) :pattern ((smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2))))) :named |Typing TIntLteq|))\n(declare-fun smt__a () Idv)\n(declare-fun smt__b () Idv)\n(assert (! (not (and (and (smt__TLA____IntLteq smt__a (smt__TLA____Cast__Int 3)) (distinct smt__a (smt__TLA____Cast__Int 3))) (smt__TLA____IntLteq (smt__TLA____Cast__Int 7) smt__b) (not (smt__TLA____Mem smt__b smt__a)))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"a","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"0x1F","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":" 12 ","fraction":""}]}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(declare-fun smt__a () Idv)\n(assert (! (not (= (= smt__a (smt__TLA____Cast__Int 31)) (distinct smt__a (smt__TLA____Cast__Int 12)))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"a","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"\\h1F","fraction":""}]}},0,"SyntaxError: Failed to parse String to BigInt"],
[0,{"context":[{"kind":"Fresh","name":"a","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":"5"}]}},0,"TlaUnsupportedError: a real number"],
[0,{"context":[],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Num","integer":"123456789012345678901234567890","fraction":""},{"kind":"Num","integer":"-0","fraction":""}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(assert (! (not (= (smt__TLA____Cast__Int 123456789012345678901234567890) (smt__TLA____Cast__Int 0))) :named |Goal|))\n(check-sat)\n(exit)"],
[3,{"context":[{"kind":"Fresh","name":"a","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Case","arms":[{"condition":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]},"body":{"kind":"Num","integer":"2","fraction":""}},{"condition":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"2","fraction":""}]},"body":{"kind":"Num","integer":"3","fraction":""}}]},{"kind":"Num","integer":"4","fraction":""}]}},4,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Anon__incomplete__case__error__4 () Idv)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(declare-fun smt__a () Idv)\n(assert (! (not (= (ite (= smt__a (smt__TLA____Cast__Int 1)) (smt__TLA____Cast__Int 2) (ite (= smt__a (smt__TLA____Cast__Int 2)) (smt__TLA____Cast__Int 3) smt__TLA____Anon__incomplete__case__error__4)) (smt__TLA____Cast__Int 4))) :named |Goal|))\n(check-sat)\n(exit)"],
[3,{"context":[{"kind":"Fresh","name":"a","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Case","arms":[{"condition":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]},"body":{"kind":"Num","integer":"2","fraction":""}}],"other":{"kind":"Num","integer":"5","fraction":""}},{"kind":"Num","integer":"4","fraction":""}]}},3,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(declare-fun smt__a () Idv)\n(assert (! (not (= (smt__TLA____Cast__Int (ite (= smt__a (smt__TLA____Cast__Int 1)) 2 5)) (smt__TLA____Cast__Int 4))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"a","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Case","arms":[{"condition":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]},"body":{"kind":"Internal","builtin":"TRUE"}}],"other":{"kind":"Internal","builtin":"FALSE"}}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(declare-fun smt__a () Idv)\n(assert (! (not (ite (= smt__a (smt__TLA____Cast__Int 1)) true false)) :named |Goal|))\n(check-sat)\n(exit)"],
[1,{"context":[{"kind":"Fresh","name":"a","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Case","arms":[{"condition":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]},"body":{"kind":"Internal","builtin":"TRUE"}},{"condition":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cup"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]}]},"body":{"kind":"String","value":"s"}}]}},2,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Anon__incomplete__case__error__2 () Idv)\n(declare-fun smt__TLA____BoolSet () Idv)\n(declare-fun smt__TLA____Cast__Bool (Bool) Idv)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____Cup (Idv Idv) Idv)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(declare-fun smt__TLA____StrLit__s () Idv)\n(declare-fun smt__TLA____StrSet () Idv)\n(declare-fun smt__TLA____Tt__Idv () Idv)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv)) (! (= (smt__TLA____Mem smt__x (smt__TLA____Cup smt__a smt__b)) (or (smt__TLA____Mem smt__x smt__a) (smt__TLA____Mem smt__x smt__b))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____Cup smt__a smt__b))) :pattern ((smt__TLA____Mem smt__x smt__a) (smt__TLA____Cup smt__a smt__b)) :pattern ((smt__TLA____Mem smt__x smt__b) (smt__TLA____Cup smt__a smt__b)))) :named |CupDef|))\n(assert (! (smt__TLA____Mem smt__TLA____StrLit__s smt__TLA____StrSet) :named |StrLitIsstr s|))\n(assert (! (and (= (smt__TLA____Cast__Bool true) smt__TLA____Tt__Idv) (distinct (smt__TLA____Cast__Bool false) smt__TLA____Tt__Idv)) :named |CastInjAlt Bool|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Bool)) (! (smt__TLA____Mem (smt__TLA____Cast__Bool smt__z) smt__TLA____BoolSet) :pattern ((smt__TLA____Cast__Bool smt__z)))) :named |TypeGuardIntro Bool|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____BoolSet) (or (= smt__x (smt__TLA____Cast__Bool true)) (= smt__x (smt__TLA____Cast__Bool false)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____BoolSet)))) :named |TypeGuardElim Bool|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(declare-fun smt__a () Idv)\n(assert (! (not (= (ite (= smt__a (smt__TLA____Cast__Int 1)) (smt__TLA____Cast__Bool true) (ite (smt__TLA____Mem smt__a (smt__TLA____Cup smt__a smt__a)) smt__TLA____StrLit__s smt__TLA____Anon__incomplete__case__error__2)) smt__TLA____Tt__Idv)) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"a","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"If","condition":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cup"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]},{"kind":"Ix","index":1}]},"consequent":{"kind":"Num","integer":"1","fraction":""},"alternative":{"kind":"Num","integer":"2","fraction":""}},{"kind":"Num","integer":"1","fraction":""}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____Cup (Idv Idv) Idv)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(declare-fun smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv)) (! (= (smt__TLA____Mem smt__x (smt__TLA____Cup smt__a smt__b)) (or (smt__TLA____Mem smt__x smt__a) (smt__TLA____Mem smt__x smt__b))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____Cup smt__a smt__b))) :pattern ((smt__TLA____Mem smt__x smt__a) (smt__TLA____Cup smt__a smt__b)) :pattern ((smt__TLA____Mem smt__x smt__b) (smt__TLA____Cup smt__a smt__b)))) :named |CupDef|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (= (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y) (= smt__x smt__y)) :pattern ((smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y)))) :named |ExtTrigEqDef Set$Idv$|))\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (smt__TLA____SetExtTrigger smt__x smt__y) :pattern ((smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y)))) :named |ExtTrigEqTrigger Idv|))\n(declare-fun smt__a () Idv)\n(assert (! (not (= (smt__TLA____Cast__Int (ite (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____Cup smt__a smt__a) smt__a) 1 2)) (smt__TLA____Cast__Int 1))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"a","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"If","condition":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]},"consequent":{"kind":"Internal","builtin":"TRUE"},"alternative":{"kind":"Ix","index":1}}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____BoolSet () Idv)\n(declare-fun smt__TLA____Cast__Bool (Bool) Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(declare-fun smt__TLA____Tt__Idv () Idv)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (and (= (smt__TLA____Cast__Bool true) smt__TLA____Tt__Idv) (distinct (smt__TLA____Cast__Bool false) smt__TLA____Tt__Idv)) :named |CastInjAlt Bool|))\n(assert (! (forall ((smt__z Bool)) (! (smt__TLA____Mem (smt__TLA____Cast__Bool smt__z) smt__TLA____BoolSet) :pattern ((smt__TLA____Cast__Bool smt__z)))) :named |TypeGuardIntro Bool|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____BoolSet) (or (= smt__x (smt__TLA____Cast__Bool true)) (= smt__x (smt__TLA____Cast__Bool false)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____BoolSet)))) :named |TypeGuardElim Bool|))\n(declare-fun smt__a () Idv)\n(assert (! (not (= (ite (= smt__a smt__a) (smt__TLA____Cast__Bool true) smt__a) smt__TLA____Tt__Idv)) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"a","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"b","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Record","fields":[{"name":"y","value":{"kind":"Ix","index":1}},{"name":"x","value":{"kind":"Ix","index":2}}]},{"kind":"Record","fields":[{"name":"x","value":{"kind":"Ix","index":1}},{"name":"y","value":{"kind":"Ix","index":2}}]}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__a () Idv)\n(declare-fun smt__b () Idv)\n(assert (! (not (and (= smt__b smt__a) (= smt__a smt__b))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"a","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Record","fields":[{"name":"b","value":{"kind":"Ix","index":1}},{"name":"a","value":{"kind":"Record","fields":[{"name":"d","value":{"kind":"Ix","index":1}},{"name":"c","value":{"kind":"Ix","index":1}}]}}]},{"kind":"Rect","fields":[{"name":"b","value":{"kind":"Internal","builtin":"Nat"}},{"name":"a","value":{"kind":"Internal","builtin":"BOOLEAN"}}]}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____BoolSet () Idv)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____FunApp (Idv Idv) Idv)\n(declare-fun smt__TLA____FunDom (Idv) Idv)\n(declare-fun smt__TLA____FunIsafcn (Idv) Bool)\n(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____NatSet () Idv)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____RecordSet__a__b (Idv Idv) Idv)\n(declare-fun smt__TLA____Record__a__b (Idv Idv) Idv)\n(declare-fun smt__TLA____Record__d__c (Idv Idv) Idv)\n(declare-fun smt__TLA____SetEnum__2 (Idv Idv) Idv)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(declare-fun smt__TLA____StrLit__a () Idv)\n(declare-fun smt__TLA____StrLit__b () Idv)\n(declare-fun smt__TLA____StrLit__c () Idv)\n(declare-fun smt__TLA____StrLit__d () Idv)\n(declare-fun smt__TLA____StrSet () Idv)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__x Idv)) (! (= (smt__TLA____Mem smt__x smt__TLA____NatSet) (and (smt__TLA____Mem smt__x smt__TLA____IntSet) (smt__TLA____IntLteq (smt__TLA____Cast__Int 0) smt__x))) :pattern ((smt__TLA____Mem smt__x smt__TLA____NatSet)))) :named |NatSetDef|))\n(assert (! (forall ((smt__f Idv) (smt__g Idv)) (! (=> (and (smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g) (= (smt__TLA____FunDom smt__f) (smt__TLA____FunDom smt__g)) (forall ((smt__x Idv)) (=> (smt__TLA____Mem smt__x (smt__TLA____FunDom smt__f)) (= (smt__TLA____FunApp smt__f smt__x) (smt__TLA____FunApp smt__g smt__x))))) (= smt__f smt__g)) :pattern ((smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g)))) :named |FunExt|))\n(assert (! (forall ((smt__a1 Idv) (smt__a2 Idv)) (! (and (smt__TLA____Mem smt__a1 (smt__TLA____SetEnum__2 smt__a1 smt__a2)) (smt__TLA____Mem smt__a2 (smt__TLA____SetEnum__2 smt__a1 smt__a2))) :pattern ((smt__TLA____SetEnum__2 smt__a1 smt__a2)))) :named |EnumDefIntro 2|))\n(assert (! (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__x Idv)) (! (=> (smt__TLA____Mem smt__x (smt__TLA____SetEnum__2 smt__a1 smt__a2)) (or (= smt__x smt__a1) (= smt__x smt__a2))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____SetEnum__2 smt__a1 smt__a2))))) :named |EnumDefElim 2|))\n(assert (! (smt__TLA____Mem smt__TLA____StrLit__a smt__TLA____StrSet) :named |StrLitIsstr a|))\n(assert (! (smt__TLA____Mem smt__TLA____StrLit__b smt__TLA____StrSet) :named |StrLitIsstr b|))\n(assert (! (smt__TLA____Mem smt__TLA____StrLit__c smt__TLA____StrSet) :named |StrLitIsstr c|))\n(assert (! (smt__TLA____Mem smt__TLA____StrLit__d smt__TLA____StrSet) :named |StrLitIsstr d|))\n(assert (! (distinct smt__TLA____StrLit__b smt__TLA____StrLit__a) :named |StrLitDistinct b a|))\n(assert (! (distinct smt__TLA____StrLit__c smt__TLA____StrLit__a) :named |StrLitDistinct c a|))\n(assert (! (distinct smt__TLA____StrLit__c smt__TLA____StrLit__b) :named |StrLitDistinct c b|))\n(assert (! (distinct smt__TLA____StrLit__d smt__TLA____StrLit__a) :named |StrLitDistinct d a|))\n(assert (! (distinct smt__TLA____StrLit__d smt__TLA____StrLit__b) :named |StrLitDistinct d b|))\n(assert (! (distinct smt__TLA____StrLit__d smt__TLA____StrLit__c) :named |StrLitDistinct d c|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv)) (! (smt__TLA____FunIsafcn (smt__TLA____Record__a__b smt__x1 smt__x2)) :pattern ((smt__TLA____Record__a__b smt__x1 smt__x2)))) :named |RecIsafcn a b|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv)) (! (smt__TLA____FunIsafcn (smt__TLA____Record__d__c smt__x1 smt__x2)) :pattern ((smt__TLA____Record__d__c smt__x1 smt__x2)))) :named |RecIsafcn d c|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv)) (! (= (smt__TLA____FunDom (smt__TLA____Record__a__b smt__x1 smt__x2)) (smt__TLA____SetEnum__2 smt__TLA____StrLit__a smt__TLA____StrLit__b)) :pattern ((smt__TLA____Record__a__b smt__x1 smt__x2)))) :named |RecDomDef a b|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv)) (! (= (smt__TLA____FunDom (smt__TLA____Record__d__c smt__x1 smt__x2)) (smt__TLA____SetEnum__2 smt__TLA____StrLit__d smt__TLA____StrLit__c)) :pattern ((smt__TLA____Record__d__c smt__x1 smt__x2)))) :named |RecDomDef d c|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv)) (! (and (= (smt__TLA____FunApp (smt__TLA____Record__a__b smt__x1 smt__x2) smt__TLA____StrLit__a) smt__x1) (= (smt__TLA____FunApp (smt__TLA____Record__a__b smt__x1 smt__x2) smt__TLA____StrLit__b) smt__x2)) :pattern ((smt__TLA____Record__a__b smt__x1 smt__x2)))) :named |RecAppDef a b|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv)) (! (and (= (smt__TLA____FunApp (smt__TLA____Record__d__c smt__x1 smt__x2) smt__TLA____StrLit__d) smt__x1) (= (smt__TLA____FunApp (smt__TLA____Record__d__c smt__x1 smt__x2) smt__TLA____StrLit__c) smt__x2)) :pattern ((smt__TLA____Record__d__c smt__x1 smt__x2)))) :named |RecAppDef d c|))\n(assert (! (forall ((smt__s1 Idv) (smt__s2 Idv) (smt__x1 Idv) (smt__x2 Idv)) (! (=> (and (smt__TLA____Mem smt__x1 smt__s1) (smt__TLA____Mem smt__x2 smt__s2)) (smt__TLA____Mem (smt__TLA____Record__a__b smt__x1 smt__x2) (smt__TLA____RecordSet__a__b smt__s1 smt__s2))) :pattern ((smt__TLA____Record__a__b smt__x1 smt__x2) (smt__TLA____RecordSet__a__b smt__s1 smt__s2)))) :named |RecSetIntro a b|))\n(assert (! (forall ((smt__s1 Idv) (smt__s2 Idv) (smt__r Idv)) (! (=> (smt__TLA____Mem smt__r (smt__TLA____RecordSet__a__b smt__s1 smt__s2)) (and (= smt__r (smt__TLA____Record__a__b (smt__TLA____FunApp smt__r smt__TLA____StrLit__a) (smt__TLA____FunApp smt__r smt__TLA____StrLit__b))) (smt__TLA____Mem (smt__TLA____FunApp smt__r smt__TLA____StrLit__a) smt__s1) (smt__TLA____Mem (smt__TLA____FunApp smt__r smt__TLA____StrLit__b) smt__s2))) :pattern ((smt__TLA____Mem smt__r (smt__TLA____RecordSet__a__b smt__s1 smt__s2))))) :named |RecSetElim a b|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(assert (! (forall ((smt__x1 Int) (smt__x2 Int)) (! (= (smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2)) (<= smt__x1 smt__x2)) :pattern ((smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2))))) :named |Typing TIntLteq|))\n(declare-fun smt__a () Idv)\n(assert (! (not (smt__TLA____Mem (smt__TLA____Record__a__b (smt__TLA____Record__d__c smt__a smt__a) smt__a) (smt__TLA____RecordSet__a__b smt__TLA____BoolSet smt__TLA____NatSet))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"a","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Record","fields":[{"name":"x","value":{"kind":"Ix","index":1}}]},{"kind":"Record","fields":[{"name":"y","value":{"kind":"Ix","index":1}}]}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____FunApp (Idv Idv) Idv)\n(declare-fun smt__TLA____FunDom (Idv) Idv)\n(declare-fun smt__TLA____FunIsafcn (Idv) Bool)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____Record__x (Idv) Idv)\n(declare-fun smt__TLA____Record__y (Idv) Idv)\n(declare-fun smt__TLA____SetEnum__1 (Idv) Idv)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(declare-fun smt__TLA____StrLit__x () Idv)\n(declare-fun smt__TLA____StrLit__y () Idv)\n(declare-fun smt__TLA____StrSet () Idv)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__f Idv) (smt__g Idv)) (! (=> (and (smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g) (= (smt__TLA____FunDom smt__f) (smt__TLA____FunDom smt__g)) (forall ((smt__x Idv)) (=> (smt__TLA____Mem smt__x (smt__TLA____FunDom smt__f)) (= (smt__TLA____FunApp smt__f smt__x) (smt__TLA____FunApp smt__g smt__x))))) (= smt__f smt__g)) :pattern ((smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g)))) :named |FunExt|))\n(assert (! (forall ((smt__a1 Idv)) (! (smt__TLA____Mem smt__a1 (smt__TLA____SetEnum__1 smt__a1)) :pattern ((smt__TLA____SetEnum__1 smt__a1)))) :named |EnumDefIntro 1|))\n(assert (! (forall ((smt__a1 Idv) (smt__x Idv)) (! (=> (smt__TLA____Mem smt__x (smt__TLA____SetEnum__1 smt__a1)) (= smt__x smt__a1)) :pattern ((smt__TLA____Mem smt__x (smt__TLA____SetEnum__1 smt__a1))))) :named |EnumDefElim 1|))\n(assert (! (smt__TLA____Mem smt__TLA____StrLit__x smt__TLA____StrSet) :named |StrLitIsstr x|))\n(assert (! (smt__TLA____Mem smt__TLA____StrLit__y smt__TLA____StrSet) :named |StrLitIsstr y|))\n(assert (! (distinct smt__TLA____StrLit__y smt__TLA____StrLit__x) :named |StrLitDistinct y x|))\n(assert (! (forall ((smt__x1 Idv)) (! (smt__TLA____FunIsafcn (smt__TLA____Record__x smt__x1)) :pattern ((smt__TLA____Record__x smt__x1)))) :named |RecIsafcn x|))\n(assert (! (forall ((smt__x1 Idv)) (! (smt__TLA____FunIsafcn (smt__TLA____Record__y smt__x1)) :pattern ((smt__TLA____Record__y smt__x1)))) :named |RecIsafcn y|))\n(assert (! (forall ((smt__x1 Idv)) (! (= (smt__TLA____FunDom (smt__TLA____Record__x smt__x1)) (smt__TLA____SetEnum__1 smt__TLA____StrLit__x)) :pattern ((smt__TLA____Record__x smt__x1)))) :named |RecDomDef x|))\n(assert (! (forall ((smt__x1 Idv)) (! (= (smt__TLA____FunDom (smt__TLA____Record__y smt__x1)) (smt__TLA____SetEnum__1 smt__TLA____StrLit__y)) :pattern ((smt__TLA____Record__y smt__x1)))) :named |RecDomDef y|))\n(assert (! (forall ((smt__x1 Idv)) (! (= (smt__TLA____FunApp (smt__TLA____Record__x smt__x1) smt__TLA____StrLit__x) smt__x1) :pattern ((smt__TLA____Record__x smt__x1)))) :named |RecAppDef x|))\n(assert (! (forall ((smt__x1 Idv)) (! (= (smt__TLA____FunApp (smt__TLA____Record__y smt__x1) smt__TLA____StrLit__y) smt__x1) :pattern ((smt__TLA____Record__y smt__x1)))) :named |RecAppDef y|))\n(declare-fun smt__a () Idv)\n(assert (! (not (= (smt__TLA____Record__x smt__a) (smt__TLA____Record__y smt__a))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Flex","name":"v"},{"kind":"Fresh","name":"w","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"v#prime"},{"kind":"Ix","index":2}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__v () Idv)\n(declare-fun smt__v__prime () Idv)\n(declare-fun smt__w () Idv)\n(assert (! (not (= smt__v__prime smt__v)) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"w","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"v#prime"},{"kind":"Ix","index":1}]}},0,"TlaUnsupportedError: a primed declaration that isn't a variable"],
[0,{"context":[{"kind":"Fresh","name":"w","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Opaque","name":"Op"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"2","fraction":""}]},{"kind":"Opaque","name":"K"}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Anon__OPAQUE__K () Idv)\n(declare-fun smt__TLA____Anon__Op (Idv Idv) Idv)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(declare-fun smt__w () Idv)\n(assert (! (not (= (smt__TLA____Anon__Op smt__w (smt__TLA____Cast__Int 2)) smt__TLA____Anon__OPAQUE__K)) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"w","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Unprimable"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Unprimable"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]}]}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____BoolSet () Idv)\n(declare-fun smt__TLA____Cast__Bool (Bool) Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(declare-fun smt__TLA____Tt__Idv () Idv)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (and (= (smt__TLA____Cast__Bool true) smt__TLA____Tt__Idv) (distinct (smt__TLA____Cast__Bool false) smt__TLA____Tt__Idv)) :named |CastInjAlt Bool|))\n(assert (! (forall ((smt__z Bool)) (! (smt__TLA____Mem (smt__TLA____Cast__Bool smt__z) smt__TLA____BoolSet) :pattern ((smt__TLA____Cast__Bool smt__z)))) :named |TypeGuardIntro Bool|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____BoolSet) (or (= smt__x (smt__TLA____Cast__Bool true)) (= smt__x (smt__TLA____Cast__Bool false)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____BoolSet)))) :named |TypeGuardElim Bool|))\n(declare-fun smt__w () Idv)\n(assert (! (not (= smt__w (smt__TLA____Cast__Bool (= smt__w smt__w)))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"SelectSeq"},"args":[{"kind":"Ix","index":1},{"kind":"Lambda","params":[{"name":"e","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"SelectSeq"},"args":[{"kind":"Ix","index":1},{"kind":"Lambda","params":[{"name":"e","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}]}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Append (Idv Idv) Idv)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____FunApp (Idv Idv) Idv)\n(declare-fun smt__TLA____FunDom (Idv) Idv)\n(declare-fun smt__TLA____FunIsafcn (Idv) Bool)\n(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)\n(declare-fun smt__TLA____IntRange (Idv Idv) Idv)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Len (Idv) Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____NatSet () Idv)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____Seq (Idv) Idv)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(declare-fun smt__TLA____Tuple__0 () Idv)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__x Idv)) (! (= (smt__TLA____Mem smt__x smt__TLA____NatSet) (and (smt__TLA____Mem smt__x smt__TLA____IntSet) (smt__TLA____IntLteq (smt__TLA____Cast__Int 0) smt__x))) :pattern ((smt__TLA____Mem smt__x smt__TLA____NatSet)))) :named |NatSetDef|))\n(assert (! (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv)) (! (= (smt__TLA____Mem smt__x (smt__TLA____IntRange smt__a smt__b)) (and (smt__TLA____Mem smt__x smt__TLA____IntSet) (smt__TLA____IntLteq smt__a smt__x) (smt__TLA____IntLteq smt__x smt__b))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____IntRange smt__a smt__b))))) :named |IntRangeDef|))\n(assert (! (forall ((smt__f Idv) (smt__g Idv)) (! (=> (and (smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g) (= (smt__TLA____FunDom smt__f) (smt__TLA____FunDom smt__g)) (forall ((smt__x Idv)) (=> (smt__TLA____Mem smt__x (smt__TLA____FunDom smt__f)) (= (smt__TLA____FunApp smt__f smt__x) (smt__TLA____FunApp smt__g smt__x))))) (= smt__f smt__g)) :pattern ((smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g)))) :named |FunExt|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv)) (! (=> (and (smt__TLA____FunIsafcn smt__s) (>= (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) 0) (forall ((smt__i Idv)) (= (smt__TLA____Mem smt__i (smt__TLA____FunDom smt__s)) (and (smt__TLA____Mem smt__i smt__TLA____IntSet) (<= 1 (smt__TLA____Proj__Int smt__i)) (<= (smt__TLA____Proj__Int smt__i) (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))))) (forall ((smt__i Int)) (=> (and (<= 1 smt__i) (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))) (smt__TLA____Mem (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)) smt__a)))) (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))))) :named |SeqSetIntro|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv)) (! (=> (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (and (smt__TLA____FunIsafcn smt__s) (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (= (smt__TLA____FunDom smt__s) (smt__TLA____IntRange (smt__TLA____Cast__Int 1) (smt__TLA____Len smt__s))))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))))) :named |SetSetElim1|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv) (smt__i Int)) (! (=> (and (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (<= 1 smt__i) (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))) (smt__TLA____Mem (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)) smt__a)) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i))))) :named |SetSetElim2|))\n(assert (! (forall ((smt__s Idv) (smt__z Int)) (=> (and (>= smt__z 0) (= (smt__TLA____FunDom smt__s) (smt__TLA____IntRange (smt__TLA____Cast__Int 1) (smt__TLA____Cast__Int smt__z)))) (= (smt__TLA____Len smt__s) (smt__TLA____Cast__Int smt__z)))) :named |SeqLenDef|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv) (smt__x Idv)) (! (=> (and (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (smt__TLA____Mem smt__x smt__a)) (smt__TLA____Mem (smt__TLA____Append smt__s smt__x) (smt__TLA____Seq smt__a))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (smt__TLA____Append smt__s smt__x)))) :named |SeqAppendTyping|))\n(assert (! (forall ((smt__s Idv) (smt__x Idv)) (! (=> (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (= (smt__TLA____Len (smt__TLA____Append smt__s smt__x)) (smt__TLA____Cast__Int (+ (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) 1)))) :pattern ((smt__TLA____Append smt__s smt__x)))) :named |SeqAppendLen|))\n(assert (! (forall ((smt__s Idv) (smt__x Idv) (smt__i Int)) (! (=> (and (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (<= 1 smt__i) (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))) (= (smt__TLA____FunApp (smt__TLA____Append smt__s smt__x) (smt__TLA____Cast__Int smt__i)) (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)))) :pattern ((smt__TLA____FunApp (smt__TLA____Append smt__s smt__x) (smt__TLA____Cast__Int smt__i))) :pattern ((smt__TLA____Append smt__s smt__x) (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i))))) :named |SeqAppendApp1|))\n(assert (! (forall ((smt__s Idv) (smt__x Idv)) (! (=> (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (= (smt__TLA____FunApp (smt__TLA____Append smt__s smt__x) (smt__TLA____Cast__Int (+ (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) 1))) smt__x)) :pattern ((smt__TLA____Append smt__s smt__x)))) :named |SeqAppendApp2|))\n(assert (! (smt__TLA____FunIsafcn smt__TLA____Tuple__0) :named |TupIsafcn 0|))\n(assert (! (forall ((smt__a Idv)) (! (smt__TLA____Mem smt__TLA____Tuple__0 (smt__TLA____Seq smt__a)) :pattern (smt__TLA____Tuple__0))) :named |SeqTupTyping 0|))\n(assert (! (= (smt__TLA____Len smt__TLA____Tuple__0) (smt__TLA____Cast__Int 0)) :named |SeqTupLen 0|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(assert (! (forall ((smt__x1 Int) (smt__x2 Int)) (! (= (smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2)) (<= smt__x1 smt__x2)) :pattern ((smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2))))) :named |Typing TIntLteq|))\n(declare-fun smt__s () Idv)\n(declare-fun smt__TLA____SelectSeq__flatnd__1 (Idv) Idv)\n(assert (! (forall ((smt__a Idv) (smt__s_1 Idv)) (! (=> (smt__TLA____Mem smt__s_1 (smt__TLA____Seq smt__a)) (smt__TLA____Mem (smt__TLA____SelectSeq__flatnd__1 smt__s_1) (smt__TLA____Seq smt__a))) :pattern ((smt__TLA____Mem smt__s_1 (smt__TLA____Seq smt__a)) (smt__TLA____SelectSeq__flatnd__1 smt__s_1)))) :named |SeqSelectseqTyping TLA__SelectSeq_flatnd_1|))\n(assert (! (forall ((smt__s_1 Idv)) (! (=> (smt__TLA____Mem (smt__TLA____Len smt__s_1) smt__TLA____NatSet) (<= (smt__TLA____Proj__Int (smt__TLA____Len (smt__TLA____SelectSeq__flatnd__1 smt__s_1))) (smt__TLA____Proj__Int (smt__TLA____Len smt__s_1)))) :pattern ((smt__TLA____SelectSeq__flatnd__1 smt__s_1)))) :named |SeqSelectseqLen TLA__SelectSeq_flatnd_1|))\n(assert (! (= (smt__TLA____SelectSeq__flatnd__1 smt__TLA____Tuple__0) smt__TLA____Tuple__0) :named |SeqSelectseqNil TLA__SelectSeq_flatnd_1|))\n(assert (! (forall ((smt__s_1 Idv) (smt__x Idv)) (! (=> (smt__TLA____Mem smt__x (smt__TLA____FunDom (smt__TLA____SelectSeq__flatnd__1 smt__s_1))) (smt__TLA____Mem (smt__TLA____FunApp (smt__TLA____SelectSeq__flatnd__1 smt__s_1) smt__x) smt__s)) :pattern ((smt__TLA____FunApp (smt__TLA____SelectSeq__flatnd__1 smt__s_1) smt__x)))) :named |SeqSelectseqApp TLA__SelectSeq_flatnd_1|))\n(assert (! (forall ((smt__s_1 Idv) (smt__x Idv)) (! (and (=> (smt__TLA____Mem smt__x smt__s) (= (smt__TLA____SelectSeq__flatnd__1 (smt__TLA____Append smt__s_1 smt__x)) (smt__TLA____Append (smt__TLA____SelectSeq__flatnd__1 smt__s_1) smt__x))) (=> (not (smt__TLA____Mem smt__x smt__s)) (= (smt__TLA____SelectSeq__flatnd__1 (smt__TLA____Append smt__s_1 smt__x)) (smt__TLA____SelectSeq__flatnd__1 smt__s_1)))) :pattern ((smt__TLA____SelectSeq__flatnd__1 (smt__TLA____Append smt__s_1 smt__x))))) :named |SeqSelectseqAppend TLA__SelectSeq_flatnd_1|))\n(assert (! (not (= (smt__TLA____SelectSeq__flatnd__1 smt__s) (smt__TLA____SelectSeq__flatnd__1 smt__s))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"T","shape":1,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"SelectSeq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]},{"kind":"Ix","index":2}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Append (Idv Idv) Idv)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____FunApp (Idv Idv) Idv)\n(declare-fun smt__TLA____FunDom (Idv) Idv)\n(declare-fun smt__TLA____FunIsafcn (Idv) Bool)\n(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)\n(declare-fun smt__TLA____IntRange (Idv Idv) Idv)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Len (Idv) Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____NatSet () Idv)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____Seq (Idv) Idv)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(declare-fun smt__TLA____Tt__Idv () Idv)\n(declare-fun smt__TLA____Tuple__0 () Idv)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__x Idv)) (! (= (smt__TLA____Mem smt__x smt__TLA____NatSet) (and (smt__TLA____Mem smt__x smt__TLA____IntSet) (smt__TLA____IntLteq (smt__TLA____Cast__Int 0) smt__x))) :pattern ((smt__TLA____Mem smt__x smt__TLA____NatSet)))) :named |NatSetDef|))\n(assert (! (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv)) (! (= (smt__TLA____Mem smt__x (smt__TLA____IntRange smt__a smt__b)) (and (smt__TLA____Mem smt__x smt__TLA____IntSet) (smt__TLA____IntLteq smt__a smt__x) (smt__TLA____IntLteq smt__x smt__b))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____IntRange smt__a smt__b))))) :named |IntRangeDef|))\n(assert (! (forall ((smt__f Idv) (smt__g Idv)) (! (=> (and (smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g) (= (smt__TLA____FunDom smt__f) (smt__TLA____FunDom smt__g)) (forall ((smt__x Idv)) (=> (smt__TLA____Mem smt__x (smt__TLA____FunDom smt__f)) (= (smt__TLA____FunApp smt__f smt__x) (smt__TLA____FunApp smt__g smt__x))))) (= smt__f smt__g)) :pattern ((smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g)))) :named |FunExt|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv)) (! (=> (and (smt__TLA____FunIsafcn smt__s) (>= (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) 0) (forall ((smt__i Idv)) (= (smt__TLA____Mem smt__i (smt__TLA____FunDom smt__s)) (and (smt__TLA____Mem smt__i smt__TLA____IntSet) (<= 1 (smt__TLA____Proj__Int smt__i)) (<= (smt__TLA____Proj__Int smt__i) (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))))) (forall ((smt__i Int)) (=> (and (<= 1 smt__i) (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))) (smt__TLA____Mem (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)) smt__a)))) (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))))) :named |SeqSetIntro|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv)) (! (=> (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (and (smt__TLA____FunIsafcn smt__s) (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (= (smt__TLA____FunDom smt__s) (smt__TLA____IntRange (smt__TLA____Cast__Int 1) (smt__TLA____Len smt__s))))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))))) :named |SetSetElim1|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv) (smt__i Int)) (! (=> (and (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (<= 1 smt__i) (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))) (smt__TLA____Mem (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)) smt__a)) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i))))) :named |SetSetElim2|))\n(assert (! (forall ((smt__s Idv) (smt__z Int)) (=> (and (>= smt__z 0) (= (smt__TLA____FunDom smt__s) (smt__TLA____IntRange (smt__TLA____Cast__Int 1) (smt__TLA____Cast__Int smt__z)))) (= (smt__TLA____Len smt__s) (smt__TLA____Cast__Int smt__z)))) :named |SeqLenDef|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv) (smt__x Idv)) (! (=> (and (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (smt__TLA____Mem smt__x smt__a)) (smt__TLA____Mem (smt__TLA____Append smt__s smt__x) (smt__TLA____Seq smt__a))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (smt__TLA____Append smt__s smt__x)))) :named |SeqAppendTyping|))\n(assert (! (forall ((smt__s Idv) (smt__x Idv)) (! (=> (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (= (smt__TLA____Len (smt__TLA____Append smt__s smt__x)) (smt__TLA____Cast__Int (+ (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) 1)))) :pattern ((smt__TLA____Append smt__s smt__x)))) :named |SeqAppendLen|))\n(assert (! (forall ((smt__s Idv) (smt__x Idv) (smt__i Int)) (! (=> (and (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (<= 1 smt__i) (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))) (= (smt__TLA____FunApp (smt__TLA____Append smt__s smt__x) (smt__TLA____Cast__Int smt__i)) (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)))) :pattern ((smt__TLA____FunApp (smt__TLA____Append smt__s smt__x) (smt__TLA____Cast__Int smt__i))) :pattern ((smt__TLA____Append smt__s smt__x) (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i))))) :named |SeqAppendApp1|))\n(assert (! (forall ((smt__s Idv) (smt__x Idv)) (! (=> (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (= (smt__TLA____FunApp (smt__TLA____Append smt__s smt__x) (smt__TLA____Cast__Int (+ (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) 1))) smt__x)) :pattern ((smt__TLA____Append smt__s smt__x)))) :named |SeqAppendApp2|))\n(assert (! (smt__TLA____FunIsafcn smt__TLA____Tuple__0) :named |TupIsafcn 0|))\n(assert (! (forall ((smt__a Idv)) (! (smt__TLA____Mem smt__TLA____Tuple__0 (smt__TLA____Seq smt__a)) :pattern (smt__TLA____Tuple__0))) :named |SeqTupTyping 0|))\n(assert (! (= (smt__TLA____Len smt__TLA____Tuple__0) (smt__TLA____Cast__Int 0)) :named |SeqTupLen 0|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(assert (! (forall ((smt__x1 Int) (smt__x2 Int)) (! (= (smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2)) (<= smt__x1 smt__x2)) :pattern ((smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2))))) :named |Typing TIntLteq|))\n(declare-fun smt__s () Idv)\n(declare-fun smt__T (Idv) Idv)\n(declare-fun smt__TLA____SelectSeq__flatnd__1 (Idv) Idv)\n(assert (! (forall ((smt__a Idv) (smt__s_1 Idv)) (! (=> (smt__TLA____Mem smt__s_1 (smt__TLA____Seq smt__a)) (smt__TLA____Mem (smt__TLA____SelectSeq__flatnd__1 smt__s_1) (smt__TLA____Seq smt__a))) :pattern ((smt__TLA____Mem smt__s_1 (smt__TLA____Seq smt__a)) (smt__TLA____SelectSeq__flatnd__1 smt__s_1)))) :named |SeqSelectseqTyping TLA__SelectSeq_flatnd_1|))\n(assert (! (forall ((smt__s_1 Idv)) (! (=> (smt__TLA____Mem (smt__TLA____Len smt__s_1) smt__TLA____NatSet) (<= (smt__TLA____Proj__Int (smt__TLA____Len (smt__TLA____SelectSeq__flatnd__1 smt__s_1))) (smt__TLA____Proj__Int (smt__TLA____Len smt__s_1)))) :pattern ((smt__TLA____SelectSeq__flatnd__1 smt__s_1)))) :named |SeqSelectseqLen TLA__SelectSeq_flatnd_1|))\n(assert (! (= (smt__TLA____SelectSeq__flatnd__1 smt__TLA____Tuple__0) smt__TLA____Tuple__0) :named |SeqSelectseqNil TLA__SelectSeq_flatnd_1|))\n(assert (! (forall ((smt__s_1 Idv) (smt__x Idv)) (! (=> (smt__TLA____Mem smt__x (smt__TLA____FunDom (smt__TLA____SelectSeq__flatnd__1 smt__s_1))) (= (smt__T (smt__TLA____FunApp (smt__TLA____SelectSeq__flatnd__1 smt__s_1) smt__x)) smt__TLA____Tt__Idv)) :pattern ((smt__TLA____FunApp (smt__TLA____SelectSeq__flatnd__1 smt__s_1) smt__x)))) :named |SeqSelectseqApp TLA__SelectSeq_flatnd_1|))\n(assert (! (forall ((smt__s_1 Idv) (smt__x Idv)) (! (and (=> (= (smt__T smt__x) smt__TLA____Tt__Idv) (= (smt__TLA____SelectSeq__flatnd__1 (smt__TLA____Append smt__s_1 smt__x)) (smt__TLA____Append (smt__TLA____SelectSeq__flatnd__1 smt__s_1) smt__x))) (=> (not (= (smt__T smt__x) smt__TLA____Tt__Idv)) (= (smt__TLA____SelectSeq__flatnd__1 (smt__TLA____Append smt__s_1 smt__x)) (smt__TLA____SelectSeq__flatnd__1 smt__s_1)))) :pattern ((smt__TLA____SelectSeq__flatnd__1 (smt__TLA____Append smt__s_1 smt__x))))) :named |SeqSelectseqAppend TLA__SelectSeq_flatnd_1|))\n(assert (! (not (= (smt__TLA____SelectSeq__flatnd__1 smt__s) smt__s)) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Defn","definition":{"kind":"Operator","name":"F","body":{"kind":"Lambda","params":[{"name":"P","shape":1},{"name":"y","shape":0}],"body":{"kind":"Internal","builtin":"TRUE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Lambda","params":[{"name":"z","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":3}]}},{"kind":"Ix","index":2}]},{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Lambda","params":[{"name":"q","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":3}]}},{"kind":"Ix","index":2}]}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____BoolSet () Idv)\n(declare-fun smt__TLA____Cast__Bool (Bool) Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(declare-fun smt__TLA____Tt__Idv () Idv)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (and (= (smt__TLA____Cast__Bool true) smt__TLA____Tt__Idv) (distinct (smt__TLA____Cast__Bool false) smt__TLA____Tt__Idv)) :named |CastInjAlt Bool|))\n(assert (! (forall ((smt__z Bool)) (! (smt__TLA____Mem (smt__TLA____Cast__Bool smt__z) smt__TLA____BoolSet) :pattern ((smt__TLA____Cast__Bool smt__z)))) :named |TypeGuardIntro Bool|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____BoolSet) (or (= smt__x (smt__TLA____Cast__Bool true)) (= smt__x (smt__TLA____Cast__Bool false)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____BoolSet)))) :named |TypeGuardElim Bool|))\n(declare-fun smt__s () Idv)\n(declare-fun smt__F__flatnd__1 (Idv) Idv)\n(assert (! (not (= (smt__F__flatnd__1 smt__s) (smt__F__flatnd__1 smt__s))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"G","shape":1,"level":"Constant","domainVisibility":"Visible"},{"kind":"Defn","definition":{"kind":"Operator","name":"F","body":{"kind":"Lambda","params":[{"name":"P","shape":1}],"body":{"kind":"Internal","builtin":"TRUE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":2}]},{"kind":"Ix","index":3}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__s () Idv)\n(declare-fun smt__G (Idv) Idv)\n(declare-fun smt__F__flatnd__1 () Idv)\n(assert (! (not (= smt__F__flatnd__1 smt__s)) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Defn","definition":{"kind":"Operator","name":"F","body":{"kind":"Lambda","params":[{"name":"P","shape":1}],"body":{"kind":"Internal","builtin":"TRUE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":2}]},{"kind":"Ix","index":2}]}},0,"TlaUnsupportedError: an operator argument that isn't a LAMBDA"],
[0,{"context":[{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Defn","definition":{"kind":"Operator","name":"F","body":{"kind":"Lambda","params":[{"name":"P","shape":1}],"body":{"kind":"Internal","builtin":"TRUE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Ix","index":2}]}},0,"TlaUnsupportedError: an operator argument that isn't a LAMBDA"],
[0,{"context":[{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Defn","definition":{"kind":"Operator","name":"F","body":{"kind":"Lambda","params":[{"name":"P","shape":1}],"body":{"kind":"Internal","builtin":"TRUE"}}},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[]},{"kind":"Ix","index":2}]}},0,"TlaUnsupportedError: an operator applied to the wrong number of arguments"],
[0,{"context":[{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"P","shape":1,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"y","shape":0,"level":"Constant","domainVisibility":"Visible","domain":{"kind":"Ix","index":2}},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Ix","index":2},"args":[{"kind":"Ix","index":1}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"z","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"SetSt","name":"u","domain":{"kind":"Ix","index":4},"body":{"kind":"Apply","operator":{"kind":"Ix","index":4},"args":[{"kind":"Ix","index":1}]}},{"kind":"Ix","index":1}]}}}},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":2}]}},0,"TlaUnsupportedError: an operator applied to the wrong number of arguments"],
[0,{"context":[{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"P","shape":1,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":2}]}}}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__s () Idv)\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"y","shape":0,"level":"Constant","domainVisibility":"Visible","domain":{"kind":"Ix","index":1}},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Internal","builtin":"FALSE"},"visibility":"Hidden","time":"Now"},{"kind":"Fresh","name":"z","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":4}]}}}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(declare-fun smt__s () Idv)\n(assert (! (not (forall ((smt__y Idv)) (=> (smt__TLA____Mem smt__y smt__s) (=> (smt__TLA____Mem smt__y smt__s) (forall ((smt__z Idv)) (= smt__z smt__y)))))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"y","shape":0,"level":"State","domainVisibility":"Visible"}],"active":{"kind":"Internal","builtin":"TRUE"}}}},0,"TlaUnsupportedError: a NEW declaration that isn't constant"],
[0,{"context":[{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Sequent","sequent":{"context":[{"kind":"Flex","name":"y"}],"active":{"kind":"Internal","builtin":"TRUE"}}}},0,"TlaUnsupportedError: a Flex in a nested ASSUME"],
[0,{"context":[{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Sequent","sequent":{"context":[{"kind":"Defn","definition":{"kind":"Operator","name":"D","body":{"kind":"Num","integer":"1","fraction":""}},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Internal","builtin":"TRUE"}}}},0,"TlaUnsupportedError: a Defn in a nested ASSUME"],
[0,{"context":[{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Num","integer":"1","fraction":""}]}},0,"TlaUnsupportedError: an applied constant"],
[0,{"context":[{"kind":"Flex","name":"v"}],"active":{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Num","integer":"1","fraction":""}]}},0,"TlaUnsupportedError: an applied variable"],
[0,{"context":[{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":5},{"kind":"Ix","index":1}]}},0,"TlaUnsupportedError: a reference outside the obligation"],
[0,{"context":[{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":0},{"kind":"Ix","index":1}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__s () Idv)\n(assert (! (not (= smt__s smt__s)) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Now"}],"active":{"kind":"Ix","index":1}},0,"TlaUnsupportedError: a reference to a fact"],
[0,{"context":[{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Defn","definition":{"kind":"Operator","name":"D","body":{"kind":"Num","integer":"1","fraction":""}},"whereDefined":"User","visibility":"Visible","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}},0,"TlaUnsupportedError: an expanded definition"],
[0,{"context":[{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Defn","definition":{"kind":"Recursive","name":"R","shape":1},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":2}]},{"kind":"Ix","index":2}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__s () Idv)\n(declare-fun smt__CONSTANT__R__ (Idv) Idv)\n(assert (! (not (= (smt__CONSTANT__R__ smt__s) smt__s)) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Defn","definition":{"kind":"Bpragma","name":"Z","body":{"kind":"Internal","builtin":"TRUE"},"methods":[]},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":2}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__s () Idv)\n(assert (! (not (= smt__s smt__s)) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Defn","definition":{"kind":"Operator","name":"D","body":{"kind":"Lambda","params":[{"name":"p","shape":0},{"name":"q","shape":0}],"body":{"kind":"Num","integer":"1","fraction":""}}},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Num","integer":"1","fraction":""}]}},0,"TlaUnsupportedError: an operator applied to the wrong number of arguments"],
[0,{"context":[{"kind":"Defn","definition":{"kind":"Operator","name":"D","body":{"kind":"Num","integer":"1","fraction":""}},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(declare-fun smt__D () Idv)\n(assert (! (not (= smt__D (smt__TLA____Cast__Int 1))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"s","shape":0,"level":"Constant","domainVisibility":"Hidden","domain":{"kind":"Apply","operator":{"kind":"Internal","builtin":"SUBSET"},"args":[{"kind":"Internal","builtin":"Nat"}]}}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Subseteq"},"args":[{"kind":"Ix","index":1},{"kind":"Internal","builtin":"Int"}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(declare-fun smt__TLA____SubsetEq (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (=> (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (smt__TLA____SubsetEq smt__x smt__y)) :pattern ((smt__TLA____SubsetEq smt__x smt__y)))) :named |SubsetEqIntro|))\n(assert (! (forall ((smt__x Idv) (smt__y Idv) (smt__z Idv)) (! (=> (and (smt__TLA____SubsetEq smt__x smt__y) (smt__TLA____Mem smt__z smt__x)) (smt__TLA____Mem smt__z smt__y)) :pattern ((smt__TLA____SubsetEq smt__x smt__y) (smt__TLA____Mem smt__z smt__x)))) :named |SubsetEqElim|))\n(declare-fun smt__s () Idv)\n(assert (! (not (smt__TLA____SubsetEq smt__s smt__TLA____IntSet)) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"f","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"k","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Except","function":{"kind":"Ix","index":2},"specs":[{"trail":[{"kind":"Apply","expression":{"kind":"Fcn","bounds":[{"name":"i","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":2}}}],"body":{"kind":"Ix","index":1}}},{"kind":"Dot","field":"a"},{"kind":"Apply","expression":{"kind":"Ix","index":1}}],"value":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"At","isExcept":true},{"kind":"Num","integer":"1","fraction":""}]}},{"trail":[{"kind":"Dot","field":"b"}],"value":{"kind":"At","isExcept":true}}]},{"kind":"Ix","index":2}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____FunApp (Idv Idv) Idv)\n(declare-fun smt__TLA____FunDom (Idv) Idv)\n(declare-fun smt__TLA____FunExcept (Idv Idv Idv) Idv)\n(declare-fun smt__TLA____FunIsafcn (Idv) Bool)\n(declare-fun smt__TLA____IntPlus (Idv Idv) Idv)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(declare-fun smt__TLA____StrLit__a () Idv)\n(declare-fun smt__TLA____StrLit__b () Idv)\n(declare-fun smt__TLA____StrSet () Idv)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__f Idv) (smt__g Idv)) (! (=> (and (smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g) (= (smt__TLA____FunDom smt__f) (smt__TLA____FunDom smt__g)) (forall ((smt__x Idv)) (=> (smt__TLA____Mem smt__x (smt__TLA____FunDom smt__f)) (= (smt__TLA____FunApp smt__f smt__x) (smt__TLA____FunApp smt__g smt__x))))) (= smt__f smt__g)) :pattern ((smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g)))) :named |FunExt|))\n(assert (! (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv)) (! (smt__TLA____FunIsafcn (smt__TLA____FunExcept smt__f smt__x smt__y)) :pattern ((smt__TLA____FunExcept smt__f smt__x smt__y)))) :named |FunExceptIsafcn|))\n(assert (! (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv)) (! (= (smt__TLA____FunDom (smt__TLA____FunExcept smt__f smt__x smt__y)) (smt__TLA____FunDom smt__f)) :pattern ((smt__TLA____FunExcept smt__f smt__x smt__y)))) :named |FunExceptDomDef|))\n(assert (! (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv)) (! (=> (smt__TLA____Mem smt__x (smt__TLA____FunDom smt__f)) (= (smt__TLA____FunApp (smt__TLA____FunExcept smt__f smt__x smt__y) smt__x) smt__y)) :pattern ((smt__TLA____FunExcept smt__f smt__x smt__y)))) :named |FunExceptAppDef1|))\n(assert (! (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv) (smt__z Idv)) (! (=> (smt__TLA____Mem smt__z (smt__TLA____FunDom smt__f)) (and (=> (= smt__z smt__x) (= (smt__TLA____FunApp (smt__TLA____FunExcept smt__f smt__x smt__y) smt__z) smt__y)) (=> (distinct smt__z smt__x) (= (smt__TLA____FunApp (smt__TLA____FunExcept smt__f smt__x smt__y) smt__z) (smt__TLA____FunApp smt__f smt__z))))) :pattern ((smt__TLA____FunApp (smt__TLA____FunExcept smt__f smt__x smt__y) smt__z)) :pattern ((smt__TLA____FunExcept smt__f smt__x smt__y) (smt__TLA____FunApp smt__f smt__z)))) :named |FunExceptAppDef2|))\n(assert (! (smt__TLA____Mem smt__TLA____StrLit__a smt__TLA____StrSet) :named |StrLitIsstr a|))\n(assert (! (smt__TLA____Mem smt__TLA____StrLit__b smt__TLA____StrSet) :named |StrLitIsstr b|))\n(assert (! (distinct smt__TLA____StrLit__b smt__TLA____StrLit__a) :named |StrLitDistinct b a|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(assert (! (forall ((smt__x1 Int) (smt__x2 Int)) (! (= (smt__TLA____IntPlus (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2)) (smt__TLA____Cast__Int (+ smt__x1 smt__x2))) :pattern ((smt__TLA____IntPlus (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2))))) :named |Typing TIntPlus|))\n(declare-fun smt__f () Idv)\n(declare-fun smt__k () Idv)\n(declare-fun smt__TLA____FunFcn__flatnd__1 (Idv) Idv)\n(assert (! (forall ((smt__a Idv)) (! (smt__TLA____FunIsafcn (smt__TLA____FunFcn__flatnd__1 smt__a)) :pattern ((smt__TLA____FunFcn__flatnd__1 smt__a)))) :named |FunConstrIsafcn TLA__FunFcn_flatnd_1|))\n(assert (! (forall ((smt__a Idv)) (! (= (smt__TLA____FunDom (smt__TLA____FunFcn__flatnd__1 smt__a)) smt__a) :pattern ((smt__TLA____FunFcn__flatnd__1 smt__a)))) :named |FunDomDef TLA__FunFcn_flatnd_1|))\n(assert (! (forall ((smt__a Idv) (smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__a) (= (smt__TLA____FunApp (smt__TLA____FunFcn__flatnd__1 smt__a) smt__x) smt__x)) :pattern ((smt__TLA____FunApp (smt__TLA____FunFcn__flatnd__1 smt__a) smt__x)) :pattern ((smt__TLA____Mem smt__x smt__a) (smt__TLA____FunFcn__flatnd__1 smt__a)))) :named |FunAppDef TLA__FunFcn_flatnd_1|))\n(assert (! (not (= (smt__TLA____FunExcept (smt__TLA____FunExcept smt__f (smt__TLA____FunFcn__flatnd__1 smt__f) (smt__TLA____FunExcept (smt__TLA____FunApp smt__f (smt__TLA____FunFcn__flatnd__1 smt__f)) smt__TLA____StrLit__a (smt__TLA____FunExcept (smt__TLA____FunApp (smt__TLA____FunApp smt__f (smt__TLA____FunFcn__flatnd__1 smt__f)) smt__TLA____StrLit__a) smt__k (smt__TLA____IntPlus (smt__TLA____FunApp (smt__TLA____FunApp (smt__TLA____FunApp smt__f (smt__TLA____FunFcn__flatnd__1 smt__f)) smt__TLA____StrLit__a) smt__k) (smt__TLA____Cast__Int 1))))) smt__TLA____StrLit__b (smt__TLA____FunApp (smt__TLA____FunExcept smt__f (smt__TLA____FunFcn__flatnd__1 smt__f) (smt__TLA____FunExcept (smt__TLA____FunApp smt__f (smt__TLA____FunFcn__flatnd__1 smt__f)) smt__TLA____StrLit__a (smt__TLA____FunExcept (smt__TLA____FunApp (smt__TLA____FunApp smt__f (smt__TLA____FunFcn__flatnd__1 smt__f)) smt__TLA____StrLit__a) smt__k (smt__TLA____IntPlus (smt__TLA____FunApp (smt__TLA____FunApp (smt__TLA____FunApp smt__f (smt__TLA____FunFcn__flatnd__1 smt__f)) smt__TLA____StrLit__a) smt__k) (smt__TLA____Cast__Int 1))))) smt__TLA____StrLit__b)) smt__f)) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"f","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"At","isExcept":true},{"kind":"Ix","index":1}]}},0,"TlaUnsupportedError: @ outside EXCEPT"],
[0,{"context":[{"kind":"Fresh","name":"f","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Fcn","bounds":[{"name":"i","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":1}}},{"name":"j","level":"Constant","domain":{"kind":"Ditto"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}},{"kind":"Ix","index":2}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____FunApp (Idv Idv) Idv)\n(declare-fun smt__TLA____FunDom (Idv) Idv)\n(declare-fun smt__TLA____FunIsafcn (Idv) Bool)\n(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)\n(declare-fun smt__TLA____IntPlus (Idv Idv) Idv)\n(declare-fun smt__TLA____IntRange (Idv Idv) Idv)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Len (Idv) Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____NatSet () Idv)\n(declare-fun smt__TLA____Product__2 (Idv Idv) Idv)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____Seq (Idv) Idv)\n(declare-fun smt__TLA____SetEnum__2 (Idv Idv) Idv)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(declare-fun smt__TLA____Tuple__2 (Idv Idv) Idv)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__x Idv)) (! (= (smt__TLA____Mem smt__x smt__TLA____NatSet) (and (smt__TLA____Mem smt__x smt__TLA____IntSet) (smt__TLA____IntLteq (smt__TLA____Cast__Int 0) smt__x))) :pattern ((smt__TLA____Mem smt__x smt__TLA____NatSet)))) :named |NatSetDef|))\n(assert (! (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv)) (! (= (smt__TLA____Mem smt__x (smt__TLA____IntRange smt__a smt__b)) (and (smt__TLA____Mem smt__x smt__TLA____IntSet) (smt__TLA____IntLteq smt__a smt__x) (smt__TLA____IntLteq smt__x smt__b))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____IntRange smt__a smt__b))))) :named |IntRangeDef|))\n(assert (! (forall ((smt__f Idv) (smt__g Idv)) (! (=> (and (smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g) (= (smt__TLA____FunDom smt__f) (smt__TLA____FunDom smt__g)) (forall ((smt__x Idv)) (=> (smt__TLA____Mem smt__x (smt__TLA____FunDom smt__f)) (= (smt__TLA____FunApp smt__f smt__x) (smt__TLA____FunApp smt__g smt__x))))) (= smt__f smt__g)) :pattern ((smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g)))) :named |FunExt|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv)) (! (=> (and (smt__TLA____FunIsafcn smt__s) (>= (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) 0) (forall ((smt__i Idv)) (= (smt__TLA____Mem smt__i (smt__TLA____FunDom smt__s)) (and (smt__TLA____Mem smt__i smt__TLA____IntSet) (<= 1 (smt__TLA____Proj__Int smt__i)) (<= (smt__TLA____Proj__Int smt__i) (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))))) (forall ((smt__i Int)) (=> (and (<= 1 smt__i) (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))) (smt__TLA____Mem (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)) smt__a)))) (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))))) :named |SeqSetIntro|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv)) (! (=> (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (and (smt__TLA____FunIsafcn smt__s) (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (= (smt__TLA____FunDom smt__s) (smt__TLA____IntRange (smt__TLA____Cast__Int 1) (smt__TLA____Len smt__s))))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))))) :named |SetSetElim1|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv) (smt__i Int)) (! (=> (and (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (<= 1 smt__i) (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))) (smt__TLA____Mem (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)) smt__a)) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i))))) :named |SetSetElim2|))\n(assert (! (forall ((smt__s Idv) (smt__z Int)) (=> (and (>= smt__z 0) (= (smt__TLA____FunDom smt__s) (smt__TLA____IntRange (smt__TLA____Cast__Int 1) (smt__TLA____Cast__Int smt__z)))) (= (smt__TLA____Len smt__s) (smt__TLA____Cast__Int smt__z)))) :named |SeqLenDef|))\n(assert (! (forall ((smt__a1 Idv) (smt__a2 Idv)) (! (and (smt__TLA____Mem smt__a1 (smt__TLA____SetEnum__2 smt__a1 smt__a2)) (smt__TLA____Mem smt__a2 (smt__TLA____SetEnum__2 smt__a1 smt__a2))) :pattern ((smt__TLA____SetEnum__2 smt__a1 smt__a2)))) :named |EnumDefIntro 2|))\n(assert (! (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__x Idv)) (! (=> (smt__TLA____Mem smt__x (smt__TLA____SetEnum__2 smt__a1 smt__a2)) (or (= smt__x smt__a1) (= smt__x smt__a2))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____SetEnum__2 smt__a1 smt__a2))))) :named |EnumDefElim 2|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv)) (! (smt__TLA____FunIsafcn (smt__TLA____Tuple__2 smt__x1 smt__x2)) :pattern ((smt__TLA____Tuple__2 smt__x1 smt__x2)))) :named |TupIsafcn 2|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv)) (! (= (smt__TLA____FunDom (smt__TLA____Tuple__2 smt__x1 smt__x2)) (smt__TLA____SetEnum__2 (smt__TLA____Cast__Int 1) (smt__TLA____Cast__Int 2))) :pattern ((smt__TLA____Tuple__2 smt__x1 smt__x2)))) :named |TupDomDef 2|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv)) (! (and (= (smt__TLA____FunApp (smt__TLA____Tuple__2 smt__x1 smt__x2) (smt__TLA____Cast__Int 1)) smt__x1) (= (smt__TLA____FunApp (smt__TLA____Tuple__2 smt__x1 smt__x2) (smt__TLA____Cast__Int 2)) smt__x2)) :pattern ((smt__TLA____Tuple__2 smt__x1 smt__x2)))) :named |TupAppDef 2|))\n(assert (! (forall ((smt__s1 Idv) (smt__s2 Idv) (smt__x1 Idv) (smt__x2 Idv)) (! (=> (and (smt__TLA____Mem smt__x1 smt__s1) (smt__TLA____Mem smt__x2 smt__s2)) (smt__TLA____Mem (smt__TLA____Tuple__2 smt__x1 smt__x2) (smt__TLA____Product__2 smt__s1 smt__s2))) :pattern ((smt__TLA____Tuple__2 smt__x1 smt__x2) (smt__TLA____Product__2 smt__s1 smt__s2)))) :named |ProductIntro 2|))\n(assert (! (forall ((smt__s1 Idv) (smt__s2 Idv) (smt__t Idv)) (! (=> (smt__TLA____Mem smt__t (smt__TLA____Product__2 smt__s1 smt__s2)) (and (= smt__t (smt__TLA____Tuple__2 (smt__TLA____FunApp smt__t (smt__TLA____Cast__Int 1)) (smt__TLA____FunApp smt__t (smt__TLA____Cast__Int 2)))) (smt__TLA____Mem (smt__TLA____FunApp smt__t (smt__TLA____Cast__Int 1)) smt__s1) (smt__TLA____Mem (smt__TLA____FunApp smt__t (smt__TLA____Cast__Int 2)) smt__s2))) :pattern ((smt__TLA____Mem smt__t (smt__TLA____Product__2 smt__s1 smt__s2))))) :named |ProductElim 2|))\n(assert (! (forall ((smt__a Idv) (smt__x1 Idv) (smt__x2 Idv)) (! (=> (and (smt__TLA____Mem smt__x1 smt__a) (smt__TLA____Mem smt__x2 smt__a)) (smt__TLA____Mem (smt__TLA____Tuple__2 smt__x1 smt__x2) (smt__TLA____Seq smt__a))) :pattern ((smt__TLA____Mem smt__x1 smt__a) (smt__TLA____Mem smt__x2 smt__a) (smt__TLA____Tuple__2 smt__x1 smt__x2)))) :named |SeqTupTyping 2|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv)) (! (= (smt__TLA____Len (smt__TLA____Tuple__2 smt__x1 smt__x2)) (smt__TLA____Cast__Int 2)) :pattern ((smt__TLA____Tuple__2 smt__x1 smt__x2)))) :named |SeqTupLen 2|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(assert (! (forall ((smt__x1 Int) (smt__x2 Int)) (! (= (smt__TLA____IntPlus (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2)) (smt__TLA____Cast__Int (+ smt__x1 smt__x2))) :pattern ((smt__TLA____IntPlus (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2))))) :named |Typing TIntPlus|))\n(assert (! (forall ((smt__x1 Int) (smt__x2 Int)) (! (= (smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2)) (<= smt__x1 smt__x2)) :pattern ((smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2))))) :named |Typing TIntLteq|))\n(declare-fun smt__f () Idv)\n(declare-fun smt__S () Idv)\n(declare-fun smt__TLA____FunFcn__flatnd__1 (Idv) Idv)\n(assert (! (forall ((smt__a Idv)) (! (smt__TLA____FunIsafcn (smt__TLA____FunFcn__flatnd__1 smt__a)) :pattern ((smt__TLA____FunFcn__flatnd__1 smt__a)))) :named |FunConstrIsafcn TLA__FunFcn_flatnd_1|))\n(assert (! (forall ((smt__a Idv)) (! (= (smt__TLA____FunDom (smt__TLA____FunFcn__flatnd__1 smt__a)) smt__a) :pattern ((smt__TLA____FunFcn__flatnd__1 smt__a)))) :named |FunDomDef TLA__FunFcn_flatnd_1|))\n(assert (! (forall ((smt__a Idv) (smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__a) (= (smt__TLA____FunApp (smt__TLA____FunFcn__flatnd__1 smt__a) smt__x) (smt__TLA____IntPlus (smt__TLA____FunApp smt__x (smt__TLA____Cast__Int 2)) (smt__TLA____FunApp smt__x (smt__TLA____Cast__Int 1))))) :pattern ((smt__TLA____FunApp (smt__TLA____FunFcn__flatnd__1 smt__a) smt__x)) :pattern ((smt__TLA____Mem smt__x smt__a) (smt__TLA____FunFcn__flatnd__1 smt__a)))) :named |FunAppDef TLA__FunFcn_flatnd_1|))\n(assert (! (not (= (smt__TLA____FunFcn__flatnd__1 (smt__TLA____Product__2 smt__S smt__S)) smt__f)) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"f","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Fcn","bounds":[{"name":"i","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Ix","index":1}},{"kind":"Ix","index":2}]}},0,"TlaUnsupportedError: a function without a domain"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"SetOf","element":{"kind":"Tuple","elements":[{"kind":"Ix","index":1},{"kind":"Ix","index":2},{"kind":"Ix","index":3}]},"bounds":[{"name":"i","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":1}}},{"name":"j","level":"Constant","domain":{"kind":"Ditto"}}]},{"kind":"Product","factors":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____FunApp (Idv Idv) Idv)\n(declare-fun smt__TLA____FunDom (Idv) Idv)\n(declare-fun smt__TLA____FunIsafcn (Idv) Bool)\n(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)\n(declare-fun smt__TLA____IntRange (Idv Idv) Idv)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____IsSetOf (Idv) Bool)\n(declare-fun smt__TLA____Len (Idv) Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____NatSet () Idv)\n(declare-fun smt__TLA____Product__2 (Idv Idv) Idv)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____Seq (Idv) Idv)\n(declare-fun smt__TLA____SetEnum__2 (Idv Idv) Idv)\n(declare-fun smt__TLA____SetEnum__3 (Idv Idv Idv) Idv)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(declare-fun smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (Idv Idv) Bool)\n(declare-fun smt__TLA____Tuple__2 (Idv Idv) Idv)\n(declare-fun smt__TLA____Tuple__3 (Idv Idv Idv) Idv)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__x Idv)) (! (= (smt__TLA____Mem smt__x smt__TLA____NatSet) (and (smt__TLA____Mem smt__x smt__TLA____IntSet) (smt__TLA____IntLteq (smt__TLA____Cast__Int 0) smt__x))) :pattern ((smt__TLA____Mem smt__x smt__TLA____NatSet)))) :named |NatSetDef|))\n(assert (! (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv)) (! (= (smt__TLA____Mem smt__x (smt__TLA____IntRange smt__a smt__b)) (and (smt__TLA____Mem smt__x smt__TLA____IntSet) (smt__TLA____IntLteq smt__a smt__x) (smt__TLA____IntLteq smt__x smt__b))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____IntRange smt__a smt__b))))) :named |IntRangeDef|))\n(assert (! (forall ((smt__f Idv) (smt__g Idv)) (! (=> (and (smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g) (= (smt__TLA____FunDom smt__f) (smt__TLA____FunDom smt__g)) (forall ((smt__x Idv)) (=> (smt__TLA____Mem smt__x (smt__TLA____FunDom smt__f)) (= (smt__TLA____FunApp smt__f smt__x) (smt__TLA____FunApp smt__g smt__x))))) (= smt__f smt__g)) :pattern ((smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g)))) :named |FunExt|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv)) (! (=> (and (smt__TLA____FunIsafcn smt__s) (>= (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) 0) (forall ((smt__i Idv)) (= (smt__TLA____Mem smt__i (smt__TLA____FunDom smt__s)) (and (smt__TLA____Mem smt__i smt__TLA____IntSet) (<= 1 (smt__TLA____Proj__Int smt__i)) (<= (smt__TLA____Proj__Int smt__i) (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))))) (forall ((smt__i Int)) (=> (and (<= 1 smt__i) (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))) (smt__TLA____Mem (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)) smt__a)))) (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))))) :named |SeqSetIntro|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv)) (! (=> (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (and (smt__TLA____FunIsafcn smt__s) (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (= (smt__TLA____FunDom smt__s) (smt__TLA____IntRange (smt__TLA____Cast__Int 1) (smt__TLA____Len smt__s))))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))))) :named |SetSetElim1|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv) (smt__i Int)) (! (=> (and (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (<= 1 smt__i) (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))) (smt__TLA____Mem (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)) smt__a)) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i))))) :named |SetSetElim2|))\n(assert (! (forall ((smt__s Idv) (smt__z Int)) (=> (and (>= smt__z 0) (= (smt__TLA____FunDom smt__s) (smt__TLA____IntRange (smt__TLA____Cast__Int 1) (smt__TLA____Cast__Int smt__z)))) (= (smt__TLA____Len smt__s) (smt__TLA____Cast__Int smt__z)))) :named |SeqLenDef|))\n(assert (! (forall ((smt__a Idv) (smt__b Idv)) (! (smt__TLA____SetExtTrigger smt__a smt__b) :pattern ((smt__TLA____IsSetOf smt__a) (smt__TLA____IsSetOf smt__b)))) :named |CompareSetOfTrigger|))\n(assert (! (forall ((smt__a1 Idv) (smt__a2 Idv)) (! (and (smt__TLA____Mem smt__a1 (smt__TLA____SetEnum__2 smt__a1 smt__a2)) (smt__TLA____Mem smt__a2 (smt__TLA____SetEnum__2 smt__a1 smt__a2))) :pattern ((smt__TLA____SetEnum__2 smt__a1 smt__a2)))) :named |EnumDefIntro 2|))\n(assert (! (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv)) (! (and (smt__TLA____Mem smt__a1 (smt__TLA____SetEnum__3 smt__a1 smt__a2 smt__a3)) (smt__TLA____Mem smt__a2 (smt__TLA____SetEnum__3 smt__a1 smt__a2 smt__a3)) (smt__TLA____Mem smt__a3 (smt__TLA____SetEnum__3 smt__a1 smt__a2 smt__a3))) :pattern ((smt__TLA____SetEnum__3 smt__a1 smt__a2 smt__a3)))) :named |EnumDefIntro 3|))\n(assert (! (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__x Idv)) (! (=> (smt__TLA____Mem smt__x (smt__TLA____SetEnum__2 smt__a1 smt__a2)) (or (= smt__x smt__a1) (= smt__x smt__a2))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____SetEnum__2 smt__a1 smt__a2))))) :named |EnumDefElim 2|))\n(assert (! (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv) (smt__x Idv)) (! (=> (smt__TLA____Mem smt__x (smt__TLA____SetEnum__3 smt__a1 smt__a2 smt__a3)) (or (= smt__x smt__a1) (= smt__x smt__a2) (= smt__x smt__a3))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____SetEnum__3 smt__a1 smt__a2 smt__a3))))) :named |EnumDefElim 3|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv)) (! (smt__TLA____FunIsafcn (smt__TLA____Tuple__2 smt__x1 smt__x2)) :pattern ((smt__TLA____Tuple__2 smt__x1 smt__x2)))) :named |TupIsafcn 2|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv)) (! (smt__TLA____FunIsafcn (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3)) :pattern ((smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3)))) :named |TupIsafcn 3|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv)) (! (= (smt__TLA____FunDom (smt__TLA____Tuple__2 smt__x1 smt__x2)) (smt__TLA____SetEnum__2 (smt__TLA____Cast__Int 1) (smt__TLA____Cast__Int 2))) :pattern ((smt__TLA____Tuple__2 smt__x1 smt__x2)))) :named |TupDomDef 2|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv)) (! (= (smt__TLA____FunDom (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3)) (smt__TLA____SetEnum__3 (smt__TLA____Cast__Int 1) (smt__TLA____Cast__Int 2) (smt__TLA____Cast__Int 3))) :pattern ((smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3)))) :named |TupDomDef 3|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv)) (! (and (= (smt__TLA____FunApp (smt__TLA____Tuple__2 smt__x1 smt__x2) (smt__TLA____Cast__Int 1)) smt__x1) (= (smt__TLA____FunApp (smt__TLA____Tuple__2 smt__x1 smt__x2) (smt__TLA____Cast__Int 2)) smt__x2)) :pattern ((smt__TLA____Tuple__2 smt__x1 smt__x2)))) :named |TupAppDef 2|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv)) (! (and (= (smt__TLA____FunApp (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3) (smt__TLA____Cast__Int 1)) smt__x1) (= (smt__TLA____FunApp (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3) (smt__TLA____Cast__Int 2)) smt__x2) (= (smt__TLA____FunApp (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3) (smt__TLA____Cast__Int 3)) smt__x3)) :pattern ((smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3)))) :named |TupAppDef 3|))\n(assert (! (forall ((smt__s1 Idv) (smt__s2 Idv) (smt__x1 Idv) (smt__x2 Idv)) (! (=> (and (smt__TLA____Mem smt__x1 smt__s1) (smt__TLA____Mem smt__x2 smt__s2)) (smt__TLA____Mem (smt__TLA____Tuple__2 smt__x1 smt__x2) (smt__TLA____Product__2 smt__s1 smt__s2))) :pattern ((smt__TLA____Tuple__2 smt__x1 smt__x2) (smt__TLA____Product__2 smt__s1 smt__s2)))) :named |ProductIntro 2|))\n(assert (! (forall ((smt__s1 Idv) (smt__s2 Idv) (smt__t Idv)) (! (=> (smt__TLA____Mem smt__t (smt__TLA____Product__2 smt__s1 smt__s2)) (and (= smt__t (smt__TLA____Tuple__2 (smt__TLA____FunApp smt__t (smt__TLA____Cast__Int 1)) (smt__TLA____FunApp smt__t (smt__TLA____Cast__Int 2)))) (smt__TLA____Mem (smt__TLA____FunApp smt__t (smt__TLA____Cast__Int 1)) smt__s1) (smt__TLA____Mem (smt__TLA____FunApp smt__t (smt__TLA____Cast__Int 2)) smt__s2))) :pattern ((smt__TLA____Mem smt__t (smt__TLA____Product__2 smt__s1 smt__s2))))) :named |ProductElim 2|))\n(assert (! (forall ((smt__a Idv) (smt__x1 Idv) (smt__x2 Idv)) (! (=> (and (smt__TLA____Mem smt__x1 smt__a) (smt__TLA____Mem smt__x2 smt__a)) (smt__TLA____Mem (smt__TLA____Tuple__2 smt__x1 smt__x2) (smt__TLA____Seq smt__a))) :pattern ((smt__TLA____Mem smt__x1 smt__a) (smt__TLA____Mem smt__x2 smt__a) (smt__TLA____Tuple__2 smt__x1 smt__x2)))) :named |SeqTupTyping 2|))\n(assert (! (forall ((smt__a Idv) (smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv)) (! (=> (and (smt__TLA____Mem smt__x1 smt__a) (smt__TLA____Mem smt__x2 smt__a) (smt__TLA____Mem smt__x3 smt__a)) (smt__TLA____Mem (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3) (smt__TLA____Seq smt__a))) :pattern ((smt__TLA____Mem smt__x1 smt__a) (smt__TLA____Mem smt__x2 smt__a) (smt__TLA____Mem smt__x3 smt__a) (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3)))) :named |SeqTupTyping 3|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv)) (! (= (smt__TLA____Len (smt__TLA____Tuple__2 smt__x1 smt__x2)) (smt__TLA____Cast__Int 2)) :pattern ((smt__TLA____Tuple__2 smt__x1 smt__x2)))) :named |SeqTupLen 2|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv)) (! (= (smt__TLA____Len (smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3)) (smt__TLA____Cast__Int 3)) :pattern ((smt__TLA____Tuple__3 smt__x1 smt__x2 smt__x3)))) :named |SeqTupLen 3|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(assert (! (forall ((smt__x1 Int) (smt__x2 Int)) (! (= (smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2)) (<= smt__x1 smt__x2)) :pattern ((smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2))))) :named |Typing TIntLteq|))\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (= (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y) (= smt__x smt__y)) :pattern ((smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y)))) :named |ExtTrigEqDef Set$Idv$|))\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (smt__TLA____SetExtTrigger smt__x smt__y) :pattern ((smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y)))) :named |ExtTrigEqTrigger Idv|))\n(declare-fun smt__S () Idv)\n(declare-fun smt__TLA____SetOf__2__flatnd__1 (Idv Idv) Idv)\n(assert (! (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__y1 Idv) (smt__y2 Idv)) (! (=> (and (smt__TLA____Mem smt__y1 smt__a1) (smt__TLA____Mem smt__y2 smt__a2)) (smt__TLA____Mem (smt__TLA____Tuple__3 smt__y2 smt__y1 smt__S) (smt__TLA____SetOf__2__flatnd__1 smt__a1 smt__a2))) :pattern ((smt__TLA____Tuple__3 smt__y2 smt__y1 smt__S) (smt__TLA____SetOf__2__flatnd__1 smt__a1 smt__a2)) :pattern ((smt__TLA____SetOf__2__flatnd__1 smt__a1 smt__a2) (smt__TLA____Mem smt__y1 smt__a1) (smt__TLA____Mem smt__y2 smt__a2)))) :named |SetOfIntro 2 TLA__SetOf_2_flatnd_1|))\n(assert (! (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__x Idv)) (! (=> (smt__TLA____Mem smt__x (smt__TLA____SetOf__2__flatnd__1 smt__a1 smt__a2)) (exists ((smt__y1 Idv) (smt__y2 Idv)) (and (smt__TLA____Mem smt__y1 smt__a1) (smt__TLA____Mem smt__y2 smt__a2) (= smt__x (smt__TLA____Tuple__3 smt__y2 smt__y1 smt__S))))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____SetOf__2__flatnd__1 smt__a1 smt__a2))))) :named |SetOfElim 2 TLA__SetOf_2_flatnd_1|))\n(assert (! (forall ((smt__a1 Idv) (smt__a2 Idv)) (! (smt__TLA____IsSetOf (smt__TLA____SetOf__2__flatnd__1 smt__a1 smt__a2)) :pattern ((smt__TLA____SetOf__2__flatnd__1 smt__a1 smt__a2)))) :named |AssertIsSetOf 2 TLA__SetOf_2_flatnd_1|))\n(assert (! (not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____SetOf__2__flatnd__1 smt__S smt__S) (smt__TLA____Product__2 smt__S smt__S))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"SetOf","element":{"kind":"Ix","index":1},"bounds":[{"name":"i","level":"Constant","domain":{"kind":"NoDomain"}}]},{"kind":"Ix","index":1}]}},0,"TlaUnsupportedError: a set of values without a domain"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"i","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":1}}},{"name":"j","level":"Constant","domain":{"kind":"Ditto"}},{"name":"k","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"FcnApp","function":{"kind":"Ix","index":4},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]},{"kind":"Dot","expression":{"kind":"Ix","index":3},"field":"fé ld"}]}}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____FunApp (Idv Idv) Idv)\n(declare-fun smt__TLA____FunDom (Idv) Idv)\n(declare-fun smt__TLA____FunIsafcn (Idv) Bool)\n(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)\n(declare-fun smt__TLA____IntRange (Idv Idv) Idv)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Len (Idv) Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____NatSet () Idv)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____Seq (Idv) Idv)\n(declare-fun smt__TLA____SetEnum__2 (Idv Idv) Idv)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(declare-fun smt__TLA____StrLit__féspace__ld () Idv)\n(declare-fun smt__TLA____StrSet () Idv)\n(declare-fun smt__TLA____Tuple__2 (Idv Idv) Idv)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__x Idv)) (! (= (smt__TLA____Mem smt__x smt__TLA____NatSet) (and (smt__TLA____Mem smt__x smt__TLA____IntSet) (smt__TLA____IntLteq (smt__TLA____Cast__Int 0) smt__x))) :pattern ((smt__TLA____Mem smt__x smt__TLA____NatSet)))) :named |NatSetDef|))\n(assert (! (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv)) (! (= (smt__TLA____Mem smt__x (smt__TLA____IntRange smt__a smt__b)) (and (smt__TLA____Mem smt__x smt__TLA____IntSet) (smt__TLA____IntLteq smt__a smt__x) (smt__TLA____IntLteq smt__x smt__b))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____IntRange smt__a smt__b))))) :named |IntRangeDef|))\n(assert (! (forall ((smt__f Idv) (smt__g Idv)) (! (=> (and (smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g) (= (smt__TLA____FunDom smt__f) (smt__TLA____FunDom smt__g)) (forall ((smt__x Idv)) (=> (smt__TLA____Mem smt__x (smt__TLA____FunDom smt__f)) (= (smt__TLA____FunApp smt__f smt__x) (smt__TLA____FunApp smt__g smt__x))))) (= smt__f smt__g)) :pattern ((smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g)))) :named |FunExt|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv)) (! (=> (and (smt__TLA____FunIsafcn smt__s) (>= (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) 0) (forall ((smt__i Idv)) (= (smt__TLA____Mem smt__i (smt__TLA____FunDom smt__s)) (and (smt__TLA____Mem smt__i smt__TLA____IntSet) (<= 1 (smt__TLA____Proj__Int smt__i)) (<= (smt__TLA____Proj__Int smt__i) (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))))) (forall ((smt__i Int)) (=> (and (<= 1 smt__i) (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))) (smt__TLA____Mem (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)) smt__a)))) (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))))) :named |SeqSetIntro|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv)) (! (=> (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (and (smt__TLA____FunIsafcn smt__s) (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (= (smt__TLA____FunDom smt__s) (smt__TLA____IntRange (smt__TLA____Cast__Int 1) (smt__TLA____Len smt__s))))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))))) :named |SetSetElim1|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv) (smt__i Int)) (! (=> (and (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (<= 1 smt__i) (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))) (smt__TLA____Mem (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)) smt__a)) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i))))) :named |SetSetElim2|))\n(assert (! (forall ((smt__s Idv) (smt__z Int)) (=> (and (>= smt__z 0) (= (smt__TLA____FunDom smt__s) (smt__TLA____IntRange (smt__TLA____Cast__Int 1) (smt__TLA____Cast__Int smt__z)))) (= (smt__TLA____Len smt__s) (smt__TLA____Cast__Int smt__z)))) :named |SeqLenDef|))\n(assert (! (forall ((smt__a1 Idv) (smt__a2 Idv)) (! (and (smt__TLA____Mem smt__a1 (smt__TLA____SetEnum__2 smt__a1 smt__a2)) (smt__TLA____Mem smt__a2 (smt__TLA____SetEnum__2 smt__a1 smt__a2))) :pattern ((smt__TLA____SetEnum__2 smt__a1 smt__a2)))) :named |EnumDefIntro 2|))\n(assert (! (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__x Idv)) (! (=> (smt__TLA____Mem smt__x (smt__TLA____SetEnum__2 smt__a1 smt__a2)) (or (= smt__x smt__a1) (= smt__x smt__a2))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____SetEnum__2 smt__a1 smt__a2))))) :named |EnumDefElim 2|))\n(assert (! (smt__TLA____Mem smt__TLA____StrLit__féspace__ld smt__TLA____StrSet) :named |StrLitIsstr fé ld|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv)) (! (smt__TLA____FunIsafcn (smt__TLA____Tuple__2 smt__x1 smt__x2)) :pattern ((smt__TLA____Tuple__2 smt__x1 smt__x2)))) :named |TupIsafcn 2|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv)) (! (= (smt__TLA____FunDom (smt__TLA____Tuple__2 smt__x1 smt__x2)) (smt__TLA____SetEnum__2 (smt__TLA____Cast__Int 1) (smt__TLA____Cast__Int 2))) :pattern ((smt__TLA____Tuple__2 smt__x1 smt__x2)))) :named |TupDomDef 2|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv)) (! (and (= (smt__TLA____FunApp (smt__TLA____Tuple__2 smt__x1 smt__x2) (smt__TLA____Cast__Int 1)) smt__x1) (= (smt__TLA____FunApp (smt__TLA____Tuple__2 smt__x1 smt__x2) (smt__TLA____Cast__Int 2)) smt__x2)) :pattern ((smt__TLA____Tuple__2 smt__x1 smt__x2)))) :named |TupAppDef 2|))\n(assert (! (forall ((smt__a Idv) (smt__x1 Idv) (smt__x2 Idv)) (! (=> (and (smt__TLA____Mem smt__x1 smt__a) (smt__TLA____Mem smt__x2 smt__a)) (smt__TLA____Mem (smt__TLA____Tuple__2 smt__x1 smt__x2) (smt__TLA____Seq smt__a))) :pattern ((smt__TLA____Mem smt__x1 smt__a) (smt__TLA____Mem smt__x2 smt__a) (smt__TLA____Tuple__2 smt__x1 smt__x2)))) :named |SeqTupTyping 2|))\n(assert (! (forall ((smt__x1 Idv) (smt__x2 Idv)) (! (= (smt__TLA____Len (smt__TLA____Tuple__2 smt__x1 smt__x2)) (smt__TLA____Cast__Int 2)) :pattern ((smt__TLA____Tuple__2 smt__x1 smt__x2)))) :named |SeqTupLen 2|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(assert (! (forall ((smt__x1 Int) (smt__x2 Int)) (! (= (smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2)) (<= smt__x1 smt__x2)) :pattern ((smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2))))) :named |Typing TIntLteq|))\n(declare-fun smt__S () Idv)\n(assert (! (not (exists ((smt__i Idv) (smt__j Idv) (smt__k Idv)) (and (smt__TLA____Mem smt__i smt__S) (smt__TLA____Mem smt__j smt__S) (= (smt__TLA____FunApp smt__S (smt__TLA____Tuple__2 smt__k smt__j)) (smt__TLA____FunApp smt__i smt__TLA____StrLit__féspace__ld))))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"i","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Choose","name":"c","domain":{"kind":"Ix","index":2},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}},{"kind":"Choose","name":"d","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}]}}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(declare-fun smt__S () Idv)\n(declare-fun smt__TLA____Choose__flatnd__1 (Idv) Idv)\n(assert (! (forall ((smt__i Idv) (smt__x Idv)) (=> (and (smt__TLA____Mem smt__x smt__S) (smt__TLA____Mem smt__x smt__i)) (and (smt__TLA____Mem (smt__TLA____Choose__flatnd__1 smt__i) smt__S) (smt__TLA____Mem (smt__TLA____Choose__flatnd__1 smt__i) smt__i)))) :named |ChooseDef TLA__Choose_flatnd_1|))\n(declare-fun smt__TLA____Choose__flatnd__2 (Idv) Idv)\n(assert (! (forall ((smt__i Idv) (smt__x Idv)) (=> (= smt__x smt__i) (= (smt__TLA____Choose__flatnd__2 smt__i) smt__i))) :named |ChooseDef TLA__Choose_flatnd_2|))\n(assert (! (not (forall ((smt__i Idv)) (= (smt__TLA____Choose__flatnd__1 smt__i) (smt__TLA____Choose__flatnd__2 smt__i)))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Arrow","domain":{"kind":"Ix","index":1},"range":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Seq"},"args":[{"kind":"Internal","builtin":"STRING"}]}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Range"},"args":[{"kind":"Num","integer":"1","fraction":""},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Len"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Append"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Tail"},"args":[{"kind":"Ix","index":1}]},{"kind":"String","value":"a|b\\c"}]}]}]}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Append (Idv Idv) Idv)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____FunApp (Idv Idv) Idv)\n(declare-fun smt__TLA____FunDom (Idv) Idv)\n(declare-fun smt__TLA____FunIsafcn (Idv) Bool)\n(declare-fun smt__TLA____FunSet (Idv Idv) Idv)\n(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)\n(declare-fun smt__TLA____IntRange (Idv Idv) Idv)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____Len (Idv) Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____NatSet () Idv)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____Seq (Idv) Idv)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(declare-fun smt__TLA____StrLit__averticalbar__bbackslash__c () Idv)\n(declare-fun smt__TLA____StrSet () Idv)\n(declare-fun smt__TLA____Tail (Idv) Idv)\n(declare-fun smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__x Idv)) (! (= (smt__TLA____Mem smt__x smt__TLA____NatSet) (and (smt__TLA____Mem smt__x smt__TLA____IntSet) (smt__TLA____IntLteq (smt__TLA____Cast__Int 0) smt__x))) :pattern ((smt__TLA____Mem smt__x smt__TLA____NatSet)))) :named |NatSetDef|))\n(assert (! (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv)) (! (= (smt__TLA____Mem smt__x (smt__TLA____IntRange smt__a smt__b)) (and (smt__TLA____Mem smt__x smt__TLA____IntSet) (smt__TLA____IntLteq smt__a smt__x) (smt__TLA____IntLteq smt__x smt__b))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____IntRange smt__a smt__b))))) :named |IntRangeDef|))\n(assert (! (forall ((smt__f Idv) (smt__g Idv)) (! (=> (and (smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g) (= (smt__TLA____FunDom smt__f) (smt__TLA____FunDom smt__g)) (forall ((smt__x Idv)) (=> (smt__TLA____Mem smt__x (smt__TLA____FunDom smt__f)) (= (smt__TLA____FunApp smt__f smt__x) (smt__TLA____FunApp smt__g smt__x))))) (= smt__f smt__g)) :pattern ((smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g)))) :named |FunExt|))\n(assert (! (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv)) (! (=> (and (smt__TLA____FunIsafcn smt__f) (= (smt__TLA____FunDom smt__f) smt__a) (forall ((smt__x Idv)) (=> (smt__TLA____Mem smt__x smt__a) (smt__TLA____Mem (smt__TLA____FunApp smt__f smt__x) smt__b)))) (smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b))) :pattern ((smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b))))) :named |FunSetIntro|))\n(assert (! (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv)) (! (=> (smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b)) (and (smt__TLA____FunIsafcn smt__f) (= (smt__TLA____FunDom smt__f) smt__a))) :pattern ((smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b))))) :named |FunSetElim1|))\n(assert (! (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv) (smt__x Idv)) (! (=> (and (smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b)) (smt__TLA____Mem smt__x smt__a)) (smt__TLA____Mem (smt__TLA____FunApp smt__f smt__x) smt__b)) :pattern ((smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b)) (smt__TLA____Mem smt__x smt__a)) :pattern ((smt__TLA____Mem smt__f (smt__TLA____FunSet smt__a smt__b)) (smt__TLA____FunApp smt__f smt__x)))) :named |FunSetElim2|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv)) (! (=> (and (smt__TLA____FunIsafcn smt__s) (>= (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) 0) (forall ((smt__i Idv)) (= (smt__TLA____Mem smt__i (smt__TLA____FunDom smt__s)) (and (smt__TLA____Mem smt__i smt__TLA____IntSet) (<= 1 (smt__TLA____Proj__Int smt__i)) (<= (smt__TLA____Proj__Int smt__i) (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))))) (forall ((smt__i Int)) (=> (and (<= 1 smt__i) (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))) (smt__TLA____Mem (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)) smt__a)))) (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))))) :named |SeqSetIntro|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv)) (! (=> (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (and (smt__TLA____FunIsafcn smt__s) (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (= (smt__TLA____FunDom smt__s) (smt__TLA____IntRange (smt__TLA____Cast__Int 1) (smt__TLA____Len smt__s))))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))))) :named |SetSetElim1|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv) (smt__i Int)) (! (=> (and (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (<= 1 smt__i) (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))) (smt__TLA____Mem (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)) smt__a)) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i))))) :named |SetSetElim2|))\n(assert (! (forall ((smt__s Idv) (smt__z Int)) (=> (and (>= smt__z 0) (= (smt__TLA____FunDom smt__s) (smt__TLA____IntRange (smt__TLA____Cast__Int 1) (smt__TLA____Cast__Int smt__z)))) (= (smt__TLA____Len smt__s) (smt__TLA____Cast__Int smt__z)))) :named |SeqLenDef|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv) (smt__x Idv)) (! (=> (and (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (smt__TLA____Mem smt__x smt__a)) (smt__TLA____Mem (smt__TLA____Append smt__s smt__x) (smt__TLA____Seq smt__a))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (smt__TLA____Append smt__s smt__x)))) :named |SeqAppendTyping|))\n(assert (! (forall ((smt__s Idv) (smt__x Idv)) (! (=> (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (= (smt__TLA____Len (smt__TLA____Append smt__s smt__x)) (smt__TLA____Cast__Int (+ (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) 1)))) :pattern ((smt__TLA____Append smt__s smt__x)))) :named |SeqAppendLen|))\n(assert (! (forall ((smt__s Idv) (smt__x Idv) (smt__i Int)) (! (=> (and (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (<= 1 smt__i) (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))) (= (smt__TLA____FunApp (smt__TLA____Append smt__s smt__x) (smt__TLA____Cast__Int smt__i)) (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)))) :pattern ((smt__TLA____FunApp (smt__TLA____Append smt__s smt__x) (smt__TLA____Cast__Int smt__i))) :pattern ((smt__TLA____Append smt__s smt__x) (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i))))) :named |SeqAppendApp1|))\n(assert (! (forall ((smt__s Idv) (smt__x Idv)) (! (=> (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (= (smt__TLA____FunApp (smt__TLA____Append smt__s smt__x) (smt__TLA____Cast__Int (+ (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) 1))) smt__x)) :pattern ((smt__TLA____Append smt__s smt__x)))) :named |SeqAppendApp2|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv)) (! (=> (and (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (distinct (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) 0)) (smt__TLA____Mem (smt__TLA____Tail smt__s) (smt__TLA____Seq smt__a))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (smt__TLA____Tail smt__s)))) :named |SeqTailTyping|))\n(assert (! (forall ((smt__s Idv)) (! (=> (and (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (distinct (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) 0)) (= (smt__TLA____Len (smt__TLA____Tail smt__s)) (smt__TLA____Cast__Int (- (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) 1)))) :pattern ((smt__TLA____Tail smt__s)))) :named |SeqTailLen|))\n(assert (! (forall ((smt__s Idv) (smt__i Int)) (! (=> (and (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (distinct (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) 0) (<= 1 smt__i) (<= smt__i (- (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) 1))) (= (smt__TLA____FunApp (smt__TLA____Tail smt__s) (smt__TLA____Cast__Int smt__i)) (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int (+ smt__i 1))))) :pattern ((smt__TLA____FunApp (smt__TLA____Tail smt__s) (smt__TLA____Cast__Int smt__i))))) :named |SeqTailApp|))\n(assert (! (smt__TLA____Mem smt__TLA____StrLit__averticalbar__bbackslash__c smt__TLA____StrSet) :named |StrLitIsstr a|b\\c|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(assert (! (forall ((smt__x1 Int) (smt__x2 Int)) (! (= (smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2)) (<= smt__x1 smt__x2)) :pattern ((smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2))))) :named |Typing TIntLteq|))\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (= (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y) (= smt__x smt__y)) :pattern ((smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y)))) :named |ExtTrigEqDef Set$Idv$|))\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (smt__TLA____SetExtTrigger smt__x smt__y) :pattern ((smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y)))) :named |ExtTrigEqTrigger Idv|))\n(declare-fun smt__S () Idv)\n(assert (! (not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____FunSet smt__S (smt__TLA____Seq smt__TLA____StrSet)) (smt__TLA____IntRange (smt__TLA____Cast__Int 1) (smt__TLA____Len (smt__TLA____Append (smt__TLA____Tail smt__S) smt__TLA____StrLit__averticalbar__bbackslash__c))))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"List","bullet":"Or","items":[{"kind":"Parens","expression":{"kind":"Internal","builtin":"TRUE"},"form":{"kind":"Syntax"}},{"kind":"With","expression":{"kind":"Internal","builtin":"FALSE"},"method":{"name":"smt"}}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__S () Idv)\n(assert (! (not (or true false)) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Ix","index":1}]}},0,"TlaUnsupportedError: the operator Prime"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Internal","builtin":"Real"},{"kind":"Ix","index":1}]}},0,"TlaUnsupportedError: the operator Real"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Tquant","quantifier":"Forall","names":["t"],"body":{"kind":"Internal","builtin":"TRUE"}}},0,"TlaUnsupportedError: a temporal formula"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Let","definitions":[],"body":{"kind":"Internal","builtin":"TRUE"}}},0,"TlaUnsupportedError: the expression Let"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cup"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]},"args":[{"kind":"Ix","index":1}]}},0,"TlaUnsupportedError: an application of Apply"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Lambda","params":[{"name":"p","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}},"args":[{"kind":"Ix","index":1}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(declare-fun smt__S () Idv)\n(assert (! (not (smt__TLA____Mem smt__S smt__S)) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neq"},"args":[{"kind":"SetEnum","elements":[]},{"kind":"SetEnum","elements":[{"kind":"Ix","index":1},{"kind":"String","value":"x"}]}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____SetEnum__0 () Idv)\n(declare-fun smt__TLA____SetEnum__2 (Idv Idv) Idv)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(declare-fun smt__TLA____StrLit__x () Idv)\n(declare-fun smt__TLA____StrSet () Idv)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__a1 Idv) (smt__a2 Idv)) (! (and (smt__TLA____Mem smt__a1 (smt__TLA____SetEnum__2 smt__a1 smt__a2)) (smt__TLA____Mem smt__a2 (smt__TLA____SetEnum__2 smt__a1 smt__a2))) :pattern ((smt__TLA____SetEnum__2 smt__a1 smt__a2)))) :named |EnumDefIntro 2|))\n(assert (! (forall ((smt__x Idv)) (! (not (smt__TLA____Mem smt__x smt__TLA____SetEnum__0)) :pattern ((smt__TLA____Mem smt__x smt__TLA____SetEnum__0)))) :named |EnumDefElim 0|))\n(assert (! (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__x Idv)) (! (=> (smt__TLA____Mem smt__x (smt__TLA____SetEnum__2 smt__a1 smt__a2)) (or (= smt__x smt__a1) (= smt__x smt__a2))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____SetEnum__2 smt__a1 smt__a2))))) :named |EnumDefElim 2|))\n(assert (! (smt__TLA____Mem smt__TLA____StrLit__x smt__TLA____StrSet) :named |StrLitIsstr x|))\n(declare-fun smt__S () Idv)\n(assert (! (not (distinct smt__TLA____SetEnum__0 (smt__TLA____SetEnum__2 smt__S smt__TLA____StrLit__x))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neg"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"SetEnum","elements":[{"kind":"Ix","index":1}]},{"kind":"Ix","index":1}]}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____SetEnum__1 (Idv) Idv)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__a1 Idv)) (! (smt__TLA____Mem smt__a1 (smt__TLA____SetEnum__1 smt__a1)) :pattern ((smt__TLA____SetEnum__1 smt__a1)))) :named |EnumDefIntro 1|))\n(assert (! (forall ((smt__a1 Idv) (smt__x Idv)) (! (=> (smt__TLA____Mem smt__x (smt__TLA____SetEnum__1 smt__a1)) (= smt__x smt__a1)) :pattern ((smt__TLA____Mem smt__x (smt__TLA____SetEnum__1 smt__a1))))) :named |EnumDefElim 1|))\n(declare-fun smt__S () Idv)\n(assert (! (not (not (= (smt__TLA____SetEnum__1 smt__S) smt__S))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"SetEnum","elements":[{"kind":"Ix","index":1}]},{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cap"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]},{"kind":"Ix","index":1}]}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Cap (Idv Idv) Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____SetEnum__0 () Idv)\n(declare-fun smt__TLA____SetEnum__1 (Idv) Idv)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv)) (! (= (smt__TLA____Mem smt__x (smt__TLA____Cap smt__a smt__b)) (and (smt__TLA____Mem smt__x smt__a) (smt__TLA____Mem smt__x smt__b))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____Cap smt__a smt__b))) :pattern ((smt__TLA____Mem smt__x smt__a) (smt__TLA____Cap smt__a smt__b)) :pattern ((smt__TLA____Mem smt__x smt__b) (smt__TLA____Cap smt__a smt__b)))) :named |CapDef|))\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (smt__TLA____SetExtTrigger (smt__TLA____Cap smt__x smt__y) smt__TLA____SetEnum__0) :pattern ((smt__TLA____Cap smt__x smt__y)))) :named |DisjointTrigger|))\n(assert (! (forall ((smt__a1 Idv)) (! (smt__TLA____Mem smt__a1 (smt__TLA____SetEnum__1 smt__a1)) :pattern ((smt__TLA____SetEnum__1 smt__a1)))) :named |EnumDefIntro 1|))\n(assert (! (forall ((smt__x Idv)) (! (not (smt__TLA____Mem smt__x smt__TLA____SetEnum__0)) :pattern ((smt__TLA____Mem smt__x smt__TLA____SetEnum__0)))) :named |EnumDefElim 0|))\n(assert (! (forall ((smt__a1 Idv) (smt__x Idv)) (! (=> (smt__TLA____Mem smt__x (smt__TLA____SetEnum__1 smt__a1)) (= smt__x smt__a1)) :pattern ((smt__TLA____Mem smt__x (smt__TLA____SetEnum__1 smt__a1))))) :named |EnumDefElim 1|))\n(declare-fun smt__S () Idv)\n(assert (! (not (=> (= (smt__TLA____SetEnum__1 smt__S) smt__S) (distinct (smt__TLA____Cap smt__S smt__S) smt__S))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cap"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]},{"kind":"Ix","index":1}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cap"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":2}]},{"kind":"Ix","index":2}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Ix","index":3}]},{"kind":"Ix","index":3}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____BoolSet () Idv)\n(declare-fun smt__TLA____Cap (Idv Idv) Idv)\n(declare-fun smt__TLA____Cast__Bool (Bool) Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____SetEnum__0 () Idv)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(declare-fun smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (Idv Idv) Bool)\n(declare-fun smt__TLA____Tt__Idv () Idv)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv)) (! (= (smt__TLA____Mem smt__x (smt__TLA____Cap smt__a smt__b)) (and (smt__TLA____Mem smt__x smt__a) (smt__TLA____Mem smt__x smt__b))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____Cap smt__a smt__b))) :pattern ((smt__TLA____Mem smt__x smt__a) (smt__TLA____Cap smt__a smt__b)) :pattern ((smt__TLA____Mem smt__x smt__b) (smt__TLA____Cap smt__a smt__b)))) :named |CapDef|))\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (smt__TLA____SetExtTrigger (smt__TLA____Cap smt__x smt__y) smt__TLA____SetEnum__0) :pattern ((smt__TLA____Cap smt__x smt__y)))) :named |DisjointTrigger|))\n(assert (! (forall ((smt__x Idv)) (! (not (smt__TLA____Mem smt__x smt__TLA____SetEnum__0)) :pattern ((smt__TLA____Mem smt__x smt__TLA____SetEnum__0)))) :named |EnumDefElim 0|))\n(assert (! (and (= (smt__TLA____Cast__Bool true) smt__TLA____Tt__Idv) (distinct (smt__TLA____Cast__Bool false) smt__TLA____Tt__Idv)) :named |CastInjAlt Bool|))\n(assert (! (forall ((smt__z Bool)) (! (smt__TLA____Mem (smt__TLA____Cast__Bool smt__z) smt__TLA____BoolSet) :pattern ((smt__TLA____Cast__Bool smt__z)))) :named |TypeGuardIntro Bool|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____BoolSet) (or (= smt__x (smt__TLA____Cast__Bool true)) (= smt__x (smt__TLA____Cast__Bool false)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____BoolSet)))) :named |TypeGuardElim Bool|))\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (= (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y) (= smt__x smt__y)) :pattern ((smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y)))) :named |ExtTrigEqDef Set$Idv$|))\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (smt__TLA____SetExtTrigger smt__x smt__y) :pattern ((smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y)))) :named |ExtTrigEqTrigger Idv|))\n(declare-fun smt__S () Idv)\n(assert (not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____Cap smt__S smt__S) smt__S)))\n(assert (= (smt__TLA____Cap smt__S smt__S) smt__S))\n(assert (! (not (smt__TLA____Mem (smt__TLA____Cast__Bool (= smt__S smt__S)) smt__S)) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cap"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]},{"kind":"Ix","index":1}]},{"kind":"Internal","builtin":"BOOLEAN"}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____BoolSet () Idv)\n(declare-fun smt__TLA____Cap (Idv Idv) Idv)\n(declare-fun smt__TLA____Cast__Bool (Bool) Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____SetEnum__0 () Idv)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(declare-fun smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (Idv Idv) Bool)\n(declare-fun smt__TLA____Tt__Idv () Idv)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv)) (! (= (smt__TLA____Mem smt__x (smt__TLA____Cap smt__a smt__b)) (and (smt__TLA____Mem smt__x smt__a) (smt__TLA____Mem smt__x smt__b))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____Cap smt__a smt__b))) :pattern ((smt__TLA____Mem smt__x smt__a) (smt__TLA____Cap smt__a smt__b)) :pattern ((smt__TLA____Mem smt__x smt__b) (smt__TLA____Cap smt__a smt__b)))) :named |CapDef|))\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (smt__TLA____SetExtTrigger (smt__TLA____Cap smt__x smt__y) smt__TLA____SetEnum__0) :pattern ((smt__TLA____Cap smt__x smt__y)))) :named |DisjointTrigger|))\n(assert (! (forall ((smt__x Idv)) (! (not (smt__TLA____Mem smt__x smt__TLA____SetEnum__0)) :pattern ((smt__TLA____Mem smt__x smt__TLA____SetEnum__0)))) :named |EnumDefElim 0|))\n(assert (! (and (= (smt__TLA____Cast__Bool true) smt__TLA____Tt__Idv) (distinct (smt__TLA____Cast__Bool false) smt__TLA____Tt__Idv)) :named |CastInjAlt Bool|))\n(assert (! (forall ((smt__z Bool)) (! (smt__TLA____Mem (smt__TLA____Cast__Bool smt__z) smt__TLA____BoolSet) :pattern ((smt__TLA____Cast__Bool smt__z)))) :named |TypeGuardIntro Bool|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____BoolSet) (or (= smt__x (smt__TLA____Cast__Bool true)) (= smt__x (smt__TLA____Cast__Bool false)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____BoolSet)))) :named |TypeGuardElim Bool|))\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (= (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y) (= smt__x smt__y)) :pattern ((smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y)))) :named |ExtTrigEqDef Set$Idv$|))\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (smt__TLA____SetExtTrigger smt__x smt__y) :pattern ((smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y)))) :named |ExtTrigEqTrigger Idv|))\n(declare-fun smt__S () Idv)\n(assert (! (not (smt__TLA____Mem (smt__TLA____Cast__Bool (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____Cap smt__S smt__S) smt__S)) smt__TLA____BoolSet)) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"smt__S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"S","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"smt__S","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":4}]}}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__smt____S () Idv)\n(declare-fun smt__S () Idv)\n(declare-fun smt__S_1 () Idv)\n(assert (! (not (forall ((smt__S_2 Idv) (smt__smt____S_1 Idv)) (= smt__smt____S_1 smt__S))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"SetSt","name":"e","domain":{"kind":"Ix","index":1},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"SetSt","name":"e","domain":{"kind":"Ix","index":2},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}},{"kind":"Ix","index":2}]}},{"kind":"SetSt","name":"e","domain":{"kind":"Ix","index":1},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"SetSt","name":"e","domain":{"kind":"Ix","index":2},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}},{"kind":"Ix","index":2}]}}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____SetEnum__0 () Idv)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(declare-fun smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__x Idv)) (! (not (smt__TLA____Mem smt__x smt__TLA____SetEnum__0)) :pattern ((smt__TLA____Mem smt__x smt__TLA____SetEnum__0)))) :named |EnumDefElim 0|))\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (= (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y) (= smt__x smt__y)) :pattern ((smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y)))) :named |ExtTrigEqDef Set$Idv$|))\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (smt__TLA____SetExtTrigger smt__x smt__y) :pattern ((smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y)))) :named |ExtTrigEqTrigger Idv|))\n(declare-fun smt__S () Idv)\n(declare-fun smt__TLA____SetSt__flatnd__1 (Idv Idv) Idv)\n(assert (! (forall ((smt__e Idv) (smt__a Idv) (smt__x Idv)) (! (= (smt__TLA____Mem smt__x (smt__TLA____SetSt__flatnd__1 smt__a smt__e)) (and (smt__TLA____Mem smt__x smt__a) (smt__TLA____Mem smt__x smt__e))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____SetSt__flatnd__1 smt__a smt__e))) :pattern ((smt__TLA____Mem smt__x smt__a) (smt__TLA____SetSt__flatnd__1 smt__a smt__e)))) :named |SetStDef TLA__SetSt_flatnd_1|))\n(declare-fun smt__TLA____SetSt__flatnd__2 (Idv) Idv)\n(assert (! (forall ((smt__a Idv) (smt__x Idv)) (! (= (smt__TLA____Mem smt__x (smt__TLA____SetSt__flatnd__2 smt__a)) (and (smt__TLA____Mem smt__x smt__a) (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____SetSt__flatnd__1 smt__S smt__x) smt__S))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____SetSt__flatnd__2 smt__a))) :pattern ((smt__TLA____Mem smt__x smt__a) (smt__TLA____SetSt__flatnd__2 smt__a)))) :named |SetStDef TLA__SetSt_flatnd_2|))\n(assert (! (not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____SetSt__flatnd__2 smt__S) (smt__TLA____SetSt__flatnd__2 smt__S))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"DOMAIN"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNION"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Setminus"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"SubSeq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Uminus"},"args":[{"kind":"Num","integer":"2","fraction":""}]}]}]}]}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____FunApp (Idv Idv) Idv)\n(declare-fun smt__TLA____FunDom (Idv) Idv)\n(declare-fun smt__TLA____FunIsafcn (Idv) Bool)\n(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)\n(declare-fun smt__TLA____IntRange (Idv Idv) Idv)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____IntUminus (Idv) Idv)\n(declare-fun smt__TLA____Len (Idv) Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____NatSet () Idv)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____Seq (Idv) Idv)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(declare-fun smt__TLA____SetMinus (Idv Idv) Idv)\n(declare-fun smt__TLA____SubSeq (Idv Idv Idv) Idv)\n(declare-fun smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (Idv Idv) Bool)\n(declare-fun smt__TLA____Union (Idv) Idv)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__a Idv) (smt__x Idv) (smt__y Idv)) (! (=> (and (smt__TLA____Mem smt__y smt__a) (smt__TLA____Mem smt__x smt__y)) (smt__TLA____Mem smt__x (smt__TLA____Union smt__a))) :pattern ((smt__TLA____Mem smt__y smt__a) (smt__TLA____Mem smt__x (smt__TLA____Union smt__a))) :pattern ((smt__TLA____Mem smt__x smt__y) (smt__TLA____Mem smt__x (smt__TLA____Union smt__a))) :pattern ((smt__TLA____Mem smt__y smt__a) (smt__TLA____Mem smt__x smt__y) (smt__TLA____Union smt__a)))) :named |UnionIntro|))\n(assert (! (forall ((smt__a Idv) (smt__x Idv)) (! (=> (smt__TLA____Mem smt__x (smt__TLA____Union smt__a)) (exists ((smt__y Idv)) (and (smt__TLA____Mem smt__y smt__a) (smt__TLA____Mem smt__x smt__y)))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____Union smt__a))))) :named |UnionElim|))\n(assert (! (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv)) (! (= (smt__TLA____Mem smt__x (smt__TLA____SetMinus smt__a smt__b)) (and (smt__TLA____Mem smt__x smt__a) (not (smt__TLA____Mem smt__x smt__b)))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____SetMinus smt__a smt__b))) :pattern ((smt__TLA____Mem smt__x smt__a) (smt__TLA____SetMinus smt__a smt__b)) :pattern ((smt__TLA____Mem smt__x smt__b) (smt__TLA____SetMinus smt__a smt__b)))) :named |SetMinusDef|))\n(assert (! (forall ((smt__x Idv)) (! (= (smt__TLA____Mem smt__x smt__TLA____NatSet) (and (smt__TLA____Mem smt__x smt__TLA____IntSet) (smt__TLA____IntLteq (smt__TLA____Cast__Int 0) smt__x))) :pattern ((smt__TLA____Mem smt__x smt__TLA____NatSet)))) :named |NatSetDef|))\n(assert (! (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv)) (! (= (smt__TLA____Mem smt__x (smt__TLA____IntRange smt__a smt__b)) (and (smt__TLA____Mem smt__x smt__TLA____IntSet) (smt__TLA____IntLteq smt__a smt__x) (smt__TLA____IntLteq smt__x smt__b))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____IntRange smt__a smt__b))))) :named |IntRangeDef|))\n(assert (! (forall ((smt__f Idv) (smt__g Idv)) (! (=> (and (smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g) (= (smt__TLA____FunDom smt__f) (smt__TLA____FunDom smt__g)) (forall ((smt__x Idv)) (=> (smt__TLA____Mem smt__x (smt__TLA____FunDom smt__f)) (= (smt__TLA____FunApp smt__f smt__x) (smt__TLA____FunApp smt__g smt__x))))) (= smt__f smt__g)) :pattern ((smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g)))) :named |FunExt|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv)) (! (=> (and (smt__TLA____FunIsafcn smt__s) (>= (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) 0) (forall ((smt__i Idv)) (= (smt__TLA____Mem smt__i (smt__TLA____FunDom smt__s)) (and (smt__TLA____Mem smt__i smt__TLA____IntSet) (<= 1 (smt__TLA____Proj__Int smt__i)) (<= (smt__TLA____Proj__Int smt__i) (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))))) (forall ((smt__i Int)) (=> (and (<= 1 smt__i) (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))) (smt__TLA____Mem (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)) smt__a)))) (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))))) :named |SeqSetIntro|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv)) (! (=> (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (and (smt__TLA____FunIsafcn smt__s) (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (= (smt__TLA____FunDom smt__s) (smt__TLA____IntRange (smt__TLA____Cast__Int 1) (smt__TLA____Len smt__s))))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))))) :named |SetSetElim1|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv) (smt__i Int)) (! (=> (and (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (<= 1 smt__i) (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))) (smt__TLA____Mem (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)) smt__a)) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i))))) :named |SetSetElim2|))\n(assert (! (forall ((smt__s Idv) (smt__z Int)) (=> (and (>= smt__z 0) (= (smt__TLA____FunDom smt__s) (smt__TLA____IntRange (smt__TLA____Cast__Int 1) (smt__TLA____Cast__Int smt__z)))) (= (smt__TLA____Len smt__s) (smt__TLA____Cast__Int smt__z)))) :named |SeqLenDef|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv) (smt__x Int) (smt__y Int)) (! (=> (or (< smt__y smt__x) (and (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (<= 1 smt__x) (<= smt__y (smt__TLA____Proj__Int (smt__TLA____Len smt__s))))) (smt__TLA____Mem (smt__TLA____SubSeq smt__s (smt__TLA____Cast__Int smt__x) (smt__TLA____Cast__Int smt__y)) (smt__TLA____Seq smt__a))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (smt__TLA____SubSeq smt__s (smt__TLA____Cast__Int smt__x) (smt__TLA____Cast__Int smt__y))))) :named |SeqSubseqTyping|))\n(assert (! (forall ((smt__s Idv) (smt__x Int) (smt__y Int)) (! (and (=> (<= smt__x (+ smt__y 1)) (= (smt__TLA____Len (smt__TLA____SubSeq smt__s (smt__TLA____Cast__Int smt__x) (smt__TLA____Cast__Int smt__y))) (smt__TLA____Cast__Int (- (+ smt__y 1) smt__x)))) (=> (> smt__x (+ smt__y 1)) (= (smt__TLA____Len (smt__TLA____SubSeq smt__s (smt__TLA____Cast__Int smt__x) (smt__TLA____Cast__Int smt__y))) (smt__TLA____Cast__Int 0)))) :pattern ((smt__TLA____SubSeq smt__s (smt__TLA____Cast__Int smt__x) (smt__TLA____Cast__Int smt__y))))) :named |SeqSubseqLen|))\n(assert (! (forall ((smt__s Idv) (smt__x Int) (smt__y Int) (smt__z Int)) (! (=> (and (<= 1 smt__x) (<= 1 smt__z) (<= smt__z (- (+ smt__y 1) smt__x))) (= (smt__TLA____FunApp (smt__TLA____SubSeq smt__s (smt__TLA____Cast__Int smt__x) (smt__TLA____Cast__Int smt__y)) (smt__TLA____Cast__Int smt__z)) (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int (- (+ smt__z smt__x) 1))))) :pattern ((smt__TLA____FunApp (smt__TLA____SubSeq smt__s (smt__TLA____Cast__Int smt__x) (smt__TLA____Cast__Int smt__y)) (smt__TLA____Cast__Int smt__z))))) :named |SeqSubseqApp|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(assert (! (forall ((smt__x1 Int)) (! (= (smt__TLA____IntUminus (smt__TLA____Cast__Int smt__x1)) (smt__TLA____Cast__Int (- smt__x1))) :pattern ((smt__TLA____IntUminus (smt__TLA____Cast__Int smt__x1))))) :named |Typing TIntUminus|))\n(assert (! (forall ((smt__x1 Int) (smt__x2 Int)) (! (= (smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2)) (<= smt__x1 smt__x2)) :pattern ((smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2))))) :named |Typing TIntLteq|))\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (= (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y) (= smt__x smt__y)) :pattern ((smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y)))) :named |ExtTrigEqDef Set$Idv$|))\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (smt__TLA____SetExtTrigger smt__x smt__y) :pattern ((smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ smt__x smt__y)))) :named |ExtTrigEqTrigger Idv|))\n(declare-fun smt__S () Idv)\n(assert (! (not (smt__TLA____TrigEq__Setdollarsign__Idvdollarsign__ (smt__TLA____FunDom smt__S) (smt__TLA____Union (smt__TLA____SetMinus smt__S (smt__TLA____SubSeq smt__S (smt__TLA____Cast__Int 1) (smt__TLA____IntUminus (smt__TLA____Cast__Int 2))))))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Times"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Exp"},"args":[{"kind":"Num","integer":"2","fraction":""},{"kind":"Num","integer":"3","fraction":""}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Quotient"},"args":[{"kind":"Num","integer":"7","fraction":""},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Remainder"},"args":[{"kind":"Num","integer":"8","fraction":""},{"kind":"Num","integer":"3","fraction":""}]}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Minus"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Head"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cat"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"BSeq"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"2","fraction":""}]}]}]},{"kind":"Num","integer":"1","fraction":""}]}]}},0,"(set-logic UFNIA)\n(declare-sort Idv 0)\n(declare-fun smt__TLA____BSeq (Idv) Idv)\n(declare-fun smt__TLA____Cast__Int (Int) Idv)\n(declare-fun smt__TLA____Cat (Idv Idv) Idv)\n(declare-fun smt__TLA____FunApp (Idv Idv) Idv)\n(declare-fun smt__TLA____FunDom (Idv) Idv)\n(declare-fun smt__TLA____FunIsafcn (Idv) Bool)\n(declare-fun smt__TLA____Head (Idv) Idv)\n(declare-fun smt__TLA____IntExp (Idv Idv) Idv)\n(declare-fun smt__TLA____IntLteq (Idv Idv) Bool)\n(declare-fun smt__TLA____IntMinus (Idv Idv) Idv)\n(declare-fun smt__TLA____IntQuotient (Idv Idv) Idv)\n(declare-fun smt__TLA____IntRange (Idv Idv) Idv)\n(declare-fun smt__TLA____IntRemainder (Idv Idv) Idv)\n(declare-fun smt__TLA____IntSet () Idv)\n(declare-fun smt__TLA____IntTimes (Idv Idv) Idv)\n(declare-fun smt__TLA____Len (Idv) Idv)\n(declare-fun smt__TLA____Mem (Idv Idv) Bool)\n(declare-fun smt__TLA____NatSet () Idv)\n(declare-fun smt__TLA____Proj__Int (Idv) Int)\n(declare-fun smt__TLA____Seq (Idv) Idv)\n(declare-fun smt__TLA____SetExtTrigger (Idv Idv) Bool)\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (forall ((smt__z Idv)) (= (smt__TLA____Mem smt__z smt__x) (smt__TLA____Mem smt__z smt__y))) (= smt__x smt__y)) :pattern ((smt__TLA____SetExtTrigger smt__x smt__y)))) :named |SetExt|))\n(assert (! (forall ((smt__x Idv)) (! (= (smt__TLA____Mem smt__x smt__TLA____NatSet) (and (smt__TLA____Mem smt__x smt__TLA____IntSet) (smt__TLA____IntLteq (smt__TLA____Cast__Int 0) smt__x))) :pattern ((smt__TLA____Mem smt__x smt__TLA____NatSet)))) :named |NatSetDef|))\n(assert (! (forall ((smt__x Idv) (smt__y Idv)) (! (=> (and (smt__TLA____Mem smt__x smt__TLA____IntSet) (smt__TLA____Mem smt__y smt__TLA____IntSet) (or (distinct smt__x (smt__TLA____Cast__Int 0)) (smt__TLA____IntLteq (smt__TLA____Cast__Int 1) smt__y))) (smt__TLA____Mem (smt__TLA____IntExp smt__x smt__y) smt__TLA____IntSet)) :pattern ((smt__TLA____IntExp smt__x smt__y)))) :named |IntExpTyping|))\n(assert (! (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv)) (! (= (smt__TLA____Mem smt__x (smt__TLA____IntRange smt__a smt__b)) (and (smt__TLA____Mem smt__x smt__TLA____IntSet) (smt__TLA____IntLteq smt__a smt__x) (smt__TLA____IntLteq smt__x smt__b))) :pattern ((smt__TLA____Mem smt__x (smt__TLA____IntRange smt__a smt__b))))) :named |IntRangeDef|))\n(assert (! (forall ((smt__f Idv) (smt__g Idv)) (! (=> (and (smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g) (= (smt__TLA____FunDom smt__f) (smt__TLA____FunDom smt__g)) (forall ((smt__x Idv)) (=> (smt__TLA____Mem smt__x (smt__TLA____FunDom smt__f)) (= (smt__TLA____FunApp smt__f smt__x) (smt__TLA____FunApp smt__g smt__x))))) (= smt__f smt__g)) :pattern ((smt__TLA____FunIsafcn smt__f) (smt__TLA____FunIsafcn smt__g)))) :named |FunExt|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv)) (! (=> (and (smt__TLA____FunIsafcn smt__s) (>= (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) 0) (forall ((smt__i Idv)) (= (smt__TLA____Mem smt__i (smt__TLA____FunDom smt__s)) (and (smt__TLA____Mem smt__i smt__TLA____IntSet) (<= 1 (smt__TLA____Proj__Int smt__i)) (<= (smt__TLA____Proj__Int smt__i) (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))))) (forall ((smt__i Int)) (=> (and (<= 1 smt__i) (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))) (smt__TLA____Mem (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)) smt__a)))) (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))))) :named |SeqSetIntro|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv)) (! (=> (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (and (smt__TLA____FunIsafcn smt__s) (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (= (smt__TLA____FunDom smt__s) (smt__TLA____IntRange (smt__TLA____Cast__Int 1) (smt__TLA____Len smt__s))))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a))))) :named |SetSetElim1|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv) (smt__i Int)) (! (=> (and (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (<= 1 smt__i) (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))) (smt__TLA____Mem (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)) smt__a)) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i))))) :named |SetSetElim2|))\n(assert (! (forall ((smt__s Idv) (smt__z Int)) (=> (and (>= smt__z 0) (= (smt__TLA____FunDom smt__s) (smt__TLA____IntRange (smt__TLA____Cast__Int 1) (smt__TLA____Cast__Int smt__z)))) (= (smt__TLA____Len smt__s) (smt__TLA____Cast__Int smt__z)))) :named |SeqLenDef|))\n(assert (! (forall ((smt__a Idv) (smt__s Idv) (smt__t Idv)) (! (=> (and (smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (smt__TLA____Mem smt__t (smt__TLA____Seq smt__a))) (smt__TLA____Mem (smt__TLA____Cat smt__s smt__t) (smt__TLA____Seq smt__a))) :pattern ((smt__TLA____Mem smt__s (smt__TLA____Seq smt__a)) (smt__TLA____Cat smt__s smt__t)) :pattern ((smt__TLA____Mem smt__t (smt__TLA____Seq smt__a)) (smt__TLA____Cat smt__s smt__t)))) :named |SeqCatTyping|))\n(assert (! (forall ((smt__s Idv) (smt__t Idv)) (! (=> (and (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (smt__TLA____Mem (smt__TLA____Len smt__t) smt__TLA____NatSet)) (= (smt__TLA____Len (smt__TLA____Cat smt__s smt__t)) (smt__TLA____Cast__Int (+ (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) (smt__TLA____Proj__Int (smt__TLA____Len smt__t)))))) :pattern ((smt__TLA____Cat smt__s smt__t)))) :named |SeqCatLen|))\n(assert (! (forall ((smt__s Idv) (smt__t Idv) (smt__i Int)) (! (=> (and (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (smt__TLA____Mem (smt__TLA____Len smt__t) smt__TLA____NatSet) (<= 1 smt__i) (<= smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s)))) (= (smt__TLA____FunApp (smt__TLA____Cat smt__s smt__t) (smt__TLA____Cast__Int smt__i)) (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i)))) :pattern ((smt__TLA____FunApp (smt__TLA____Cat smt__s smt__t) (smt__TLA____Cast__Int smt__i))) :pattern ((smt__TLA____Cat smt__s smt__t) (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int smt__i))))) :named |SeqCatApp1|))\n(assert (! (forall ((smt__s Idv) (smt__t Idv) (smt__i Int)) (! (=> (and (smt__TLA____Mem (smt__TLA____Len smt__s) smt__TLA____NatSet) (smt__TLA____Mem (smt__TLA____Len smt__t) smt__TLA____NatSet) (<= smt__i (+ (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) (smt__TLA____Proj__Int (smt__TLA____Len smt__t)))) (< (smt__TLA____Proj__Int (smt__TLA____Len smt__s)) smt__i)) (= (smt__TLA____FunApp (smt__TLA____Cat smt__s smt__t) (smt__TLA____Cast__Int smt__i)) (smt__TLA____FunApp smt__t (smt__TLA____Cast__Int (- smt__i (smt__TLA____Proj__Int (smt__TLA____Len smt__s))))))) :pattern ((smt__TLA____FunApp (smt__TLA____Cat smt__s smt__t) (smt__TLA____Cast__Int smt__i))))) :named |SeqCatApp2|))\n(assert (! (forall ((smt__s Idv)) (! (= (smt__TLA____Head smt__s) (smt__TLA____FunApp smt__s (smt__TLA____Cast__Int 1))) :pattern ((smt__TLA____Head smt__s)))) :named |SeqHeadDef|))\n(assert (! (forall ((smt__x Int)) (! (= smt__x (smt__TLA____Proj__Int (smt__TLA____Cast__Int smt__x))) :pattern ((smt__TLA____Cast__Int smt__x)))) :named |CastInjAlt Int|))\n(assert (! (forall ((smt__z Int)) (! (smt__TLA____Mem (smt__TLA____Cast__Int smt__z) smt__TLA____IntSet) :pattern ((smt__TLA____Cast__Int smt__z)))) :named |TypeGuardIntro Int|))\n(assert (! (forall ((smt__x Idv)) (! (=> (smt__TLA____Mem smt__x smt__TLA____IntSet) (= smt__x (smt__TLA____Cast__Int (smt__TLA____Proj__Int smt__x)))) :pattern ((smt__TLA____Mem smt__x smt__TLA____IntSet)))) :named |TypeGuardElim Int|))\n(assert (! (forall ((smt__x1 Int) (smt__x2 Int)) (! (= (smt__TLA____IntMinus (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2)) (smt__TLA____Cast__Int (- smt__x1 smt__x2))) :pattern ((smt__TLA____IntMinus (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2))))) :named |Typing TIntMinus|))\n(assert (! (forall ((smt__x1 Int) (smt__x2 Int)) (! (= (smt__TLA____IntTimes (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2)) (smt__TLA____Cast__Int (* smt__x1 smt__x2))) :pattern ((smt__TLA____IntTimes (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2))))) :named |Typing TIntTimes|))\n(assert (! (forall ((smt__x Int) (smt__y Int)) (! (=> (> smt__y 0) (= (smt__TLA____IntQuotient (smt__TLA____Cast__Int smt__x) (smt__TLA____Cast__Int smt__y)) (smt__TLA____Cast__Int (div smt__x smt__y)))) :pattern ((smt__TLA____IntQuotient (smt__TLA____Cast__Int smt__x) (smt__TLA____Cast__Int smt__y))))) :named |Typing TIntQuotient|))\n(assert (! (forall ((smt__x Int) (smt__y Int)) (! (=> (> smt__y 0) (= (smt__TLA____IntRemainder (smt__TLA____Cast__Int smt__x) (smt__TLA____Cast__Int smt__y)) (smt__TLA____Cast__Int (mod smt__x smt__y)))) :pattern ((smt__TLA____IntRemainder (smt__TLA____Cast__Int smt__x) (smt__TLA____Cast__Int smt__y))))) :named |Typing TIntRemainder|))\n(assert (! (forall ((smt__x1 Int) (smt__x2 Int)) (! (= (smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2)) (<= smt__x1 smt__x2)) :pattern ((smt__TLA____IntLteq (smt__TLA____Cast__Int smt__x1) (smt__TLA____Cast__Int smt__x2))))) :named |Typing TIntLteq|))\n(declare-fun smt__S () Idv)\n(assert (! (not (= (smt__TLA____IntTimes (smt__TLA____IntExp (smt__TLA____Cast__Int 2) (smt__TLA____Cast__Int 3)) (smt__TLA____IntQuotient (smt__TLA____Cast__Int 7) (smt__TLA____IntRemainder (smt__TLA____Cast__Int 8) (smt__TLA____Cast__Int 3)))) (smt__TLA____IntMinus (smt__TLA____Head (smt__TLA____Cat smt__S (smt__TLA____BSeq smt__S (smt__TLA____Cast__Int 2)))) (smt__TLA____Cast__Int 1)))) :named |Goal|))\n(check-sat)\n(exit)"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"SortSeq"},"args":[{"kind":"Ix","index":1}]},{"kind":"Ix","index":1}]}},0,"TlaUnsupportedError: the operator SortSeq"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Tsub","modal":"Box","action":{"kind":"Internal","builtin":"TRUE"},"subscript":{"kind":"Ix","index":1}}},0,"TlaUnsupportedError: a temporal formula"],
[0,{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Bang","expression":{"kind":"Ix","index":1},"selectors":[]}},0,"TlaUnsupportedError: the expression Bang"]
]"###;

    fn check_all(cases: &str) {
        for case in parse_json(cases).items() {
            check(case);
        }
    }

    #[test]
    fn encodes_tlapm_obligations_as_the_typescript_does() {
        check_all(TLAPM_CASES);
    }

    #[test]
    fn encodes_constructed_sequents_as_the_typescript_does() {
        check_all(CONSTRUCTED_CASES);
    }
}
