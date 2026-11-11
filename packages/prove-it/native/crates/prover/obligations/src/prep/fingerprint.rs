//! A port of tlapm's Backend.Fingerprints.fp_sequent: the digest of an obligation that names its
//! hypotheses and bound variables by the order of their first use, so two obligations that differ
//! only in names share it. A port of `src/prover/prep/fingerprint.ts`.

use crate::errors::{ObligationError, Result};
use crate::expression::{
    Bound, BoundDomain, Builtin, Bullet, DefnCore, ExceptPoint, Expr, ExprCore, Fairness, HypCore,
    Level, Modal, Quantifier, ScopeRef, Sequent, Time, Visibility, adjoin, to_index,
};
use crate::prep::md5::get_md5;
use crate::temporal::is_constant;

// builtin_to_int, whose numbers skip [], which fp_bin prints by name.
const BUILTIN_NUMBERS: [Builtin; 70] = [
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

fn get_bullet_number(bullet: Bullet) -> usize {
    match bullet {
        Bullet::And => 0,
        Bullet::Or => 1,
        Bullet::Refs => 2,
    }
}

fn get_quantifier_number(quantifier: Quantifier) -> usize {
    match quantifier {
        Quantifier::Forall => 0,
        Quantifier::Exists => 1,
    }
}

fn get_modal_number(modal: Modal) -> usize {
    match modal {
        Modal::Box => 0,
        Modal::Dia => 1,
    }
}

fn get_fairness_number(fairness: Fairness) -> usize {
    match fairness {
        Fairness::Weak => 0,
        Fairness::Strong => 1,
    }
}

// What a stack entry stands for: a hypothesis not yet used, under the label its first use prints,
// one used, numbered, a bound variable not yet used, one used, a pragma, or a hidden fact.
#[derive(Clone, Copy)]
enum Ident {
    Hyp { label: &'static str },
    HypIndex { index: usize },
    Var,
    VarIndex { index: usize },
    Pragma,
    None,
}

struct Entry {
    ident: Ident,
    is_used: bool,
}

struct Counters {
    hyp: usize,
    variable: usize,
}

// OCaml's %S: a string literal, with each byte outside printable ASCII as a decimal escape.
fn quote_string(value: &str) -> String {
    let mut quoted = String::from("\"");
    for byte in value.bytes() {
        match byte {
            0x22 => quoted.push_str("\\\""),
            0x5c => quoted.push_str("\\\\"),
            0x0a => quoted.push_str("\\n"),
            0x09 => quoted.push_str("\\t"),
            0x0d => quoted.push_str("\\r"),
            0x08 => quoted.push_str("\\b"),
            byte if !(0x20..=0x7e).contains(&byte) => quoted.push_str(&format!("\\{byte:03}")),
            byte => quoted.push(char::from(byte)),
        }
    }
    quoted.push('"');
    quoted
}

fn get_builtin(builtin: Builtin) -> String {
    match builtin {
        Builtin::BoxTrue => "$Box".to_owned(),
        Builtin::BoxFalse => "$FakeBox".to_owned(),
        _ => match BUILTIN_NUMBERS.iter().position(|entry| *entry == builtin) {
            Some(number) => format!("${number}"),
            None => "$-1".to_owned(),
        },
    }
}

fn get_fresh_label(level: Level) -> &'static str {
    match level {
        Level::Unknown => "Unknown",
        Level::Constant => "CONSTANT",
        Level::State => "STATE",
        Level::Action => "ACTION",
        Level::Temporal => "TEMPORAL",
    }
}

fn get_variable_number(entry: Option<&Entry>) -> Result<usize> {
    match entry.map(|entry| entry.ident) {
        Some(Ident::VarIndex { index }) => Ok(index),
        Some(Ident::Var) => Ok(0),
        _ => Err(ObligationError::assert_failure()),
    }
}

fn get_hyp_number(entry: &Entry) -> Result<usize> {
    match entry.ident {
        Ident::HypIndex { index } => Ok(index),
        _ => Err(ObligationError::assert_failure()),
    }
}

fn get_numbers(entries: &[Entry]) -> Result<String> {
    let mut text = String::new();
    for entry in entries {
        text.push_str(&format!("{}.", get_variable_number(Some(entry))?));
    }
    Ok(text)
}

/// A binder's body, then what pops off the stack after it.
struct BoundText {
    text: String,
    entries: Vec<Entry>,
}

// fp_sequent's text for an obligation, before its digest.
struct Printer {
    stack: Vec<Entry>,
}

impl Printer {
    fn get_entry(&mut self, index: isize) -> Result<&mut Entry> {
        usize::try_from(to_index(self.stack.len()) - index)
            .ok()
            .and_then(|position| self.stack.get_mut(position))
            .ok_or_else(ObligationError::assert_failure)
    }

    fn push(&mut self, ident: Ident) {
        self.stack.push(Entry {
            ident,
            is_used: false,
        });
    }

    fn pop(&mut self) -> Result<Entry> {
        self.stack.pop().ok_or_else(ObligationError::assert_failure)
    }

    // Stack.popn: the entries from the top down.
    fn pop_variables(&mut self, count: usize) -> Result<Vec<Entry>> {
        (0..count).map(|_| self.pop()).collect()
    }

    fn print_list(&mut self, counters: &mut Counters, items: &[Expr]) -> Result<String> {
        let texts = items
            .iter()
            .map(|item| self.print_expr(counters, item))
            .collect::<Result<Vec<_>>>()?;
        Ok(texts.join(","))
    }

    // fp_bounds pairs each bound with an entry, and prints those with a domain.
    fn print_bounds(
        &mut self,
        counters: &mut Counters,
        entries: &[Entry],
        bounds: &[Bound],
    ) -> Result<String> {
        let mut text = String::new();
        for (index, bound) in bounds.iter().enumerate() {
            if let BoundDomain::Domain(domain) = &bound.domain {
                let number = get_variable_number(entries.get(index))?;
                let domain = self.print_expr(counters, domain)?;
                text.push_str(&format!("{number}:{domain},"));
            }
        }
        Ok(text)
    }

    // A binder's body comes first, then what pops off the stack after it.
    fn print_bound(
        &mut self,
        counters: &mut Counters,
        count: usize,
        body: &Expr,
    ) -> Result<BoundText> {
        for _ in 0..count {
            self.push(Ident::Var);
        }
        let text = self.print_expr(counters, body)?;
        Ok(BoundText {
            text,
            entries: self.pop_variables(count)?,
        })
    }

    fn print_expr(&mut self, counters: &mut Counters, expression: &Expr) -> Result<String> {
        Ok(match &expression.core {
            ExprCore::Ix { index } => {
                let entry = self.get_entry(*index)?;
                entry.is_used = true;
                match entry.ident {
                    Ident::None => format!("$V({index}SHOULD_NOT_APPEAR)"),
                    Ident::Hyp { label } => {
                        let number = counters.hyp;
                        counters.hyp += 1;
                        entry.ident = Ident::HypIndex { index: number };
                        format!("${label}({number})")
                    }
                    Ident::Var => {
                        let number = counters.variable;
                        counters.variable += 1;
                        entry.ident = Ident::VarIndex { index: number };
                        format!("$PRM({number})")
                    }
                    Ident::HypIndex { index } => format!("$HYP({index})"),
                    Ident::VarIndex { index } => format!("$PRM({index})"),
                    Ident::Pragma => String::new(),
                }
            }
            ExprCore::Opaque { name } => name.clone(),
            ExprCore::Internal { builtin } => get_builtin(*builtin),
            ExprCore::Lambda { params, body } => {
                let mut bound = self.print_bound(counters, params.len(), body)?;
                bound.entries.reverse();
                format!("$Lam({}{})", get_numbers(&bound.entries)?, bound.text)
            }
            ExprCore::Sequent { sequent } => self.print_sequent(sequent)?,
            ExprCore::Apply { operator, args } => {
                if let ExprCore::Ix { index } = operator.core
                    && matches!(self.get_entry(index)?.ident, Ident::Pragma)
                {
                    return Ok(String::new());
                }
                let operator = self.print_expr(counters, operator)?;
                let args = self.print_list(counters, args)?;
                format!("$OpApp({operator};{args})")
            }
            ExprCore::With { expression, .. } | ExprCore::Parens { expression, .. } => {
                self.print_expr(counters, expression)?
            }
            ExprCore::If {
                condition,
                consequent,
                alternative,
            } => {
                let condition = self.print_expr(counters, condition)?;
                let consequent = self.print_expr(counters, consequent)?;
                let alternative = self.print_expr(counters, alternative)?;
                format!("$If({condition},{consequent},{alternative})")
            }
            ExprCore::List { bullet, items } => {
                let items = self.print_list(counters, items)?;
                format!("$List({};{items})", get_bullet_number(*bullet))
            }
            ExprCore::Let { definitions, body } => {
                let mut texts = String::new();
                for definition in definitions {
                    let (DefnCore::Operator { body, .. } | DefnCore::Bpragma { body, .. }) =
                        &definition.core
                    else {
                        return Err(ObligationError::assert_failure());
                    };
                    texts.push_str(&self.print_expr(counters, body)?);
                    texts.push('.');
                    self.push(Ident::Var);
                }
                let body = self.print_expr(counters, body)?;
                self.pop_variables(definitions.len())?;
                format!("{texts}{body}")
            }
            // fp_expr pairs a quantifier's bounds with its variables from the last one down.
            ExprCore::Quant {
                quantifier,
                bounds,
                body,
            } => {
                let bound = self.print_bound(counters, bounds.len(), body)?;
                let domains = self.print_bounds(counters, &bound.entries, bounds)?;
                format!(
                    "$Quant({};{domains}.{})",
                    get_quantifier_number(*quantifier),
                    bound.text
                )
            }
            ExprCore::Tquant {
                quantifier,
                names,
                body,
            } => {
                let mut bound = self.print_bound(counters, names.len(), body)?;
                bound.entries.reverse();
                format!(
                    "$Tquant({}{}{})",
                    get_quantifier_number(*quantifier),
                    get_numbers(&bound.entries)?,
                    bound.text
                )
            }
            ExprCore::Choose { domain, body, .. } => {
                let bound = self.print_bound(counters, 1, body)?;
                let number = get_variable_number(bound.entries.first())?;
                match domain {
                    Some(domain) => {
                        let domain = self.print_expr(counters, domain)?;
                        format!("$Bch({number}:{domain};{})", bound.text)
                    }
                    None => format!("$Ch({number}:{})", bound.text),
                }
            }
            ExprCore::SetSt { domain, body, .. } => {
                let bound = self.print_bound(counters, 1, body)?;
                let number = get_variable_number(bound.entries.first())?;
                let domain = self.print_expr(counters, domain)?;
                format!("$SSt({number}:{domain};{})", bound.text)
            }
            ExprCore::SetOf { element, bounds } => {
                let mut bound = self.print_bound(counters, bounds.len(), element)?;
                bound.entries.reverse();
                let domains = self.print_bounds(counters, &bound.entries, bounds)?;
                format!("$Sof({domains}.{})", bound.text)
            }
            ExprCore::Fcn { bounds, body } => {
                let mut bound = self.print_bound(counters, bounds.len(), body)?;
                bound.entries.reverse();
                let domains = self.print_bounds(counters, &bound.entries, bounds)?;
                format!("$Fcn({domains}.{})", bound.text)
            }
            ExprCore::SetEnum { elements } => {
                format!("$Set({})", self.print_list(counters, elements)?)
            }
            ExprCore::Tuple { elements } => {
                format!("$Tup({})", self.print_list(counters, elements)?)
            }
            ExprCore::Product { factors } => {
                format!("$Prod({})", self.print_list(counters, factors)?)
            }
            ExprCore::FcnApp { function, args } => {
                let function = self.print_expr(counters, function)?;
                let args = self.print_list(counters, args)?;
                format!("$FcnApp({function};{args})")
            }
            ExprCore::Arrow { domain, range } => {
                let domain = self.print_expr(counters, domain)?;
                let range = self.print_expr(counters, range)?;
                format!("$Arrow({domain},{range})")
            }
            ExprCore::Rect { fields } | ExprCore::Record { fields } => {
                let kind = if matches!(expression.core, ExprCore::Rect { .. }) {
                    "Rect"
                } else {
                    "Record"
                };
                let mut texts = Vec::new();
                for field in fields {
                    let value = self.print_expr(counters, &field.value)?;
                    texts.push(format!("({},{value})", field.name));
                }
                format!("${kind}({})", texts.join(","))
            }
            ExprCore::Except { function, specs } => {
                let base = self.print_expr(counters, function)?;
                let mut texts = Vec::new();
                for spec in specs {
                    let mut trail = String::new();
                    for point in &spec.trail {
                        trail.push('.');
                        match point {
                            ExceptPoint::Dot(field) => trail.push_str(field),
                            ExceptPoint::Apply(inner) => {
                                trail.push_str(&self.print_expr(counters, inner)?);
                            }
                        }
                    }
                    let value = self.print_expr(counters, &spec.value)?;
                    texts.push(format!("({trail}={value})"));
                }
                format!("$Except({base},{})", texts.join(","))
            }
            ExprCore::Dot { expression, field } => {
                format!("$Dot({},{field})", self.print_expr(counters, expression)?)
            }
            ExprCore::Sub {
                modal,
                action,
                subscript,
            }
            | ExprCore::Tsub {
                modal,
                action,
                subscript,
            } => {
                let kind = if matches!(expression.core, ExprCore::Sub { .. }) {
                    "Sub"
                } else {
                    "Tsub"
                };
                let action = self.print_expr(counters, action)?;
                let subscript = self.print_expr(counters, subscript)?;
                format!("${kind}({},{action},{subscript})", get_modal_number(*modal))
            }
            ExprCore::Fair {
                fairness,
                subscript,
                action,
            } => {
                let subscript = self.print_expr(counters, subscript)?;
                let action = self.print_expr(counters, action)?;
                format!(
                    "$Fair({},{subscript},{action})",
                    get_fairness_number(*fairness)
                )
            }
            ExprCore::Case { arms, other } => {
                let mut texts = Vec::new();
                for arm in arms {
                    let condition = self.print_expr(counters, &arm.condition)?;
                    let body = self.print_expr(counters, &arm.body)?;
                    texts.push(format!("({condition},{body})"));
                }
                let other = match other {
                    Some(other) => self.print_expr(counters, other)?,
                    None => String::new(),
                };
                format!("$Case({},{other})", texts.join(","))
            }
            ExprCore::String { value } => quote_string(value),
            ExprCore::Num { integer, fraction } => format!("$Num({integer},{fraction})"),
            ExprCore::At { .. } => "$At".to_owned(),
            ExprCore::Bang { .. } => return Err(ObligationError::assert_failure()),
        })
    }

    /// Pushes the hypothesis, prints the rest of the sequent after it, and pops it.
    fn get_rest(
        &mut self,
        counters: &mut Counters,
        sequent: &Sequent,
        index: usize,
        scope: &ScopeRef,
        ident: Ident,
    ) -> Result<(String, Entry)> {
        self.push(ident);
        let rest = self.spin(counters, sequent, index + 1, scope)?;
        Ok((rest, self.pop()?))
    }

    fn spin(
        &mut self,
        counters: &mut Counters,
        sequent: &Sequent,
        index: usize,
        scope: &ScopeRef,
    ) -> Result<String> {
        let Some(hyp) = sequent.context.get(index) else {
            return Ok(format!(
                "$Goal({})",
                self.print_expr(counters, &sequent.active)?
            ));
        };
        let next_scope = adjoin(scope, hyp);
        Ok(match &hyp.core {
            HypCore::Fresh {
                name,
                level,
                domain: None,
                ..
            } => {
                let label = get_fresh_label(*level);
                let (rest, entry) =
                    self.get_rest(counters, sequent, index, &next_scope, Ident::Hyp { label })?;
                if entry.is_used {
                    format!("{rest}{label}{name}")
                } else {
                    rest
                }
            }
            HypCore::Fresh {
                domain: Some(domain),
                domain_visibility,
                ..
            } => {
                let (rest, entry) = self.get_rest(
                    counters,
                    sequent,
                    index,
                    &next_scope,
                    Ident::Hyp { label: "CON" },
                )?;
                if *domain_visibility == Visibility::Hidden {
                    return Ok(rest);
                }
                let number = if entry.is_used {
                    get_hyp_number(&entry)?.to_string()
                } else {
                    "_".to_owned()
                };
                let domain = self.print_expr(counters, domain)?;
                format!("{rest}$Dom({number};{domain})")
            }
            HypCore::Flex { .. } => {
                self.get_rest(
                    counters,
                    sequent,
                    index,
                    &next_scope,
                    Ident::Hyp { label: "VAR" },
                )?
                .0
            }
            HypCore::Defn {
                definition,
                visibility,
                ..
            } => match &definition.core {
                DefnCore::Recursive { .. } => {
                    self.get_rest(
                        counters,
                        sequent,
                        index,
                        &next_scope,
                        Ident::Hyp { label: "CON" },
                    )?
                    .0
                }
                DefnCore::Bpragma { .. } => {
                    self.get_rest(counters, sequent, index, &next_scope, Ident::Pragma)?
                        .0
                }
                DefnCore::Instance { .. } => return Err(ObligationError::assert_failure()),
                DefnCore::Operator { body, .. } => {
                    let (rest, entry) = self.get_rest(
                        counters,
                        sequent,
                        index,
                        &next_scope,
                        Ident::Hyp { label: "HYP" },
                    )?;
                    if !entry.is_used {
                        return Ok(rest);
                    }
                    let number = get_hyp_number(&entry)?;
                    if *visibility == Visibility::Hidden {
                        let level = if is_constant(scope, body) { 0 } else { 3 };
                        format!("{rest}$Def({number},{level})")
                    } else {
                        let body = self.print_expr(counters, body)?;
                        format!("{rest}$Def({number};{body})")
                    }
                }
            },
            HypCore::Fact {
                expression,
                visibility,
                time,
                ..
            } => {
                if *visibility == Visibility::Hidden {
                    return Ok(self
                        .get_rest(counters, sequent, index, &next_scope, Ident::None)?
                        .0);
                }
                let (rest, _) = self.get_rest(
                    counters,
                    sequent,
                    index,
                    &next_scope,
                    Ident::Hyp { label: "HYP" },
                )?;
                let expression = self.print_expr(counters, expression)?;
                let time = match time {
                    Time::Now => "now",
                    Time::Always => "always",
                };
                format!("{rest}$Fact({expression},{time})")
            }
        })
    }

    // Each hypothesis prints after the goal and the hypotheses after it, once their uses have
    // numbered it.
    fn print_sequent(&mut self, sequent: &Sequent) -> Result<String> {
        let mut counters = Counters {
            hyp: 1,
            variable: 1,
        };
        self.spin(&mut counters, sequent, 0, &None)
    }
}

/// fingerprint: the hex digest of an obligation's fp_sequent text.
pub fn get_fingerprint(sequent: &Sequent) -> Result<String> {
    let mut printer = Printer { stack: Vec::new() };
    Ok(get_md5(&printer.print_sequent(sequent)?))
}

#[cfg(test)]
pub(crate) mod tests {
    //! A reader for sequents as the TypeScript's `JSON.stringify` prints them, without locations,
    //! which the tests of this module and the other Prep modules share. Their expected values come
    //! from running the TypeScript under Bun on the same sequents.

    use std::rc::Rc;

    use super::*;
    use crate::expression::{
        CaseArm, Defn, ExceptSpec, ExprNode, Field, Hyp, HypNode, InstanceDefinition, Param,
        ParenForm, Selector, Substitution, WhereDefined, XlabelIndex,
    };
    use crate::pragma::OldMethod;

    enum Json {
        Null,
        Bool(bool),
        Number(f64),
        String(String),
        Array(Vec<Json>),
        Object(Vec<(String, Json)>),
    }

    struct Reader<'a> {
        bytes: &'a [u8],
        position: usize,
    }

    impl Reader<'_> {
        fn peek(&mut self) -> u8 {
            while self.bytes[self.position].is_ascii_whitespace() {
                self.position += 1;
            }
            self.bytes[self.position]
        }

        fn expect(&mut self, byte: u8) {
            assert_eq!(self.peek(), byte, "at {}", self.position);
            self.position += 1;
        }

        fn read_string(&mut self) -> String {
            self.expect(b'"');
            let mut units: Vec<u16> = Vec::new();
            loop {
                let byte = self.bytes[self.position];
                self.position += 1;
                match byte {
                    b'"' => break,
                    b'\\' => {
                        let escape = self.bytes[self.position];
                        self.position += 1;
                        match escape {
                            b'n' => units.push(0x0a),
                            b't' => units.push(0x09),
                            b'r' => units.push(0x0d),
                            b'b' => units.push(0x08),
                            b'f' => units.push(0x0c),
                            b'u' => {
                                let hex = std::str::from_utf8(
                                    &self.bytes[self.position..self.position + 4],
                                )
                                .unwrap();
                                self.position += 4;
                                units.push(u16::from_str_radix(hex, 16).unwrap());
                            }
                            other => units.push(u16::from(other)),
                        }
                    }
                    _ => {
                        let start = self.position - 1;
                        while self.bytes[self.position] >= 0x80
                            && std::str::from_utf8(&self.bytes[start..self.position]).is_err()
                        {
                            self.position += 1;
                        }
                        let text = std::str::from_utf8(&self.bytes[start..self.position]).unwrap();
                        units.extend(text.encode_utf16());
                    }
                }
            }
            String::from_utf16(&units).unwrap()
        }

        fn read_items(&mut self, close: u8, mut read_item: impl FnMut(&mut Self)) {
            self.position += 1;
            if self.peek() == close {
                self.position += 1;
                return;
            }
            loop {
                read_item(self);
                if self.peek() == b',' {
                    self.position += 1;
                } else {
                    self.expect(close);
                    return;
                }
            }
        }

        fn read(&mut self) -> Json {
            match self.peek() {
                b'{' => {
                    let mut entries = Vec::new();
                    self.read_items(b'}', |reader| {
                        let key = reader.read_string();
                        reader.expect(b':');
                        entries.push((key, reader.read()));
                    });
                    Json::Object(entries)
                }
                b'[' => {
                    let mut items = Vec::new();
                    self.read_items(b']', |reader| items.push(reader.read()));
                    Json::Array(items)
                }
                b'"' => Json::String(self.read_string()),
                b't' => {
                    self.position += 4;
                    Json::Bool(true)
                }
                b'f' => {
                    self.position += 5;
                    Json::Bool(false)
                }
                b'n' => {
                    self.position += 4;
                    Json::Null
                }
                _ => {
                    let start = self.position;
                    while self.bytes.get(self.position).is_some_and(|byte| {
                        byte.is_ascii_digit() || matches!(byte, b'-' | b'+' | b'.' | b'e' | b'E')
                    }) {
                        self.position += 1;
                    }
                    let text = std::str::from_utf8(&self.bytes[start..self.position]).unwrap();
                    Json::Number(text.parse().unwrap())
                }
            }
        }
    }

    fn read_json(text: &str) -> Json {
        Reader {
            bytes: text.as_bytes(),
            position: 0,
        }
        .read()
    }

    impl Json {
        fn get(&self, key: &str) -> Option<&Json> {
            let Json::Object(entries) = self else {
                panic!("not an object");
            };
            entries
                .iter()
                .find(|entry| entry.0 == key)
                .map(|entry| &entry.1)
                .filter(|value| !matches!(value, Json::Null))
        }

        fn field(&self, key: &str) -> &Json {
            self.get(key).unwrap_or_else(|| panic!("no {key}"))
        }

        fn text(&self, key: &str) -> String {
            match self.field(key) {
                Json::String(text) => text.clone(),
                _ => panic!("{key} is not a string"),
            }
        }

        fn number(&self, key: &str) -> f64 {
            match self.field(key) {
                Json::Number(number) => *number,
                _ => panic!("{key} is not a number"),
            }
        }

        fn count(&self, key: &str) -> usize {
            self.number(key) as usize
        }

        fn flag(&self, key: &str) -> bool {
            matches!(self.get(key), Some(Json::Bool(true)))
        }

        fn items(&self, key: &str) -> &[Json] {
            match self.field(key) {
                Json::Array(items) => items,
                _ => panic!("{key} is not an array"),
            }
        }

        fn kind(&self) -> String {
            self.text("kind")
        }
    }

    fn get_builtin_named(name: &str) -> Builtin {
        BUILTIN_NUMBERS
            .iter()
            .chain(&[Builtin::BoxTrue, Builtin::BoxFalse])
            .copied()
            .find(|builtin| builtin.name() == name)
            .unwrap_or_else(|| panic!("no builtin {name}"))
    }

    fn get_level(name: &str) -> Level {
        match name {
            "Constant" => Level::Constant,
            "State" => Level::State,
            "Action" => Level::Action,
            "Temporal" => Level::Temporal,
            _ => Level::Unknown,
        }
    }

    fn get_visibility(name: &str) -> Visibility {
        if name == "Hidden" {
            Visibility::Hidden
        } else {
            Visibility::Visible
        }
    }

    fn get_time(name: &str) -> Time {
        if name == "Always" {
            Time::Always
        } else {
            Time::Now
        }
    }

    fn get_quantifier(name: &str) -> Quantifier {
        if name == "Exists" {
            Quantifier::Exists
        } else {
            Quantifier::Forall
        }
    }

    fn get_modal(name: &str) -> Modal {
        if name == "Dia" {
            Modal::Dia
        } else {
            Modal::Box
        }
    }

    fn to_exprs(items: &[Json]) -> Vec<Expr> {
        items.iter().map(to_expr).collect()
    }

    fn to_names(items: &[Json]) -> Vec<String> {
        items
            .iter()
            .map(|item| match item {
                Json::String(text) => text.clone(),
                _ => panic!("not a name"),
            })
            .collect()
    }

    fn to_bounds(items: &[Json]) -> Vec<Bound> {
        items
            .iter()
            .map(|item| {
                let domain = item.field("domain");
                Bound {
                    name: item.text("name"),
                    level: get_level(&item.text("level")),
                    domain: match domain.kind().as_str() {
                        "Domain" => BoundDomain::Domain(to_expr(domain.field("expression"))),
                        "Ditto" => BoundDomain::Ditto,
                        _ => BoundDomain::NoDomain,
                    },
                }
            })
            .collect()
    }

    fn to_fields(items: &[Json]) -> Vec<Field> {
        items
            .iter()
            .map(|item| Field {
                name: item.text("name"),
                value: to_expr(item.field("value")),
            })
            .collect()
    }

    fn to_defn(value: &Json) -> Defn {
        let name = value.text("name");
        let core = match value.kind().as_str() {
            "Recursive" => DefnCore::Recursive {
                name,
                shape: value.count("shape"),
            },
            "Operator" => DefnCore::Operator {
                name,
                body: to_expr(value.field("body")),
            },
            "Instance" => {
                let instance = value.field("instance");
                DefnCore::Instance {
                    name,
                    instance: InstanceDefinition {
                        args: to_names(instance.items("args")),
                        module: instance.text("module"),
                        substitutions: instance
                            .items("substitutions")
                            .iter()
                            .map(|item| Substitution {
                                name: item.text("name"),
                                expression: to_expr(item.field("expression")),
                            })
                            .collect(),
                        location: None,
                    },
                }
            }
            // The pragma's methods take no part in what the Prep modules tested here compute.
            _ => DefnCore::Bpragma {
                name,
                body: to_expr(value.field("body")),
                methods: Vec::new(),
            },
        };
        Defn {
            core,
            location: None,
        }
    }

    fn to_hyp(value: &Json) -> Hyp {
        let core = match value.kind().as_str() {
            "Fresh" => HypCore::Fresh {
                name: value.text("name"),
                shape: value.count("shape"),
                level: get_level(&value.text("level")),
                domain: value.get("domain").map(to_expr),
                domain_visibility: get_visibility(&value.text("domainVisibility")),
            },
            "Flex" => HypCore::Flex {
                name: value.text("name"),
            },
            "Defn" => HypCore::Defn {
                definition: to_defn(value.field("definition")),
                where_defined: match value.field("whereDefined") {
                    Json::String(text) if text == "Builtin" => WhereDefined::Builtin,
                    Json::String(_) => WhereDefined::User,
                    proof => WhereDefined::Proof(get_time(&proof.text("time"))),
                },
                visibility: get_visibility(&value.text("visibility")),
                is_local: value.flag("isLocal"),
                is_constness_unset: value.flag("isConstnessUnset"),
            },
            _ => HypCore::Fact {
                expression: to_expr(value.field("expression")),
                visibility: get_visibility(&value.text("visibility")),
                time: get_time(&value.text("time")),
                use_location: None,
            },
        };
        Rc::new(HypNode {
            core,
            location: None,
        })
    }

    fn to_sequent(value: &Json) -> Sequent {
        Sequent {
            context: value.items("context").iter().map(to_hyp).collect(),
            active: to_expr(value.field("active")),
        }
    }

    fn to_expr(value: &Json) -> Expr {
        let core = match value.kind().as_str() {
            "Ix" => ExprCore::Ix {
                index: value.number("index") as isize,
            },
            "Opaque" => ExprCore::Opaque {
                name: value.text("name"),
            },
            "Internal" => ExprCore::Internal {
                builtin: get_builtin_named(&value.text("builtin")),
            },
            "Lambda" => ExprCore::Lambda {
                params: value
                    .items("params")
                    .iter()
                    .map(|param| Param {
                        name: param.text("name"),
                        shape: param.count("shape"),
                        location: None,
                    })
                    .collect(),
                body: to_expr(value.field("body")),
            },
            "Sequent" => ExprCore::Sequent {
                sequent: to_sequent(value.field("sequent")),
            },
            "Bang" => ExprCore::Bang {
                expression: to_expr(value.field("expression")),
                selectors: value
                    .items("selectors")
                    .iter()
                    .map(|selector| match selector.kind().as_str() {
                        "Down" => Selector::Down,
                        "Number" => Selector::Number(selector.count("value") as i64),
                        "Left" => Selector::Left,
                        "Right" => Selector::Right,
                        "At" => Selector::At,
                        "Instance" => Selector::Instance(to_exprs(selector.items("args"))),
                        _ => Selector::Label {
                            label: selector.text("label"),
                            args: to_exprs(selector.items("args")),
                        },
                    })
                    .collect(),
            },
            "Apply" => ExprCore::Apply {
                operator: to_expr(value.field("operator")),
                args: to_exprs(value.items("args")),
            },
            // Only the method's name: the rest takes no part in what these modules compute.
            "With" => ExprCore::With {
                expression: to_expr(value.field("expression")),
                method: OldMethod {
                    name: value.field("method").text("name"),
                    tactic: None,
                    timeout: None,
                },
            },
            "If" => ExprCore::If {
                condition: to_expr(value.field("condition")),
                consequent: to_expr(value.field("consequent")),
                alternative: to_expr(value.field("alternative")),
            },
            "List" => ExprCore::List {
                bullet: match value.text("bullet").as_str() {
                    "And" => Bullet::And,
                    "Or" => Bullet::Or,
                    _ => Bullet::Refs,
                },
                items: to_exprs(value.items("items")),
            },
            "Let" => ExprCore::Let {
                definitions: value.items("definitions").iter().map(to_defn).collect(),
                body: to_expr(value.field("body")),
            },
            "Quant" => ExprCore::Quant {
                quantifier: get_quantifier(&value.text("quantifier")),
                bounds: to_bounds(value.items("bounds")),
                body: to_expr(value.field("body")),
            },
            "Tquant" => ExprCore::Tquant {
                quantifier: get_quantifier(&value.text("quantifier")),
                names: to_names(value.items("names")),
                body: to_expr(value.field("body")),
            },
            "Choose" => ExprCore::Choose {
                name: value.text("name"),
                domain: value.get("domain").map(to_expr),
                body: to_expr(value.field("body")),
            },
            "SetSt" => ExprCore::SetSt {
                name: value.text("name"),
                domain: to_expr(value.field("domain")),
                body: to_expr(value.field("body")),
            },
            "SetOf" => ExprCore::SetOf {
                element: to_expr(value.field("element")),
                bounds: to_bounds(value.items("bounds")),
            },
            "SetEnum" => ExprCore::SetEnum {
                elements: to_exprs(value.items("elements")),
            },
            "Product" => ExprCore::Product {
                factors: to_exprs(value.items("factors")),
            },
            "Tuple" => ExprCore::Tuple {
                elements: to_exprs(value.items("elements")),
            },
            "Fcn" => ExprCore::Fcn {
                bounds: to_bounds(value.items("bounds")),
                body: to_expr(value.field("body")),
            },
            "FcnApp" => ExprCore::FcnApp {
                function: to_expr(value.field("function")),
                args: to_exprs(value.items("args")),
            },
            "Arrow" => ExprCore::Arrow {
                domain: to_expr(value.field("domain")),
                range: to_expr(value.field("range")),
            },
            "Rect" => ExprCore::Rect {
                fields: to_fields(value.items("fields")),
            },
            "Record" => ExprCore::Record {
                fields: to_fields(value.items("fields")),
            },
            "Except" => ExprCore::Except {
                function: to_expr(value.field("function")),
                specs: value
                    .items("specs")
                    .iter()
                    .map(|spec| ExceptSpec {
                        trail: spec
                            .items("trail")
                            .iter()
                            .map(|point| match point.kind().as_str() {
                                "Dot" => ExceptPoint::Dot(point.text("field")),
                                _ => ExceptPoint::Apply(to_expr(point.field("expression"))),
                            })
                            .collect(),
                        value: to_expr(spec.field("value")),
                    })
                    .collect(),
            },
            "Dot" => ExprCore::Dot {
                expression: to_expr(value.field("expression")),
                field: value.text("field"),
            },
            "Sub" => ExprCore::Sub {
                modal: get_modal(&value.text("modal")),
                action: to_expr(value.field("action")),
                subscript: to_expr(value.field("subscript")),
            },
            "Tsub" => ExprCore::Tsub {
                modal: get_modal(&value.text("modal")),
                action: to_expr(value.field("action")),
                subscript: to_expr(value.field("subscript")),
            },
            "Fair" => ExprCore::Fair {
                fairness: if value.text("fairness") == "Strong" {
                    Fairness::Strong
                } else {
                    Fairness::Weak
                },
                subscript: to_expr(value.field("subscript")),
                action: to_expr(value.field("action")),
            },
            "Case" => ExprCore::Case {
                arms: value
                    .items("arms")
                    .iter()
                    .map(|arm| CaseArm {
                        condition: to_expr(arm.field("condition")),
                        body: to_expr(arm.field("body")),
                    })
                    .collect(),
                other: value.get("other").map(to_expr),
            },
            "String" => ExprCore::String {
                value: value.text("value"),
            },
            "Num" => ExprCore::Num {
                integer: value.text("integer"),
                fraction: value.text("fraction"),
            },
            "At" => ExprCore::At {
                is_except: value.flag("isExcept"),
            },
            "Parens" => {
                let form = value.field("form");
                ExprCore::Parens {
                    expression: to_expr(value.field("expression")),
                    form: match form.kind().as_str() {
                        "Nlabel" => ParenForm::Nlabel {
                            label: form.text("label"),
                            names: to_names(form.items("names")),
                        },
                        "Xlabel" => ParenForm::Xlabel {
                            label: form.text("label"),
                            indices: form
                                .items("indices")
                                .iter()
                                .map(|index| XlabelIndex {
                                    name: index.text("name"),
                                    index: index.count("index"),
                                })
                                .collect(),
                        },
                        _ => ParenForm::Syntax,
                    },
                }
            }
            other => panic!("unknown kind {other}"),
        };
        Rc::new(ExprNode {
            core,
            location: None,
            is_atomic: value.flag("isAtomic"),
        })
    }

    /// A sequent from the JSON the TypeScript prints for it.
    pub(crate) fn parse_sequent(text: &str) -> Sequent {
        to_sequent(&read_json(text))
    }

    /// An outcome as the TypeScript scripts print it: `ok`, or `name|message|exception`.
    pub(crate) fn describe<Value>(result: Result<Value>) -> String {
        match result {
            Ok(_) => "ok".to_owned(),
            Err(error) => {
                let exception = match &error {
                    ObligationError::Proof { exception, .. } => exception.as_str(),
                    _ => "",
                };
                format!("{}|{}|{exception}", error.name(), error.message())
            }
        }
    }

    fn get_fingerprint_outcome(sequent: &Sequent) -> String {
        get_fingerprint(sequent).unwrap_or_else(|error| describe::<()>(Err(error)))
    }

    /// Checks each case: the expected outcomes as JSON on one line, then the sequent on the next.
    pub(crate) fn check_cases(text: &str) -> usize {
        let lines = text
            .lines()
            .filter(|line| !line.is_empty())
            .collect::<Vec<_>>();
        let mut failures = Vec::new();
        for pair in lines.chunks(2) {
            let expected = read_json(pair[0]);
            let sequent = parse_sequent(pair[1]);
            let outcomes = [
                ("fp", get_fingerprint_outcome(&sequent)),
                (
                    "lc",
                    describe(crate::prep::level_comparison::check_level_change(&sequent)),
                ),
                (
                    "ea",
                    describe(crate::prep::enabled_axioms::implication_to_enabled(
                        &sequent,
                    )),
                ),
            ];
            for (name, actual) in outcomes {
                if let Some(Json::String(wanted)) = expected.get(name)
                    && *wanted != actual
                {
                    failures.push(format!("{name}: {wanted} != {actual}\n{}", pair[1]));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "{} failures:\n{}",
            failures.len(),
            failures
                .iter()
                .take(10)
                .cloned()
                .collect::<Vec<_>>()
                .join("\n")
        );
        lines.len() / 2
    }

    /// Each case: the outcomes `fingerprint.ts`, `level-comparison.ts` and `enabled-axioms.ts`
    /// give, then the sequent, from handwritten sequents of every form and obligations of tlapm's
    /// tests.
    const CASES: &str = r##"
{"fp":"89b94dbc59b2ff31da91da96fb58617d","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[],"active":{"kind":"Internal","builtin":"TRUE"}}
{"fp":"a15a72aa4c25a1ab76d004b0653c8f56","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[],"active":{"kind":"String","value":"a\"b\\c\nd\te\rf\bg\u0001h é ∀ 😀 ~"}}
{"fp":"7a7d3e32df1cb8ae36bbc04c54a62336","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"x","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"y","shape":0,"level":"State","domainVisibility":"Visible"},{"kind":"Fresh","name":"z","shape":0,"level":"Unknown","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Ix","index":1}]}}
{"fp":"92f0d6570252d5fd442697cedcfbfced","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"x","shape":0,"level":"Constant","domain":{"kind":"Ix","index":1},"domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}
{"fp":"8f72d3968811c439bae4cdd52b0e41d7","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"x","shape":0,"level":"Constant","domain":{"kind":"Ix","index":1},"domainVisibility":"Hidden"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}
{"fp":"94e622b884620fe09946112f7f8af889","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"x","shape":0,"level":"Constant","domain":{"kind":"Ix","index":1},"domainVisibility":"Visible"}],"active":{"kind":"Internal","builtin":"TRUE"}}
{"fp":"ad28a97a5825f4951252f5171a3ce5ca","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"v"},{"kind":"Defn","definition":{"kind":"Operator","name":"A","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}},"whereDefined":"User","visibility":"Visible","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"B","body":{"kind":"Ix","index":2}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Defn","definition":{"kind":"Operator","name":"C","body":{"kind":"Opaque","name":"k"}},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":3}]}]}}
{"fp":"8c95b06b1e907b584e1fd6105e32c0e6","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Defn","definition":{"kind":"Bpragma","name":"P","body":{"kind":"Internal","builtin":"TRUE"},"methods":[]},"whereDefined":"User","visibility":"Visible","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Internal","builtin":"TRUE"}]}}
{"fp":"8c95b06b1e907b584e1fd6105e32c0e6","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Defn","definition":{"kind":"Bpragma","name":"P","body":{"kind":"Internal","builtin":"TRUE"},"methods":[]},"whereDefined":"User","visibility":"Visible","isLocal":false}],"active":{"kind":"Ix","index":1}}
{"fp":"54c51ccdc0066085c9a30cf8ce315819","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Defn","definition":{"kind":"Recursive","name":"R","shape":1},"whereDefined":"User","visibility":"Visible","isLocal":false}],"active":{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":1}]}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Defn","definition":{"kind":"Instance","name":"I","instance":{"args":[],"module":"M","substitutions":[]}},"whereDefined":"User","visibility":"Visible","isLocal":false}],"active":{"kind":"Internal","builtin":"TRUE"}}
{"fp":"2d8dc1049299aff82549e7ee9bbe35e1","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Hidden","time":"Now"}],"active":{"kind":"Ix","index":1}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Opaque","name":"a"},{"kind":"Opaque","name":"b"}]},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Internal","builtin":"FALSE"},"visibility":"Visible","time":"Now"}],"active":{"kind":"Ix","index":0}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[],"active":{"kind":"Ix","index":-2}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"x","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Ix","index":2}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[],"active":{"kind":"Bang","expression":{"kind":"Opaque","name":"a"},"selectors":[]}}
{"fp":"635be4d779a8643e3bc342ee7e592863","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"a","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":1}}},{"name":"b","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"c","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":1}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Ix","index":1}]}}}
{"fp":"d781594507bff388c3c0d7f6a7bce035","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Lambda","params":[{"name":"p","shape":0},{"name":"q","shape":1}],"body":{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":2}]}}}
{"fp":"3aed2f1237eb5c838520bc0198e4cbfe","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Tquant","quantifier":"Forall","names":["u","w"],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}}
{"fp":"a300ff04157a884944de96684f7bfda7","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Choose","name":"c","domain":{"kind":"Ix","index":1},"body":{"kind":"Ix","index":1}},{"kind":"Choose","name":"c","body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}]}}
{"fp":"db30621e83cab8dc7472bd8694b42e69","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"SetSt","name":"s","domain":{"kind":"Ix","index":1},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]}}}
{"fp":"d0c180f35ecd1042bf2eebc91f73514a","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"SetOf","element":{"kind":"Tuple","elements":[{"kind":"Ix","index":1},{"kind":"Ix","index":2}]},"bounds":[{"name":"a","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":1}}},{"name":"b","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":1}}}]}}
{"fp":"ebe1d0acece0c943652d7f8b64496929","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Fcn","bounds":[{"name":"a","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":1}}},{"name":"b","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":1}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":1}]}}}
{"fp":"9e660edbbe67d7e10a6ab3b3a41d4145","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Let","definitions":[{"kind":"Operator","name":"L","body":{"kind":"Ix","index":1}},{"kind":"Bpragma","name":"M","body":{"kind":"Ix","index":2},"methods":[]}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":3}]}}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[],"active":{"kind":"Let","definitions":[{"kind":"Recursive","name":"L","shape":0}],"body":{"kind":"Internal","builtin":"TRUE"}}}
{"fp":"32d4c361bbc8f5a91a796bbaec88040b","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"f","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Except","function":{"kind":"Ix","index":1},"specs":[{"trail":[{"kind":"Dot","field":"a"},{"kind":"Apply","expression":{"kind":"Num","integer":"1","fraction":"5"}}],"value":{"kind":"At","isExcept":true}}]}}
{"fp":"2033b606c8aea5cbda0013b61364da6a","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"r","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Record","fields":[{"name":"b","value":{"kind":"Ix","index":1}},{"name":"a","value":{"kind":"String","value":"x"}}]}}
{"fp":"64615dca22992099cf4d506a15fce00c","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"r","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Rect","fields":[{"name":"b","value":{"kind":"Ix","index":1}}]}}
{"fp":"d954647af2d880b8843e64c908c0b258","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"v"}],"active":{"kind":"Sub","modal":"Dia","action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},"subscript":{"kind":"Ix","index":1}}}
{"fp":"abc788eca7a9efdb39bf3adabdee3d13","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"v"}],"active":{"kind":"Tsub","modal":"Box","action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},"subscript":{"kind":"Ix","index":1}}}
{"fp":"069ec9a65e94b9dfa505e622862b4f1d","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"v"}],"active":{"kind":"Fair","fairness":"Strong","subscript":{"kind":"Ix","index":1},"action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}}}
{"fp":"09a8c324733704e1b3032f8d738d0831","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"p","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Case","arms":[{"condition":{"kind":"Ix","index":1},"body":{"kind":"Opaque","name":"a"}},{"condition":{"kind":"Internal","builtin":"TRUE"},"body":{"kind":"Opaque","name":"b"}}]}}
{"fp":"748a02d76b9e751411110f8ca6de1630","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"p","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Case","arms":[{"condition":{"kind":"Ix","index":1},"body":{"kind":"Opaque","name":"a"}}],"other":{"kind":"Opaque","name":"c"}}}
{"fp":"406e8c1e76bb67712672904c63cd24ea","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"p","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"If","condition":{"kind":"Ix","index":1},"consequent":{"kind":"SetEnum","elements":[]},"alternative":{"kind":"Product","factors":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]}}}
{"fp":"c7ab18fcb0d8c679e6a6707cd944336b","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"p","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"List","bullet":"Or","items":[{"kind":"Ix","index":1},{"kind":"Dot","expression":{"kind":"Ix","index":1},"field":"f"}]}}
{"fp":"88369db519a3461cd6059b6a474509e6","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"p","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"FcnApp","function":{"kind":"Ix","index":1},"args":[{"kind":"Ix","index":1},{"kind":"Arrow","domain":{"kind":"Internal","builtin":"Nat"},"range":{"kind":"Internal","builtin":"BoxTrue"}}]}}
{"fp":"9c86c7c3ee3f012302fa1b64f3e6c85f","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"p","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"With","expression":{"kind":"Parens","expression":{"kind":"Ix","index":1},"form":{"kind":"Syntax"}},"method":{"name":"cooper"}}}
{"fp":"18d69f58744af2b28c30b411879e8ade","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"p","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"q","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Ix","index":1},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":2},{"kind":"Ix","index":3}]}}},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Ix","index":2},{"kind":"Internal","builtin":"BoxFalse"}]}}
{"fp":"f9d3bed193d02fd089d168f992a741a5","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"FcnApp","function":{"kind":"FcnApp","function":{"kind":"Except","function":{"kind":"Fcn","bounds":[{"name":"x","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"SetEnum","elements":[{"kind":"Num","integer":"1","fraction":""}]}}}],"body":{"kind":"Fcn","bounds":[{"name":"y","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"SetEnum","elements":[{"kind":"Num","integer":"2","fraction":""}]}}}],"body":{"kind":"Num","integer":"3","fraction":""}}},"specs":[{"trail":[{"kind":"Apply","expression":{"kind":"Num","integer":"1","fraction":""}}],"value":{"kind":"Except","function":{"kind":"FcnApp","function":{"kind":"Fcn","bounds":[{"name":"x","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"SetEnum","elements":[{"kind":"Num","integer":"1","fraction":""}]}}}],"body":{"kind":"Fcn","bounds":[{"name":"y","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"SetEnum","elements":[{"kind":"Num","integer":"2","fraction":""}]}}}],"body":{"kind":"Num","integer":"3","fraction":""}}},"args":[{"kind":"Num","integer":"1","fraction":""}]},"specs":[{"trail":[{"kind":"Apply","expression":{"kind":"Num","integer":"2","fraction":""}}],"value":{"kind":"Num","integer":"1","fraction":""}}]}}]},"args":[{"kind":"Num","integer":"1","fraction":""}]},"args":[{"kind":"Num","integer":"2","fraction":""}]},{"kind":"Num","integer":"1","fraction":""}]}}
{"fp":"592c6a82c0c0d426a070cd0c2c8ce8c6","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Defn","definition":{"kind":"Bpragma","name":"M!SMT","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"smt3"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Ix","index":1},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
{"fp":"38e25fe83619a963fff5421b184569e7","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Defn","definition":{"kind":"Operator","name":"M!Foo","body":{"kind":"Lambda","params":[{"name":"x","shape":0}],"body":{"kind":"Ix","index":1}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Hidden","time":"Always"},{"kind":"Defn","definition":{"kind":"Operator","name":"<1>1","body":{"kind":"List","bullet":"Refs","items":[]}},"whereDefined":{"kind":"Proof","time":"Always"},"visibility":"Visible","isLocal":true},{"kind":"Fact","expression":{"kind":"Ix","index":1},"visibility":"Hidden","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":4},"args":[{"kind":"Internal","builtin":"TRUE"}]},{"kind":"Apply","operator":{"kind":"Ix","index":4},"args":[{"kind":"Internal","builtin":"TRUE"}]}]},"time":"Always"}
{"fp":"32e75b71917693cd0b0d96630c6b2103","lc":"ok","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Defn","definition":{"kind":"Operator","name":"F","body":{"kind":"Lambda","params":[{"name":"a","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Num","integer":"2","fraction":""}]},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Ix","index":3}]},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":4},{"kind":"Ix","index":4}]},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":5},{"kind":"Ix","index":5}]},"visibility":"Visible","time":"Always"},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Visible","time":"Always"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":7},{"kind":"Ix","index":7}]}}
{"fp":"c8804d351125b398d2d6fbce078ed179","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"List","bullet":"Refs","items":[]},"visibility":"Hidden","time":"Always"},{"kind":"Fresh","name":"f","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"List","bullet":"Refs","items":[]},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"Internal","builtin":"TRUE"},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"List","bullet":"Refs","items":[]},"visibility":"Hidden","time":"Always"}],"active":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"x","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":8}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neq"},"args":[{"kind":"FcnApp","function":{"kind":"Ix","index":6},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Unprimable"},"args":[{"kind":"SetSt","name":"z","domain":{"kind":"Ix","index":9},"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Notmem"},"args":[{"kind":"Ix","index":1},{"kind":"FcnApp","function":{"kind":"Ix","index":7},"args":[{"kind":"Ix","index":1}]}]}}]}]}}}
{"fp":"8c95b06b1e907b584e1fd6105e32c0e6","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Defn","definition":{"kind":"Bpragma","name":"M!SMT","body":{"kind":"Internal","builtin":"TRUE"},"methods":[[{"hint":"prover","value":{"kind":"String","value":"smt3"}}]]},"whereDefined":"User","visibility":"Hidden","isLocal":false}],"active":{"kind":"Ix","index":1}}
{"fp":"f7130f4e2db1b14c60a3e008babd3ffd","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Internal","builtin":"TRUE"},"action":{"kind":"Internal","builtin":"TRUE"}},{"kind":"Fair","fairness":"Weak","subscript":{"kind":"Internal","builtin":"TRUE"},"action":{"kind":"Internal","builtin":"TRUE"}}]}}
{"fp":"74099cb156180247d9686b087f494f2d","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"f","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"A","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"SUBSET"},"args":[{"kind":"Ix","index":2}]}}}],"body":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"x","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":3}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neq"},"args":[{"kind":"FcnApp","function":{"kind":"Ix","index":3},"args":[{"kind":"Ix","index":1}]},{"kind":"Ix","index":2}]}}}}}},"visibility":"Visible","time":"Always"}],"active":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"f","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"A","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"SUBSET"},"args":[{"kind":"Ix","index":2}]}}}],"body":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"x","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":3}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neq"},"args":[{"kind":"FcnApp","function":{"kind":"Ix","index":3},"args":[{"kind":"Ix","index":1}]},{"kind":"Ix","index":2}]}}}}}}}
{"fp":"5a625e44f4d242557eb2e3e69ecc7741","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Fact","expression":{"kind":"Sequent","sequent":{"context":[{"kind":"Fresh","name":"S","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fresh","name":"f","shape":0,"level":"Constant","domainVisibility":"Visible"}],"active":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"A","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"SUBSET"},"args":[{"kind":"Ix","index":2}]}}}],"body":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"x","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":3}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neq"},"args":[{"kind":"FcnApp","function":{"kind":"Ix","index":3},"args":[{"kind":"Ix","index":1}]},{"kind":"Ix","index":2}]}}}}},"visibility":"Visible","time":"Always"}],"active":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"S","level":"Constant","domain":{"kind":"NoDomain"}},{"name":"f","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"A","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"SUBSET"},"args":[{"kind":"Ix","index":2}]}}}],"body":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"x","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":3}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Neq"},"args":[{"kind":"FcnApp","function":{"kind":"Ix","index":3},"args":[{"kind":"Ix","index":1}]},{"kind":"Ix","index":2}]}}}}}
{"fp":"1f752508ddc5c722a0fd0c580cb820df","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"v"},{"kind":"Defn","definition":{"kind":"Operator","name":"I","body":{"kind":"Quant","quantifier":"Forall","bounds":[{"name":"y","level":"Constant","domain":{"kind":"Domain","expression":{"kind":"Ix","index":1}}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":1},{"kind":"Ix","index":1}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Ix","index":1},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}}
{"fp":"121ca41029078600f4ed7af9fb5fec39","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Defn","definition":{"kind":"Operator","name":"F","body":{"kind":"Lambda","params":[{"name":"a","shape":0}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Plus"},"args":[{"kind":"Ix","index":1},{"kind":"Num","integer":"1","fraction":""}]}}},"whereDefined":"User","visibility":"Hidden","isLocal":false},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Ix","index":1},"args":[{"kind":"Num","integer":"1","fraction":""}]},{"kind":"Num","integer":"2","fraction":""}]},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":3},{"kind":"Ix","index":3}]},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":4},{"kind":"Ix","index":4}]},"visibility":"Hidden","time":"Always"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Ix","index":5},{"kind":"Ix","index":5}]},"visibility":"Visible","time":"Always"}],"active":{"kind":"Internal","builtin":"TRUE"}}
"##;

    #[test]
    fn matches_the_typescript() {
        assert_eq!(check_cases(CASES), 49);
    }
}
