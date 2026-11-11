//! TLC's dumps of a counterexample, the value `[counterexample |-> CounterExample, vars |-> vars]`
//! of `_TLCTrace.tla` and `_JsonTrace.tla`: serialized by `ValueOutputStream` and gzipped for
//! `-dumpTrace tlc` and the trace exploration spec's `<Spec>_TTrace_<epoch>.bin`
//! (`_TLCTrace.ioSerialize`), and written as JSON for `-dumpTrace json` (`Json.serialize`).
//!
//! The serialization writes a value TLC wrote before as a back-reference to it
//! (`ValueOutputStream.put`), and TLC tells by the identity of its Java objects, so the dump
//! follows the sharing of the evaluator's values: one `Rc` is one object. Each `UniqueString`
//! carries TLC's token, its global intern number in one run, which no other run can reproduce and
//! which TLC's reader skips (`UniqueString.readExternal`): the dump numbers each text in the order
//! it first writes it.

use std::collections::HashMap;
use std::rc::Rc;

use crate::alias::Alias;
use crate::deflate::{crc32, deflate};
use crate::print::{format_value, print_order};
use crate::rebuild::{Rebuilder, run};
use crate::value::{Class, Text, Value, elements, set_of, settle};
use crate::{CounterExample, Unsupported};

// `ValueConstants`.
const BOOLVALUE: u8 = 0;
const INTVALUE: u8 = 1;
const STRINGVALUE: u8 = 3;
const RECORDVALUE: u8 = 4;
const SETENUMVALUE: u8 = 5;
const TUPLEVALUE: u8 = 7;
const FCNRCDVALUE: u8 = 9;
const MODELVALUE: u8 = 21;
const INTERVALVALUE: u8 = 23;
const DUMMYVALUE: u8 = 26;

fn unsupported<T>(reason: impl std::fmt::Display) -> Result<T, Unsupported> {
    Err(Unsupported(format!("a dumped trace {reason}")))
}

/// A counterexample as TLC's trace modules dump it.
pub struct TraceDump {
    counter_example: Value,
    /// `UNION { DOMAIN trace[i] : i \in DOMAIN trace }`, of strings TLC makes for it.
    vars: Value,
    counter_example_field: Rc<Text>,
    vars_field: Rc<Text>,
    /// The names of the state variables in TLC's order, the slot each one's text carries
    /// (`UniqueString.getVarLoc`).
    variables: Vec<Box<[u16]>>,
}

impl Rebuilder<'_> {
    /// What TLC's trace modules dump of a violation's counterexample, as its postconditions read
    /// it: for an invariant violation, `counter_example.trace` from
    /// [`Rebuilder::rebuild_counter_example`], through the ALIAS for a safety violation, as TLC
    /// builds it. With `is_sharing_followed` the dump shares
    /// each value TLC shares, as a file written byte for byte needs, and declines where the
    /// evaluator doesn't; without it, as for TLC's binary trace file, which a reader that rebuilds
    /// the same trace from it matches (AGENTS.md, "The oracle"), it writes a value TLC shares as
    /// many times as the evaluator made it.
    pub fn dump_trace(
        &mut self,
        counter_example: &CounterExample<'_>,
        is_sharing_followed: bool,
        is_initial: bool,
    ) -> Result<TraceDump, Unsupported> {
        let ir = self.evaluator().ir;
        // TLC's worker builds a safety violation's counterexample from the ALIAS of each state
        // (`Worker.doPostCondition`), whose records the dump follows only where it needn't share
        // values as TLC does; an initial state's violation, `is_initial`, from the state itself
        // (`ModelChecker.doInit`'s `new CounterExample(errState)`).
        let aliases = if counter_example.cycle.is_none() && !is_initial && ir.model.alias.is_some()
        {
            if is_sharing_followed {
                return unsupported("of a model with an ALIAS");
            }
            self.alias(counter_example.trace, None, None, false)?
        } else {
            None
        };
        if let Some(reason) = self.evaluator().unshared.filter(|_| is_sharing_followed) {
            return unsupported(reason);
        }
        let value = self.counter_example_value(
            counter_example,
            aliases.as_deref(),
            true,
            is_sharing_followed,
        )?;
        let evaluator = self.evaluator();
        let variables: Vec<Box<[u16]>> = ir
            .tlc_order
            .iter()
            .map(|&variable| ir.get_text_units(ir.variables[variable as usize]).into())
            .collect();
        let variable_names = || {
            variables
                .iter()
                .map(|name| Value::Str(evaluator.text_of(name.clone())))
                .collect::<Vec<_>>()
        };
        // `UNION { DOMAIN trace[i] : i \in DOMAIN trace }`: each state's record has the variables
        // as its domain, or the fields of its ALIAS, which DOMAIN makes strings of.
        let vars: Vec<Value> = match &aliases {
            _ if counter_example.trace.states.is_empty() => Vec::new(),
            None => variable_names(),
            Some(aliases) => aliases
                .iter()
                .flat_map(|alias| match alias {
                    Alias::Record(fields) => fields
                        .iter()
                        .map(|(name, _)| {
                            Value::Str(evaluator.text_of(name.encode_utf16().collect()))
                        })
                        .collect(),
                    Alias::State => variable_names(),
                })
                .collect(),
        };
        Ok(TraceDump {
            counter_example: value,
            vars: run(set_of(vars))?,
            counter_example_field: evaluator.counterexample_field("counterexample", true),
            vars_field: evaluator.counterexample_field("vars", true),
            variables,
        })
    }
}

impl TraceDump {
    /// The file `-dumpTrace tlc` writes, as the trace exploration spec's `.bin` is: the value
    /// fingerprinted, which sorts it in place as TLC's does, so a JSON dump after it writes it
    /// sorted; then serialized and gzipped. `model_values` are the configuration's model values in
    /// the order TLC makes them (`ModelValue.make` as `ModelConfig.parse` reads them), whose
    /// position TLC writes for each.
    pub fn to_tlc(&self, model_values: &[&str]) -> Result<Vec<u8>, Unsupported> {
        // The record the trace module builds, a new one each time.
        let value = run(Value::record(vec![
            (
                Rc::clone(&self.counter_example_field),
                self.counter_example.clone(),
            ),
            (Rc::clone(&self.vars_field), self.vars.clone()),
        ]))?;
        settle(&value);
        let mut writer = Writer {
            bytes: Vec::new(),
            handles: 0,
            objects: HashMap::new(),
            names: HashMap::new(),
            tokens: HashMap::new(),
            variables: &self.variables,
            model_values: model_values
                .iter()
                .map(|name| name.encode_utf16().collect())
                .collect(),
        };
        writer.value(&value)?;
        Ok(gzip(&writer.bytes))
    }

    /// The file `-dumpTrace json` writes (`Json.serialize`, with Gson's `JsonElement.toString`):
    /// records and functions in the order written until TLC sorts them, sets sorted.
    pub fn to_json(&self) -> Result<String, Unsupported> {
        let mut out = String::new();
        out.push_str("{\"counterexample\":");
        json_value(&self.counter_example, &mut out)?;
        out.push_str(",\"vars\":");
        json_value(&self.vars, &mut out)?;
        out.push('}');
        Ok(out)
    }
}

// `ValueOutputStream` over `BufferedDataOutputStream`: big-endian, with its table of the objects
// written (`HandleTable`).
struct Writer<'a> {
    bytes: Vec<u8>,
    handles: usize,
    /// The handle of each value written, by the address of its `Rc`.
    objects: HashMap<usize, usize>,
    /// The handle of each record field's name written, by its text: TLC interns a name.
    names: HashMap<Box<[u16]>, usize>,
    tokens: HashMap<Box<[u16]>, i32>,
    variables: &'a [Box<[u16]>],
    model_values: Vec<Vec<u16>>,
}

impl Writer<'_> {
    // `ValueOutputStream.put`: the handle of an object written before, or else a new one.
    fn put(&mut self, address: usize) -> Option<usize> {
        if let Some(&handle) = self.objects.get(&address) {
            return Some(handle);
        }
        self.objects.insert(address, self.handles);
        self.handles += 1;
        None
    }

    fn short(&mut self, value: i16) {
        self.bytes.extend(value.to_be_bytes());
    }

    fn int(&mut self, value: i32) {
        self.bytes.extend(value.to_be_bytes());
    }

    // `writeNat`.
    fn nat(&mut self, value: usize) -> Result<(), Unsupported> {
        let Ok(value) = i32::try_from(value) else {
            return unsupported("of a value too large to write");
        };
        if value > 0x7fff {
            self.int(-value);
        } else {
            self.short(value as i16);
        }
        Ok(())
    }

    fn handle(&mut self, handle: usize) -> Result<(), Unsupported> {
        self.bytes.push(DUMMYVALUE);
        self.nat(handle)
    }

    fn length(&mut self, length: usize) -> Result<(), Unsupported> {
        let Ok(length) = i32::try_from(length) else {
            return unsupported("of a value too large to write");
        };
        self.int(length);
        Ok(())
    }

    // `UniqueString.write`: its token, the slot of the variable it names or -1, its length, and
    // each unit's low byte (`String.getBytes`).
    fn unique(&mut self, units: &[u16]) -> Result<(), Unsupported> {
        let next = self.tokens.len() as i32;
        let token = *self.tokens.entry(units.into()).or_insert(next);
        let slot = self
            .variables
            .iter()
            .position(|variable| **variable == *units)
            .map_or(-1, |slot| slot as i32);
        self.int(token);
        self.int(slot);
        self.length(units.len())?;
        self.bytes.extend(units.iter().map(|&unit| unit as u8));
        Ok(())
    }

    fn value(&mut self, value: &Value) -> Result<(), Unsupported> {
        match value {
            Value::Bool(boolean) => self.bytes.extend([BOOLVALUE, u8::from(*boolean)]),
            Value::Int(int) => {
                self.bytes.push(INTVALUE);
                self.int(*int);
            }
            Value::Str(text) => match self.put(Rc::as_ptr(text) as usize) {
                Some(handle) => self.handle(handle)?,
                None => {
                    self.bytes.push(STRINGVALUE);
                    self.unique(&text.units)?;
                }
            },
            Value::Model(text) => {
                let Some(index) = self
                    .model_values
                    .iter()
                    .position(|name| **name == *text.units)
                    .and_then(|index| i16::try_from(index).ok())
                else {
                    return unsupported("of a model value the configuration doesn't make");
                };
                self.bytes.push(MODELVALUE);
                self.short(index);
            }
            Value::Interval(low, high) => {
                self.bytes.push(INTERVALVALUE);
                self.int(*low);
                self.int(*high);
            }
            Value::Set(elements) => match self.put(Rc::as_ptr(elements) as usize) {
                Some(handle) => self.handle(handle)?,
                None => {
                    self.bytes.push(SETENUMVALUE);
                    self.length(elements.len())?;
                    for element in elements.iter() {
                        self.value(element)?;
                    }
                }
            },
            Value::Function(function) => {
                if let Some(handle) = self.put(Rc::as_ptr(function) as usize) {
                    return self.handle(handle);
                }
                match function.class.get() {
                    Class::Tuple => {
                        self.bytes.push(TUPLEVALUE);
                        self.nat(function.range.len())?;
                    }
                    Class::Record => {
                        self.bytes.push(RECORDVALUE);
                        self.length(function.domain.len())?;
                        for (key, value) in function.domain.iter().zip(&function.range) {
                            let Value::Str(name) = key else {
                                return unsupported("of a record with a field that isn't a name");
                            };
                            match self.names.get(&name.units) {
                                Some(&handle) => self.handle(handle)?,
                                None => {
                                    self.names.insert(name.units.clone(), self.handles);
                                    self.handles += 1;
                                    self.bytes.push(STRINGVALUE);
                                    self.unique(&name.units)?;
                                }
                            }
                            self.value(value)?;
                        }
                        return Ok(());
                    }
                    Class::Plain | Class::Lambda => {
                        self.bytes.push(FCNRCDVALUE);
                        self.nat(function.range.len())?;
                        match function.interval {
                            Some((low, high)) => {
                                self.bytes.push(0);
                                self.int(low);
                                self.int(high);
                            }
                            None => {
                                self.bytes.push(1);
                                for (key, value) in function.domain.iter().zip(&function.range) {
                                    self.value(key)?;
                                    self.value(value)?;
                                }
                                return Ok(());
                            }
                        }
                    }
                }
                for value in &function.range {
                    self.value(value)?;
                }
            }
            Value::Unsorted(_) => return unsupported("of a set TLC fails to normalize"),
            Value::Lazy(_) | Value::Lambda(_) => {
                return unsupported("of a set or function TLC keeps lazy");
            }
        }
        Ok(())
    }
}

/// A gzip file of `payload` as `java.util.zip.GZIPOutputStream` writes it: its header, zlib's
/// deflate stream at the default level, and its trailer.
fn gzip(payload: &[u8]) -> Vec<u8> {
    let mut out = vec![0x1f, 0x8b, 8, 0, 0, 0, 0, 0, 0, 0xff];
    out.extend(deflate(payload));
    out.extend(crc32(payload).to_le_bytes());
    out.extend((payload.len() as u32).to_le_bytes());
    out
}

fn json_value(value: &Value, out: &mut String) -> Result<(), Unsupported> {
    match value {
        Value::Bool(boolean) => out.push_str(if *boolean { "true" } else { "false" }),
        Value::Int(int) => out.push_str(&int.to_string()),
        Value::Str(text) | Value::Model(text) => json_string(&text.units, out),
        Value::Set(_) | Value::Interval(..) => {
            let elements = run(elements(value))?;
            json_array(elements.iter(), out)?;
        }
        Value::Lazy(lazy) if !lazy.is_overridden() => {
            let elements = run(elements(value))?;
            json_array(elements.iter(), out)?;
        }
        Value::Function(function) => {
            // TLC writes a function as an array where its domain is 1..n, which it sorts to find
            // out where every key is an integer (`isValidSequence`).
            let is_numbered = function.class.get() != Class::Record
                && function
                    .domain
                    .iter()
                    .all(|key| matches!(key, Value::Int(_)));
            let is_sequence = function.class.get() == Class::Tuple
                || is_numbered
                    && (1..)
                        .zip(&function.domain)
                        .all(|(position, key)| matches!(key, Value::Int(int) if *int == position));
            if is_sequence {
                return json_array(function.range.iter(), out);
            }
            if is_numbered {
                function.written.borrow_mut().take();
            }
            let order = print_order(function, false);
            // A JSON object keeps a key's first place and its last value.
            // Keys stay UTF-16, as Java's do, so an unpaired surrogate is neither merged with
            // another key nor written but as `json_string` writes it.
            let mut fields: Vec<(Vec<u16>, String)> = Vec::with_capacity(order.len());
            for position in order {
                let key = match &function.domain[position] {
                    Value::Str(text) => text.units.to_vec(),
                    key => format_value(key).encode_utf16().collect(),
                };
                let mut field = String::new();
                json_value(&function.range[position], &mut field)?;
                match fields.iter_mut().find(|(name, _)| *name == key) {
                    Some(entry) => entry.1 = field,
                    None => fields.push((key, field)),
                }
            }
            out.push('{');
            for (position, (key, field)) in fields.iter().enumerate() {
                if position > 0 {
                    out.push(',');
                }
                json_string(key, out);
                out.push(':');
                out.push_str(field);
            }
            out.push('}');
        }
        Value::Unsorted(_) => return unsupported("of a set TLC fails to normalize"),
        Value::Lazy(_) | Value::Lambda(_) => {
            return unsupported("of a set or function TLC can't write as JSON");
        }
    }
    Ok(())
}

fn json_array<'a>(
    values: impl Iterator<Item = &'a Value>,
    out: &mut String,
) -> Result<(), Unsupported> {
    out.push('[');
    for (position, value) in values.enumerate() {
        if position > 0 {
            out.push(',');
        }
        json_value(value, out)?;
    }
    out.push(']');
    Ok(())
}

// Gson's `JsonWriter.string`, not HTML-safe: a lone surrogate is written as `?`, as the file's
// UTF-8 encoder replaces it.
fn json_string(units: &[u16], out: &mut String) {
    out.push('"');
    for item in char::decode_utf16(units.iter().copied()) {
        match item {
            Ok('"') => out.push_str("\\\""),
            Ok('\\') => out.push_str("\\\\"),
            Ok('\t') => out.push_str("\\t"),
            Ok('\u{8}') => out.push_str("\\b"),
            Ok('\n') => out.push_str("\\n"),
            Ok('\r') => out.push_str("\\r"),
            Ok('\u{c}') => out.push_str("\\f"),
            Ok(character @ ('\0'..='\u{1f}' | '\u{2028}' | '\u{2029}')) => {
                out.push_str(&format!("\\u{:04x}", character as u32));
            }
            Ok(character) => out.push(character),
            Err(_) => out.push('?'),
        }
    }
    out.push('"');
}
