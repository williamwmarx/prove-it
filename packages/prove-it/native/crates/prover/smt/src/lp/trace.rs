//! The LP call trace, written from Rust as `src/prover/smt/solver/lp-trace.ts` writes it from
//! TypeScript (design/prover.md, P3b-lp): that file's header specifies the format. With
//! `PROVE_IT_LP_TRACE` naming a directory, each SMT decision writes
//! `<dir>/<first 16 hex digits of the input text's SHA-256>.lptrace`, one JSON line per event, the
//! same text the TypeScript writes for the same events, so that `tests/lp_trace_diff.rs` can
//! compare the traces of the two theories and `tests/lp_trace.rs` can replay either.
//!
//! What to record (the TypeScript's proxies decide it there; the Rust theory does it by hand, at
//! the places theory-lra*.ts reaches lp, which the TypeScript header lists):
//! - every call the theory makes into lp directly, never one lp makes itself;
//! - every callback lp makes into the theory, with the theory's answer, but not one made while
//!   the theory answers another;
//! - every field of an lp object the theory reads or writes.
//!
//! Tracing off costs a branch: the theory holds an `Option<LpTrace>` (or, when lp's callbacks
//! record too, an `Option<Rc<RefCell<LpTrace>>>` that the callback closures and hosts clone), and
//! builds no value, runs no encoder and allocates nothing unless it is `Some`. Every recording
//! takes the values already encoded, so each call site encodes inside the `Some` branch only:
//!
//! ```ignore
//! let id = trace.as_mut().map(|trace| {
//!     trace.new_object("lar", |id| vec![get_callback(&format!("{id}.new.0"))])
//! });
//! // A call: its line first, as the callbacks it makes come after it, then what it returned.
//! let call = trace.as_mut().map(|trace| {
//!     trace.call(&lar_id, "addVar", vec![get_number(external), Json::Bool(is_int)])
//! });
//! let column = lar.add_var(external, is_int);
//! if let (Some(trace), Some(call)) = (trace.as_mut(), call) {
//!     trace.returned(call, Some(get_number(column)));
//! }
//! // A callback, in the closure lp calls, once the theory has its answer.
//! if let Some(trace) = &trace {
//!     trace.borrow_mut().callback(&name, Vec::new(), Some(Json::Bool(is_canceled)));
//! }
//! // A field read.
//! if let Some(trace) = trace.as_mut() {
//!     trace.read(&lar_id, "status", Json::Number(f64::from(lar.status)));
//! }
//! ```
//!
//! Values are encoded as the TypeScript serializes them, by the `get_*` functions below: a number
//! as itself (`usize::MAX`, `NULL_LPVAR`, as -1), a Rational `"n"` or `"n/d"`, an Impq `["x","y"]`,
//! a LarTerm, an Explanation, a Dependency, an algebraic number and the nla records as the
//! TypeScript object of their fields, a function the theory passes as `{"cb":name}` and an lp
//! object as `{"ref":id}`. A method that returns `undefined` in TypeScript records `None`, which
//! leaves out the `"r"` field.
//!
//! On `wasm32-unknown-unknown`, where `std::env` and `std::fs` compile but fail at run time,
//! `open` returns `None`: there is no trace.

use std::fs::{self, File};
use std::io::{self, BufWriter, Write as _};
use std::path::Path;

use prove_num::Rational;

use crate::lp::bound_propagator::ImpliedBound;
use crate::lp::dependency::{Dependency, linearize};
use crate::lp::explanation::Explanation;
use crate::lp::int_solver::LiaMove;
use crate::lp::json::Json;
use crate::lp::lar_solver::BoundInfo;
use crate::lp::lar_term::LarTerm;
use crate::lp::nla_core::{NlaEquality, NlaFixedEquality};
use crate::lp::nla_types::{Ineq, Lemma};
use crate::lp::numeric_pair::Impq;
use crate::nlsat::algebraic::{Anum, AnumValue};
use crate::nlsat::mpbq::Mpbq;
use crate::util::error::SmtError;
use crate::util::lbool::LBool;

// The lines kept before they are written, past which a finished call writes them.
const FLUSH_SIZE: usize = 4096;

/// The trace of one SMT decision.
pub struct LpTrace {
    writer: BufWriter<File>,
    // The objects made so far of each kind, which number the next.
    counts: Vec<(String, usize)>,
    lines: Vec<Json>,
    // The calls whose lines wait for what they return, which keep the lines from being written.
    open_calls: usize,
    // The first write that failed, which `close` reports; the trace stops writing there.
    error: Option<io::Error>,
}

/// A call whose line is in the trace, to finish with what it returned or threw.
#[must_use]
pub struct Call(usize);

impl LpTrace {
    /// The trace of the decision of the text, when `PROVE_IT_LP_TRACE` names a directory.
    pub fn open(text: &str) -> io::Result<Option<LpTrace>> {
        if cfg!(all(target_arch = "wasm32", target_os = "unknown")) {
            return Ok(None);
        }
        std::env::var_os("PROVE_IT_LP_TRACE")
            .filter(|directory| !directory.is_empty())
            .map(|directory| LpTrace::create(Path::new(&directory), text))
            .transpose()
    }

    /// The trace of the decision of the text in the directory, whatever `PROVE_IT_LP_TRACE` says.
    pub fn create(directory: &Path, text: &str) -> io::Result<LpTrace> {
        let digest: String = sha256(text.as_bytes())[..8]
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect();
        fs::create_dir_all(directory)?;
        let file = File::create(directory.join(format!("{digest}.lptrace")))?;
        Ok(LpTrace {
            writer: BufWriter::new(file),
            counts: Vec::new(),
            lines: Vec::new(),
            open_calls: 0,
            error: None,
        })
    }

    /// The theory made an lp object of the kind ("lar", "lia", "bp", "nla"): its id, `kind#n`,
    /// numbered per kind, and its `new` line, with the arguments the closure encodes given the id
    /// (a callback argument is named after it, as `lar#0.new.0`).
    pub fn new_object(&mut self, kind: &str, args: impl FnOnce(&str) -> Vec<Json>) -> String {
        let count = match self.counts.iter_mut().find(|entry| entry.0 == kind) {
            Some(entry) => {
                entry.1 += 1;
                entry.1 - 1
            }
            None => {
                self.counts.push((kind.to_string(), 1));
                0
            }
        };
        let id = format!("{kind}#{count}");
        let line = Json::object([
            ("c", Json::String(id.clone())),
            ("m", Json::String("new".into())),
            ("a", Json::Array(args(&id))),
        ]);
        self.push(line);
        id
    }

    /// The theory calls `method` (a path, as "divisions.addIdivision") of the object `id`, or
    /// lp's free function `method` with `id` "lp". The line goes in now, as the callbacks the call
    /// makes come after it; `returned`, `returned_with_out` or `threw` finish it.
    pub fn call(&mut self, id: &str, method: &str, args: Vec<Json>) -> Call {
        self.open_calls += 1;
        self.lines.push(Json::object([
            ("c", Json::String(id.into())),
            ("m", Json::String(method.into())),
            ("a", Json::Array(args)),
        ]));
        Call(self.lines.len() - 1)
    }

    /// The call returned the result, `None` for TypeScript's `undefined`.
    pub fn returned(&mut self, call: Call, result: Option<Json>) {
        self.finish(call, result.map(|result| ("r", result)));
    }

    /// The call, one of whose arguments is an Explanation that lp fills in, returned: `out` holds
    /// the arguments after it.
    pub fn returned_with_out(&mut self, call: Call, out: Vec<Json>, result: Option<Json>) {
        self.add_field(&call, "o", Json::Array(out));
        self.returned(call, result);
    }

    /// The call threw the error, `"Name: message"` (`get_error`).
    pub fn threw(&mut self, call: Call, error: &str) {
        self.finish(call, Some(("e", Json::String(error.into()))));
    }

    /// lp called back the theory's function `name` (`<obj>.<method>.<index>`, or
    /// `<that>.<method>` for a host's method), which answered the result.
    pub fn callback(&mut self, name: &str, args: Vec<Json>, result: Option<Json>) {
        let mut fields = vec![
            ("cb".to_string(), Json::String(name.into())),
            ("a".to_string(), Json::Array(args)),
        ];
        fields.extend(result.map(|result| ("r".to_string(), result)));
        self.push(Json::Object(fields));
    }

    /// lp called back the theory's function `name`, which threw the error.
    pub fn callback_threw(&mut self, name: &str, args: Vec<Json>, error: &str) {
        self.push(Json::object([
            ("cb", Json::String(name.into())),
            ("a", Json::Array(args)),
            ("e", Json::String(error.into())),
        ]));
    }

    /// The theory read the field `path` (as "columnsWithChangedBounds.size") of the object `id`.
    pub fn read(&mut self, id: &str, path: &str, value: Json) {
        self.push(Json::object([
            ("f", Json::String(id.into())),
            ("p", Json::String(path.into())),
            ("r", value),
        ]));
    }

    /// The theory wrote the field `path` of the object `id`.
    pub fn write(&mut self, id: &str, path: &str, value: Json) {
        self.push(Json::object([
            ("w", Json::String(id.into())),
            ("p", Json::String(path.into())),
            ("v", value),
        ]));
    }

    /// Writes the rest of the trace, and reports the first write that failed. Dropping the trace
    /// writes the rest too, but ignores a failure.
    pub fn close(mut self) -> io::Result<()> {
        self.flush();
        self.error.take().map_or(Ok(()), Err)
    }

    fn add_field(&mut self, call: &Call, key: &str, value: Json) {
        if let Json::Object(fields) = &mut self.lines[call.0] {
            fields.push((key.into(), value));
        }
    }

    fn finish(&mut self, call: Call, field: Option<(&str, Json)>) {
        if let Some(field) = field {
            self.add_field(&call, field.0, field.1);
        }
        self.open_calls -= 1;
        self.flush_if_full();
    }

    fn push(&mut self, line: Json) {
        self.lines.push(line);
        self.flush_if_full();
    }

    fn flush_if_full(&mut self) {
        if self.open_calls == 0 && self.lines.len() >= FLUSH_SIZE {
            self.flush();
        }
    }

    fn flush(&mut self) {
        let lines = std::mem::take(&mut self.lines);
        if self.error.is_some() {
            return;
        }
        let result = lines
            .iter()
            .try_for_each(|line| writeln!(self.writer, "{line}"))
            .and_then(|()| self.writer.flush());
        self.error = result.err();
    }
}

impl Drop for LpTrace {
    fn drop(&mut self) {
        self.flush();
    }
}

/// SHA-256 (FIPS 180-4).
fn sha256(bytes: &[u8]) -> [u8; 32] {
    const ROUND_CONSTANTS: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut state: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    let mut message = bytes.to_vec();
    message.push(0x80);
    while message.len() % 64 != 56 {
        message.push(0);
    }
    message.extend_from_slice(&((bytes.len() as u64) * 8).to_be_bytes());
    for block in message.as_chunks::<64>().0 {
        let mut schedule = [0u32; 64];
        for (index, word) in block.as_chunks::<4>().0.iter().enumerate() {
            schedule[index] = u32::from_be_bytes(*word);
        }
        for index in 16..64 {
            let previous = schedule[index - 15];
            let sigma0 = previous.rotate_right(7) ^ previous.rotate_right(18) ^ (previous >> 3);
            let before = schedule[index - 2];
            let sigma1 = before.rotate_right(17) ^ before.rotate_right(19) ^ (before >> 10);
            schedule[index] = schedule[index - 16]
                .wrapping_add(sigma0)
                .wrapping_add(schedule[index - 7])
                .wrapping_add(sigma1);
        }
        let mut work = state;
        for index in 0..64 {
            let [a, b, c, d, e, f, g, h] = work;
            let choice = (e & f) ^ (!e & g);
            let sum1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let first = h
                .wrapping_add(sum1)
                .wrapping_add(choice)
                .wrapping_add(ROUND_CONSTANTS[index])
                .wrapping_add(schedule[index]);
            let majority = (a & b) ^ (a & c) ^ (b & c);
            let sum0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let second = sum0.wrapping_add(majority);
            work = [
                first.wrapping_add(second),
                a,
                b,
                c,
                d.wrapping_add(first),
                e,
                f,
                g,
            ];
        }
        for (word, added) in state.iter_mut().zip(work) {
            *word = word.wrapping_add(added);
        }
    }
    let mut digest = [0u8; 32];
    for (chunk, word) in digest.as_chunks_mut::<4>().0.iter_mut().zip(state) {
        chunk.copy_from_slice(&word.to_be_bytes());
    }
    digest
}

// The trace's encoding of lp's values (lp-trace.ts's serialize).

/// An index or a count; `usize::MAX` (`NULL_LPVAR` and the other `-1` sentinels) is -1.
pub fn get_number(value: usize) -> Json {
    Json::Number(if value == usize::MAX {
        -1.0
    } else {
        value as f64
    })
}

pub fn get_rational(value: &Rational) -> Json {
    Json::String(value.to_string())
}

pub fn get_impq(value: &Impq) -> Json {
    Json::Array(vec![get_rational(&value.x), get_rational(&value.y)])
}

/// A dependency's leaves in the order of `linearize`, `null` for none.
pub fn get_dependency(dep: &Dependency) -> Json {
    match dep {
        None => Json::Null,
        Some(_) => Json::object([(
            "dep",
            Json::Array(
                linearize(std::slice::from_ref(dep))
                    .into_iter()
                    .map(|leaf| Json::Number(f64::from(leaf)))
                    .collect(),
            ),
        )]),
    }
}

pub fn get_explanation(explanation: &Explanation) -> Json {
    let expl = (
        "expl",
        Json::Array(explanation.iter().map(get_number).collect()),
    );
    if explanation.pairs().is_empty() {
        return Json::object([expl]);
    }
    Json::object([
        expl,
        (
            "pairs",
            Json::Array(
                explanation
                    .pairs()
                    .iter()
                    .map(|pair| Json::Array(vec![get_number(pair.0), get_rational(&pair.1)]))
                    .collect(),
            ),
        ),
    ])
}

pub fn get_term(term: &LarTerm) -> Json {
    Json::object([
        ("col", get_number(term.column)),
        (
            "coeffs",
            Json::Array(
                term.iter()
                    .map(|entry| Json::Array(vec![get_number(entry.0), get_rational(entry.1)]))
                    .collect(),
            ),
        ),
    ])
}

/// What `LarSolver.getBound` returns when the column has the bound.
pub fn get_bound_info(bound: &BoundInfo) -> Json {
    Json::object([
        ("dep", get_dependency(&bound.dep)),
        ("value", get_rational(&bound.value)),
        ("isStrict", Json::Bool(bound.is_strict)),
    ])
}

/// An ImpliedBound of BoundPropagator's ibounds, as the iteration of them reads it.
pub fn get_implied_bound(bound: &ImpliedBound) -> Json {
    Json::object([
        ("column", get_number(bound.column)),
        ("bound", get_rational(&bound.bound)),
        ("isLower", Json::Bool(bound.is_lower)),
        ("isStrict", Json::Bool(bound.is_strict)),
        ("explain", Json::object([("fn", Json::Bool(true))])),
    ])
}

/// What `ImpliedBound.explain` returns.
pub fn get_bound_explanation(explanation: &[(Rational, Dependency)]) -> Json {
    Json::Array(
        explanation
            .iter()
            .map(|entry| Json::Array(vec![get_rational(&entry.0), get_dependency(&entry.1)]))
            .collect(),
    )
}

/// A LiaMove as TypeScript's `{ kind, ... }`.
pub fn get_lia_move(lia_move: &LiaMove) -> Json {
    let kind = |name: &str| ("kind", Json::String(name.into()));
    match lia_move {
        LiaMove::Sat => Json::object([kind("sat")]),
        LiaMove::Undef => Json::object([kind("undef")]),
        LiaMove::Conflict => Json::object([kind("conflict")]),
        LiaMove::Continue => Json::object([kind("continue")]),
        LiaMove::Cut { offset, is_upper } => Json::object([
            kind("cut"),
            ("offset", get_rational(offset)),
            ("isUpper", Json::Bool(*is_upper)),
        ]),
        LiaMove::Branch { is_upper, offset } => Json::object([
            kind("branch"),
            ("isUpper", Json::Bool(*is_upper)),
            ("offset", get_rational(offset)),
        ]),
    }
}

/// An lbool as TypeScript's number: 1, -1 or 0.
pub fn get_lbool(value: LBool) -> Json {
    Json::Number(f64::from(value.to_i8()))
}

pub fn get_ineq(ineq: &Ineq) -> Json {
    Json::object([
        ("cmp", Json::Number(f64::from(ineq.cmp))),
        ("term", get_term(&ineq.term)),
        ("rs", get_rational(&ineq.rs)),
    ])
}

pub fn get_lemma(lemma: &Lemma) -> Json {
    Json::object([
        (
            "ineqs",
            Json::Array(lemma.ineqs.iter().map(get_ineq).collect()),
        ),
        ("expl", get_explanation(&lemma.expl)),
    ])
}

pub fn get_equality(equality: &NlaEquality) -> Json {
    Json::object([
        ("first", get_number(equality.first)),
        ("second", get_number(equality.second)),
        ("explanation", get_explanation(&equality.explanation)),
    ])
}

pub fn get_fixed_equality(equality: &NlaFixedEquality) -> Json {
    Json::object([
        ("lpVar", get_number(equality.lp_var)),
        ("value", get_rational(&equality.value)),
        ("explanation", get_explanation(&equality.explanation)),
    ])
}

fn get_mpbq(value: &Mpbq) -> Json {
    Json::object([
        ("num", Json::String(value.num.to_string())),
        ("k", Json::Number(f64::from(value.k))),
    ])
}

/// An algebraic number as `{"anum": value}`, a cell with the fields of TypeScript's AlgebraicCell.
pub fn get_anum(anum: &Anum) -> Json {
    let value = match &*anum.value() {
        AnumValue::Rational(value) => get_rational(value),
        AnumValue::Cell(cell) => Json::object([
            (
                "p",
                Json::Array(
                    cell.p
                        .iter()
                        .map(|coeff| Json::String(coeff.to_string()))
                        .collect(),
                ),
            ),
            ("lower", get_mpbq(&cell.lower)),
            ("upper", get_mpbq(&cell.upper)),
            ("isMinimal", Json::Bool(cell.is_minimal)),
            ("isSignLowerNeg", Json::Bool(cell.is_sign_lower_neg)),
            ("isNotRational", Json::Bool(cell.is_not_rational)),
            ("rootIndex", Json::Number(f64::from(cell.root_index))),
        ]),
    };
    Json::object([("anum", value)])
}

/// A function the theory passes to lp, or stores in an lp field, by its callback name.
pub fn get_callback(name: &str) -> Json {
    Json::object([("cb", Json::String(name.into()))])
}

/// An lp object the theory passes, by its id.
pub fn get_reference(id: &str) -> Json {
    Json::object([("ref", Json::String(id.into()))])
}

/// The `Name: message` of the TypeScript error an SmtError stands for.
pub fn get_error(error: &SmtError) -> String {
    let name = match error {
        SmtError::Canceled => "SmtCanceledError",
        SmtError::Unsupported(_) => "SmtUnsupportedError",
        SmtError::Invariant(_) => "SmtInvariantError",
        SmtError::Parse(_) => "SmtParseError",
        SmtError::NlsatUnsupported(_) => "NlsatUnsupportedError",
        SmtError::PddMemoryOut => "PddMemoryOutError",
    };
    format!("{name}: {error}")
}

#[cfg(test)]
mod tests {
    use super::sha256;

    fn get_hex(bytes: &[u8]) -> String {
        bytes.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    #[test]
    fn hashes_the_fips_test_vectors() {
        let cases = [
            (
                "",
                "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            ),
            (
                "abc",
                "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
            ),
            (
                "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
                "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
            ),
        ];
        for case in cases {
            assert_eq!(get_hex(&sha256(case.0.as_bytes())), case.1);
        }
        assert_eq!(
            get_hex(&sha256(&vec![b'a'; 1_000_000])),
            "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
        );
    }
}
