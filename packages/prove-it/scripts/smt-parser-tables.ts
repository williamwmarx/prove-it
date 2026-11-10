// Writes the table the Rust port of the SMT-LIB parser (design/smt-core.md) is tested against, from
// the TypeScript it ports. parser.txt parses every script of tests/fixtures/smt, and short scripts
// that reach each error of smtlib-parser.ts, with a fresh AstManager each, and records the error, or
// the assertions (handle, Z3 id, hash and text), the declarations and sorts, the number of ASTs, and
// a hash of the id and reference count of every expression. prove-smt's tests/parser.rs replays it:
//   bun scripts/smt-parser-tables.ts

import { readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

import { AstManager, SORT_BOOL } from "../src/prover/smt/solver/ast";
import { ResourceLimit } from "../src/prover/smt/solver/rlimit";
import { parseSmtlib } from "../src/prover/smt/solver/smtlib-parser";

// A text longer than this is recorded as its length and hash.
const MAX_TEXT_LENGTH = 400;

const encoder = new TextEncoder();

// FNV-1a over the UTF-8 bytes, which tests/parser.rs computes the same way.
const getTextHash = (text: string) =>
  encoder.encode(text).reduce((hash, byte) => Math.imul(hash ^ byte, 16777619) >>> 0, 2166136261);

const getShortText = (text: string) => {
  const length = encoder.encode(text).length;
  return length > MAX_TEXT_LENGTH ? `#${length}:${getTextHash(text)}` : text;
};

const SCRIPTS: [string, string][] = [
  ["empty", ""],
  ["comment-only", "; nothing\n"],
  ["no-check-sat", "(declare-const p Bool)\n(assert p)"],
  [
    "after-check-sat",
    "(set-logic AUFLIA)(declare-const p Bool)(assert p)(check-sat)(assert (not p))(push 1)",
  ],
  [
    "arith-coercion",
    "(declare-fun x () Int)(declare-fun y () Real)(assert (< x y 2.50 3))(assert (= (+ x 1) (* 2 y)))(check-sat)",
  ],
  [
    "builtins",
    "(declare-const a Int)(declare-const b Int)(declare-const r Real)(declare-const p Bool)\n" +
      "(assert (and (=> p (xor p p)) (distinct a b 0) (= (div a 2) (mod b 3)) (<= (abs a) 7)))\n" +
      "(assert (or (is_int r) (= (to_int r) a) (= (to_real a) (/ r 2 3 4)) (> (- a) (- a b 1))))\n" +
      "(assert (= (ite p a r) (ite (not p) 1.5 0.25)))\n" +
      "(assert (>= 0007 a))(assert (= a b a))(check-sat)",
  ],
  ["nullary-connectives", "(assert (=))(assert (and))(assert (or))(check-sat)"],
  [
    "sorts-and-funcs",
    "(declare-sort U 0)(declare-sort V)(declare-fun f (U V) Int)(declare-fun g (Int) U)\n" +
      "(declare-fun c () V)(declare-const d U)(assert (= (f (g 1) c) (f d c)))\n" +
      "(declare-fun f (U) Bool)(assert (f d))(check-sat)",
  ],
  [
    "quoted",
    '(declare-fun |a b| () Int)(declare-fun |12| () Int)(set-info :source |x ; y|)(set-info :s "a""b")\n' +
      "(assert (= |a b| 4))(check-sat)",
  ],
  [
    "quantifiers",
    "(declare-sort U 0)(declare-fun f (U) U)(declare-fun g (U U) Bool)(declare-fun c () U)\n" +
      "(assert (forall ((x U) (y U)) (! (=> (g x y) (= (f x) y)) :pattern ((g x y)) :pattern ((f x)) :qid ax1 :weight 3)))\n" +
      "(assert (forall ((x U)) (! (g x (f x)) :pattern (f x) :pattern (c) :pattern (true) :pattern ((not (g x x))) :pattern ((f x) (g c x)))))\n" +
      "(assert (exists ((x U)) (forall ((y U)) (! (g x y) :pattern ((g x y)) :weight 0x10))))\n" +
      "(assert (forall ((x U) (y Int)) (! (exists ((z U)) (= (f z) x)) :pattern ((f x)) :pattern ((g (f x) (f x))))))\n" +
      "(assert (forall ((x Int)) (! (> x 0) :weight 2 :pattern ((+ x 1)) :pattern ((forall ((y Int)) (> y x))))))\n" +
      "(check-sat)",
  ],
  [
    "lets",
    "(declare-const a Int)(declare-const p Bool)\n" +
      "(assert (let ((x (+ a 1)) (y a)) (let ((x (* x y)) (p (not p))) (and p (> x y)))))\n" +
      "(assert (forall ((x Int)) (let ((y (+ x 1))) (> y x))))\n" +
      "(check-sat)",
  ],
  [
    "let-under-binder",
    "(declare-const a Int)(assert (let ((y a) (z 1)) (forall ((x Int)) (> x (+ y z)))))\n" +
      "(assert (forall ((v Int)) (let ((w (+ v 1))) (exists ((x Int)) (> x w)))))(check-sat)",
  ],
  [
    "named",
    "(declare-const p Bool)(declare-const q Bool)(assert (! (and p q) :named both))(assert (! p :lbl x))(assert (! q :named n1 :named n2))(check-sat)",
  ],
  ["unterminated-quoted-symbol", "(assert |x)"],
  ["unbalanced-close", "(assert true))"],
  ["unbalanced-open", "(assert true"],
  ["unbalanced-quoted-paren", "(assert |(|)"],
  ["top-level-symbol", "foo"],
  ["declare-fun-without-domain", "(declare-fun f Int Int)"],
  ["quantifier-without-declarations", "(assert (forall x true))"],
  ["let-binding-not-a-list", "(assert (let (x) true))"],
  ["empty-command", "()"],
  ["command-head-list", "((assert) true)"],
  ["declare-const-without-name", "(declare-const (x) Int)"],
  ["declare-const-without-sort", "(declare-const x)"],
  ["sort-not-a-symbol", "(declare-const x (Array Int Int))"],
  ["empty-application", "(assert ())"],
  ["application-head-list", "(assert ((f) 1))"],
  ["named-without-name", "(assert (! true :named))"],
  ["qid-not-a-symbol", "(assert (forall ((x Int)) (! (> x 0) :qid (a))))"],
  ["declaration-without-sort", "(assert (forall ((x)) true))"],
  ["unknown-sort", "(declare-const x Foo)"],
  ["unknown-function", "(assert g)"],
  ["unknown-function-applied", "(declare-const a Int)(assert (> (h a) 0))"],
  ["ill-sorted-and", "(assert (and 1))"],
  ["ill-sorted-arity", "(declare-fun f (Int) Bool)(assert (f 1 2))"],
  ["ill-sorted-argument", "(declare-fun f (Int) Bool)(assert (f true))"],
  ["ill-sorted-plus", "(assert (> (+ true) 0))"],
  ["ill-sorted-abs", "(assert (> (abs) 0))"],
  ["ill-sorted-minus", "(assert (> (-) 0))"],
  ["ill-sorted-eq", "(assert (= 1 true))"],
  ["ill-sorted-ite", "(assert (ite 1 true false))"],
  ["ill-sorted-uninterpreted-arith", "(declare-sort U 0)(declare-const u U)(assert (< u u))"],
  ["expected-formula", "(assert 1)"],
  ["expected-formula-body", "(assert (forall ((x Int)) x))"],
  ["parametric-sort", "(declare-sort S 1)"],
  ["parametric-sort-list", "(declare-sort S (1))"],
  ["push", "(push 1)"],
  ["pop", "(pop 1)"],
  ["define-fun", "(define-fun f () Int 1)"],
  ["define-sort", "(define-sort S () Int)"],
  ["missing-assertion", "(assert)"],
  ["missing-named-term", "(assert (!))"],
  ["missing-let-body", "(assert (let ((x 1))))"],
  ["missing-let-term", "(assert (let ((x)) x))"],
  ["missing-quantifier-body", "(assert (forall ((y Int))))"],
];

const lines: string[] = [];

const record = (label: string, text: string) => {
  lines.push(label);
  const manager = new AstManager(new ResourceLimit(Number.POSITIVE_INFINITY));
  const getProblem = () => {
    try {
      return parseSmtlib(text, manager, () => {});
    } catch (error) {
      if (!(error instanceof Error)) throw error;
      // A TypeError's message is the engine's, so only its name is recorded.
      lines.push(
        error.name === "TypeError" ? "error TypeError" : `error ${error.name} ${error.message}`,
      );
      return undefined;
    }
  };
  const problem = getProblem();
  if (problem === undefined) return;
  lines.push(`check-sat ${problem.hasCheckSat}`);
  for (const assertion of problem.assertions)
    lines.push(
      `assert ${assertion} ${manager.ids[assertion]} ${manager.hashes[assertion]} ${getShortText(manager.toString(assertion))}`,
    );
  for (const [index, name] of manager.sortNames.entries()) lines.push(`sort ${index} ${name}`);
  for (const [index, decl] of manager.funcDecls.entries())
    lines.push(
      `decl ${index} ${decl.name} ${decl.family} ${decl.op} ${decl.domain.join(",")}:${decl.range} ${decl.smallId}`,
    );
  lines.push(`asts ${manager.getNumAsts()}`);
  // A fresh variable takes the next handle, so it counts the expressions.
  const numNodes = manager.mkVar(1 << 20, SORT_BOOL);
  const handles = Array.from({ length: numNodes }, (_, index) => index);
  lines.push(
    `nodes ${numNodes} ${getTextHash(handles.map((handle) => manager.ids[handle]).join(","))} ${getTextHash(handles.map((handle) => manager.getRefCount(handle)).join(","))}`,
  );
};

const fixtures = join(import.meta.dir, "../tests/fixtures/smt");
for (const file of readdirSync(fixtures)
  .filter((name) => name.endsWith(".smt"))
  .sort())
  record(`fixture ${file}`, readFileSync(join(fixtures, file), "utf8"));
for (const [name, text] of SCRIPTS) record(`script ${name} ${JSON.stringify(text)}`, text);

writeFileSync(
  join(import.meta.dir, "../native/crates/prover/smt/tests/tables/parser.txt"),
  `${lines.join("\n")}\n`,
);
