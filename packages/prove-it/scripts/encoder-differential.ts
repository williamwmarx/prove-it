// Compares what Prep.ship makes of each obligation in Rust (native/crates/prover/obligations) and in
// TypeScript, on every module of proofs.json: each side writes one JSON line per module, with each
// obligation's fingerprint, its methods, and for each method the text encodeForBackend gives or its
// error, and each result's theory of the Isabelle proofs, as if every Isabelle method it encodes
// proved. Each result is one run, as prove-it tlapm proves it, so the SMT encoder numbers its CASE
// errors across the result's obligations in order.
// With tests/conformance/prover-inputs.json, every text the Rust writes must be recorded there,
// unless the TypeScript writes the same text, which is then a record gap: prove sends a backend
// only the methods it tries. With --reset-caches, the Rust starts each module from empty caches.
// Usage: bun scripts/encoder-differential.ts [--filter text] [--skip text] [--rust <dump>]
//   [--reset-caches]

import { existsSync, readFileSync } from "node:fs";

import { getObligations } from "../src/obligations";
import { getFingerprint } from "../src/prover/prep/fingerprint";
import { findMethods } from "../src/prover/prep/methods";
import { encodeForBackend, encodeProofTheory, type ProofAttempt } from "../src/prover/prove";
import { type ComparedModule, compareModules, describeError } from "./obligations-dump";
import { readModule, readProofRecords } from "./proof-records";
import { getInputKey, PROVER_INPUTS_PATH, readInputRecords } from "./prover-records";
import { getDigest } from "./tlapm-digest";

interface EncodedModule {
  results: { obligations: { encodings: [string, unknown][] }[] }[];
}

interface ProverCount {
  texts: number;
  errors: number;
  recorded: number;
  gaps: number;
  absent: Map<string, number>;
}

const getOutcome = (write: () => unknown) => {
  try {
    return write();
  } catch (error) {
    return describeError(error);
  }
};

const writeModule = (path: string) => {
  const read = () => {
    try {
      return {
        results: getObligations([{ file: path, source: readFileSync(path, "utf8") }], (name) =>
          readModule(path, name),
        ),
      };
    } catch (error) {
      return { error: describeError(error) };
    }
  };
  const outcome = read();
  return JSON.stringify({
    results: (outcome.results ?? []).map((result) => {
      const session = { caseErrors: 0 };
      const attempts: ProofAttempt[][] = [];
      const obligations = result.obligations.map((obligation) => {
        const fingerprint = getOutcome(() => getFingerprint(obligation.sequent));
        const proved: ProofAttempt[] = [];
        attempts.push(proved);
        const methods = getOutcome(() => findMethods(obligation).provers);
        if (!Array.isArray(methods))
          return { id: obligation.id, fingerprint, methods, encodings: [] };
        return {
          id: obligation.id,
          fingerprint,
          methods: methods.map((method) => [
            method.prover,
            method.timeLimitMs,
            method.rlimit ?? null,
            method.tactic ?? null,
          ]),
          encodings: methods.map((method) => {
            const encoding = getOutcome(() => encodeForBackend(obligation, method.prover, session));
            if (method.prover === "isabelle" && typeof encoding === "string")
              proved.push({ method, isProved: true, isReused: false });
            return [method.prover, encoding];
          }),
        };
      });
      return {
        name: result.name,
        obligations,
        theory: getOutcome(() =>
          encodeProofTheory(
            result.name,
            attempts.map((innerAttempts, index) => ({
              obligation: {
                id: result.obligations[index].id,
                location: "",
                text: "",
                status: "trivial",
              },
              attempts: innerAttempts,
            })),
            result.obligations,
          ),
        ),
      };
    }),
    error: outcome.error ?? null,
  });
};

const getObligationList = (line: string) =>
  line === ""
    ? []
    : (JSON.parse(line) as EncodedModule).results.flatMap((result) => result.obligations);

const startedAt = performance.now();
const records = readProofRecords();
const inputs = existsSync(PROVER_INPUTS_PATH) ? readInputRecords() : undefined;
const counts = new Map<string, ProverCount>();
const obligationCounts = { obligations: 0 };

// Counts each encoding the Rust writes, and whether the record has it or the TypeScript writes the
// same one in its place.
const countModule = (module: ComparedModule) => {
  const expected = getObligationList(module.expected).flatMap((obligation) => obligation.encodings);
  const actual = getObligationList(module.actual);
  obligationCounts.obligations += actual.length;
  actual
    .flatMap((obligation) => obligation.encodings)
    .forEach((encoding, index) => {
      const prover = encoding[0];
      const count = counts.get(prover) ?? {
        texts: 0,
        errors: 0,
        recorded: 0,
        gaps: 0,
        absent: new Map(),
      };
      counts.set(prover, count);
      if (typeof encoding[1] !== "string") {
        count.errors++;
        return;
      }
      count.texts++;
      if (!inputs) return;
      if (inputs[getInputKey(prover, getDigest(encoding[1]))]) count.recorded++;
      else if (JSON.stringify(expected[index]) === JSON.stringify(encoding)) count.gaps++;
      else count.absent.set(module.record.id, (count.absent.get(module.record.id) ?? 0) + 1);
    });
  // Frees the module's garbage before the next one: tcp_proof takes 5 GB in Rust and 12 GB here.
  Bun.gc(true);
};

const differences = compareModules({
  records,
  writeModule,
  flags: process.argv.includes("--reset-caches") ? ["--encode", "--reset-caches"] : ["--encode"],
  batch: 10,
  onModule: countModule,
});

console.log(`obligations: ${obligationCounts.obligations}`);
counts.forEach((count, prover) =>
  console.log(
    inputs
      ? `  ${prover}: ${count.texts} texts, ${count.errors} errors; ${count.recorded} recorded, ${count.gaps} record gaps, ${[...count.absent.values()].reduce((total, absent) => total + absent, 0)} absent`
      : `  ${prover}: ${count.texts} texts, ${count.errors} errors`,
  ),
);
if (!inputs) console.log(`record: ${PROVER_INPUTS_PATH} is absent, so no text is checked`);
counts.forEach((count, prover) =>
  count.absent.forEach((absent, id) => console.log(`absent: ${prover} in ${id}: ${absent}`)),
);
const absentCount = [...counts.values()].reduce((total, count) => total + count.absent.size, 0);
console.log(
  `encodings: ${records.length - differences.length} of ${records.length} modules match in ${Math.round((performance.now() - startedAt) / 1000)}s`,
);
process.exit(differences.length === 0 && absentCount === 0 ? 0 : 1);
