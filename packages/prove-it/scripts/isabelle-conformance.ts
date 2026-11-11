// Runs each Isabelle theory tlapm wrote through the native Isabelle and compares the verdict with
// Isabelle's. An unsound answer proves what Isabelle couldn't. Each theory gets tlapm's limit of
// 30 s, which the port enforces itself.

import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";

import { getNativeAddon } from "../src/engine/native";
import { getIsabelleDigest, PROOF_INPUTS_DIRECTORY, readProofRecords } from "./proof-records";

type Outcome = "match" | "unsound" | "missed" | "missing" | "stale";

interface Result {
  name: string;
  expected: "unsat" | "unknown";
  outcome: Outcome;
  milliseconds: number;
}

const TIME_LIMIT_MS = 30_000;

const addon = getNativeAddon();
if (typeof addon === "string") throw new Error(`no native engine: ${addon}`);

const report = (result: Result) => {
  if (result.outcome === "match") return;
  console.log(
    `${result.outcome.padEnd(8)} ${result.name} (Isabelle: ${result.expected}, ${result.milliseconds} ms)`,
  );
};

const getOutcome = (expected: string, isProved: boolean): Outcome => {
  if (isProved && expected !== "unsat") return "unsound";
  return (isProved ? "unsat" : "unknown") === expected ? "match" : "missed";
};

const results: Result[] = [];
for (const module of readProofRecords()) {
  for (const obligation of module.obligations) {
    if (!("isabelle" in obligation) || obligation.isabelle === undefined) continue;
    const name = `${module.id}/${obligation.id}`;
    const path = join(PROOF_INPUTS_DIRECTORY, module.id, `${obligation.id}.thy`);
    const expected = obligation.isabelle.verdict;
    if (!existsSync(path)) {
      results.push({ name, expected, outcome: "missing", milliseconds: 0 });
      continue;
    }
    const text = readFileSync(path, "utf8");
    if (getIsabelleDigest(text) !== obligation.isabelle.input) {
      results.push({ name, expected, outcome: "stale", milliseconds: 0 });
      continue;
    }
    const started = performance.now();
    const decision = addon.decide("isabelle", text, TIME_LIMIT_MS, undefined, undefined);
    const result = {
      name,
      expected,
      outcome: getOutcome(expected, decision.kind === "decided" && decision.verdict === "unsat"),
      milliseconds: Math.round(performance.now() - started),
    };
    report(result);
    results.push(result);
  }
}

const counts = new Map<Outcome, number>();
results.forEach((result) => counts.set(result.outcome, (counts.get(result.outcome) ?? 0) + 1));
counts.forEach((count, outcome) => console.log(`${outcome}: ${count}`));
console.log(`obligations: ${results.length}`);
if (counts.has("unsound")) process.exitCode = 1;
