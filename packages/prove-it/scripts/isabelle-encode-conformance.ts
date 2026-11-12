// Compares tla-ts's Isabelle theory for each obligation with the theory tlapm wrote, as
// conformance:record-proofs recorded it, up to comments and the theory's name.

import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";

import { TlaProverError, TlaUnsupportedError } from "../src/errors";
import { CONFORMANCE_DIRECTORY, CORPORA_DIRECTORY, writeResults } from "./corpora";
import {
  getIsabelleDigest,
  getModuleEncodings,
  normalizeTheory,
  printResults,
  PROOF_INPUTS_DIRECTORY,
  readProofRecords,
} from "./proof-records";

type Verdict = "match" | "mismatch" | "unsupported" | "failed";

const RESULTS_PATH = join(CONFORMANCE_DIRECTORY, ".isabelle-encode-results.json");

// How much of each theory to show around the first difference.
const CONTEXT_LENGTH = 150;

interface Result {
  module: string;
  id: number;
  verdict: Verdict;
  reason?: string;
  expected?: string;
  actual?: string;
}

// The theory, or why tla-ts can't encode the obligation or tlapm wouldn't.
const getEncoding = (encoding: string | Error) => {
  if (typeof encoding === "string") return { kind: "theory", text: encoding } as const;
  if (encoding instanceof TlaUnsupportedError)
    return { kind: "unsupported", reason: encoding.message } as const;
  if (encoding instanceof TlaProverError)
    return { kind: "failed", reason: encoding.message } as const;
  throw encoding;
};

// The two normalized theories from just before the first character where they differ.
const findDifference = (expected: string, actual: string) => {
  const left = normalizeTheory(expected);
  const right = normalizeTheory(actual);
  const index = [...left].findIndex((character, position) => character !== right[position]);
  const start = Math.max(0, (index === -1 ? left.length : index) - CONTEXT_LENGTH / 3);
  return {
    expected: left.slice(start, start + CONTEXT_LENGTH),
    actual: right.slice(start, start + CONTEXT_LENGTH),
  };
};

const results = readProofRecords()
  .filter((record) =>
    record.obligations.some(
      (obligation) => obligation.status !== "trivial" && "isabelle" in obligation,
    ),
  )
  .flatMap((record): Result[] => {
    const recorded = record.obligations.flatMap((expected) =>
      expected.status === "trivial" || !("isabelle" in expected) || !expected.isabelle
        ? []
        : [{ id: expected.id, input: expected.isabelle.input }],
    );
    const encodings = getModuleEncodings(
      join(CORPORA_DIRECTORY, record.id),
      recorded.map((expected) => expected.id),
      "isabelle",
      (obligation) => obligation.kind !== "Error",
    ).encodings;
    return recorded.map((expected): Result => {
      const base = { module: record.id, id: expected.id };
      const encoding = encodings.get(expected.id);
      if (encoding === undefined)
        return { ...base, verdict: "mismatch", reason: "tla-ts has no such obligation" };
      const encoded = getEncoding(encoding);
      const inputPath = join(PROOF_INPUTS_DIRECTORY, record.id, `${expected.id}.thy`);
      // tlapm writes a theory as it prints it, so one whose printing fails stops before its end.
      if (
        encoded.kind === "failed" &&
        existsSync(inputPath) &&
        !/\nend\s*$/.test(readFileSync(inputPath, "utf8"))
      )
        return { ...base, verdict: "match" };
      if (encoded.kind !== "theory")
        return { ...base, verdict: encoded.kind, reason: encoded.reason };
      if (getIsabelleDigest(encoded.text) === expected.input) return { ...base, verdict: "match" };
      if (!existsSync(inputPath)) return { ...base, verdict: "mismatch" };
      return {
        ...base,
        verdict: "mismatch",
        ...findDifference(readFileSync(inputPath, "utf8"), encoded.text),
      };
    });
  });

writeResults(RESULTS_PATH, results);
printResults(
  results,
  ["match", "mismatch", "unsupported", "failed"],
  ["mismatch", "unsupported", "failed"],
  (result) =>
    [
      `${result.verdict} ${result.module} #${result.id}${result.reason ? `: ${result.reason}` : ""}`,
      ...(result.expected === undefined ? [] : [`  tlapm:  ${result.expected}`]),
      ...(result.actual === undefined ? [] : [`  tla-ts: ${result.actual}`]),
    ].join("\n"),
);
