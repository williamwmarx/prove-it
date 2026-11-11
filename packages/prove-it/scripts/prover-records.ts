// The inputs prove sends its backends on the recorded modules, which prover-inputs.ts writes, and
// what the TypeScript backends answered on each, which prover-differential.ts compares other ports
// with.

import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

import type { Statistics, Verdict } from "../src/prover/verdict";
import { CONFORMANCE_DIRECTORY } from "./corpora";

// The answer to an input with stepLimit steps and no time limit, or the error the backend threw.
// An input that throws has no step limit: a backend may take steps before the error, as Z3 does
// parsing up to the malformed term, so a limit could stop it before the error. It throws within
// the time limit, so it throws without one.
export interface InputRecord {
  prover: string;
  stepLimit?: number;
  verdict: Verdict;
  statistics: Statistics;
  error?: string;
}

export const PROVER_INPUTS_PATH = join(CONFORMANCE_DIRECTORY, "prover-inputs.json");

export const PROVER_INPUTS_DIRECTORY = join(CONFORMANCE_DIRECTORY, ".prover-inputs");

// The time limits in seconds, null for none, that prove sent each input with, by key.
export const TIME_LIMITS_PATH = join(PROVER_INPUTS_DIRECTORY, "time-limits.json");

const EXTENSIONS: Record<string, string> = {
  smt: "smt",
  z3: "smt2",
  zenon: "znn",
  isabelle: "thy",
  ls4: "ls4",
};

// An input by its prover and the digest of its text. Two provers can be sent the same text, as the
// smt and z3 methods are, each with its own time limit and so its own step limit.
export const getInputKey = (prover: string, digest: string) => `${prover}/${digest}`;

export const getInputPath = (key: string) => {
  const [prover, digest] = key.split("/");
  return join(PROVER_INPUTS_DIRECTORY, prover, `${digest}.${EXTENSIONS[prover]}`);
};

export const readInputRecords = (): Record<string, InputRecord> => {
  if (!existsSync(PROVER_INPUTS_PATH)) {
    console.error("Run prover-inputs --record first");
    process.exit(1);
  }
  return JSON.parse(readFileSync(PROVER_INPUTS_PATH, "utf8"));
};

// The answer a decision gave to a recorded input, or the error it threw.
export interface InputAnswer {
  verdict: Verdict;
  statistics: Statistics;
  error?: string;
}

// The records with the given answers in place of the recorded ones, each input keeping its prover
// and step limit, for a change that moves the search on the step limit it was recorded with.
export const getUpdatedRecords = (
  records: Record<string, InputRecord>,
  answers: ReadonlyMap<string, InputAnswer>,
) =>
  Object.fromEntries(
    Object.entries(records).map(([key, record]) => {
      const answer = answers.get(key);
      if (answer === undefined) return [key, record];
      const updated: InputRecord = {
        prover: record.prover,
        ...(record.stepLimit !== undefined && { stepLimit: record.stepLimit }),
        verdict: answer.verdict,
        statistics: answer.statistics,
        ...(answer.error !== undefined && { error: answer.error }),
      };
      return [key, updated];
    }),
  );

// The time limits after a run over some modules: the run's limits for the inputs it wrote, the
// earlier file's for the rest, so that a run with --filter or --skip keeps the other modules' limits.
export const getMergedTimeLimits = (
  earlier: Record<string, (number | null)[]>,
  written: Record<string, (number | null)[]>,
): Record<string, (number | null)[]> => ({ ...earlier, ...written });

// One input to a line, by key, so that a new recording's diff shows what changed.
export const writeInputRecords = (records: Record<string, InputRecord>) =>
  writeFileSync(
    PROVER_INPUTS_PATH,
    `{\n${Object.keys(records)
      .sort()
      .map((key) => `${JSON.stringify(key)}: ${JSON.stringify(records[key])}`)
      .join(",\n")}\n}\n`,
  );

// Makes prove's decide use the TypeScript backends whatever the environment says, as the record is
// theirs.
export const useTypeScriptBackends = () => {
  Object.keys(process.env)
    .filter((name) => name.startsWith("PROVE_IT_PROVER"))
    .forEach((name) => delete process.env[name]);
  process.env.PROVE_IT_PROVER = "ts";
};
