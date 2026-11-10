// The inputs prove sends its backends on the recorded modules, which prover-inputs.ts writes, and
// what the TypeScript backends answered on each, which prover-differential.ts compares other ports
// with.

import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

import type { Statistics, Verdict } from "../src/prover/verdict";
import { CONFORMANCE_DIRECTORY } from "./corpora";

// The answer to an input with stepLimit steps and no time limit, or the error the backend threw.
export interface InputRecord {
  prover: string;
  stepLimit: number;
  verdict: Verdict;
  statistics: Statistics;
  error?: string;
}

export const PROVER_INPUTS_PATH = join(CONFORMANCE_DIRECTORY, "prover-inputs.json");

export const PROVER_INPUTS_DIRECTORY = join(CONFORMANCE_DIRECTORY, ".prover-inputs");

const EXTENSIONS: Record<string, string> = {
  smt: "smt",
  z3: "smt2",
  zenon: "znn",
  isabelle: "thy",
  ls4: "ls4",
};

export const getInputPath = (prover: string, digest: string) =>
  join(PROVER_INPUTS_DIRECTORY, prover, `${digest}.${EXTENSIONS[prover]}`);

export const readInputRecords = (): Record<string, InputRecord> => {
  if (!existsSync(PROVER_INPUTS_PATH)) {
    console.error("Run prover-inputs --record first");
    process.exit(1);
  }
  return JSON.parse(readFileSync(PROVER_INPUTS_PATH, "utf8"));
};

// One input to a line, by digest, so that a new recording's diff shows what changed.
export const writeInputRecords = (records: Record<string, InputRecord>) =>
  writeFileSync(
    PROVER_INPUTS_PATH,
    `{\n${Object.keys(records)
      .sort()
      .map((digest) => `${JSON.stringify(digest)}: ${JSON.stringify(records[digest])}`)
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
