// Compares the Rust obligations (native/crates/prover/obligations) with the TypeScript ones on every
// module of proofs.json, as text: each side writes one JSON line per module, with each obligation's
// id, location, kind, method and printed text, each module's summary, the warnings in order, and
// the error that stopped it, if any.
// Usage: bun scripts/obligation-differential.ts [--filter text] [--skip text] [--rust <dump>]

import { readFileSync } from "node:fs";

import { formatSummary, getObligations } from "../src/obligations";
import type { Warn } from "../src/obligations/expression";
import { compareModules, describeError } from "./obligations-dump";
import { readModule, readProofRecords } from "./proof-records";

const writeModule = (path: string) => {
  const warnings: [string, string][] = [];
  const onWarning: Warn = (warning) => warnings.push([warning.channel, warning.text]);
  const read = () => {
    try {
      return {
        results: getObligations(
          [{ file: path, source: readFileSync(path, "utf8") }],
          (name) => readModule(path, name),
          { onWarning },
        ),
      };
    } catch (error) {
      return { error: describeError(error) };
    }
  };
  const outcome = read();
  return JSON.stringify({
    results: (outcome.results ?? []).map((result) => ({
      name: result.name,
      summary: formatSummary(result),
      obligations: result.obligations.map((obligation) => ({
        id: obligation.id,
        location: obligation.location,
        kind:
          obligation.kind.kind === "Omitted"
            ? `Omitted ${obligation.kind.omission}`
            : obligation.kind.kind,
        method:
          obligation.method === undefined
            ? null
            : [
                obligation.method.name,
                obligation.method.tactic ?? null,
                obligation.method.timeout ?? null,
              ],
        text: obligation.text,
      })),
    })),
    warnings,
    error: outcome.error ?? null,
  });
};

const records = readProofRecords();
const differences = compareModules({ records, writeModule, flags: [], batch: 50 });
console.log(
  `obligations: ${records.length - differences.length} of ${records.length} modules match`,
);
process.exit(differences.length === 0 ? 0 : 1);
