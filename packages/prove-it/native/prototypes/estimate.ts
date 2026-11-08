// Projects each stage's time per model from today's Depot times under the assumptions in DESIGN.md
// section 8, and prints each model's seconds and the geometric means. The input is a JSON array of
// { model, proveit_s, tlc_s, tlats_s } rows, one per suite model, as the benchmark table gives them.
//
// Usage: bun native/prototypes/estimate.ts suite.json

import { readFileSync } from "node:fs";

interface SuiteRow {
  model: string;
  proveit_s: number;
  tlc_s: number;
  tlats_s: number;
}

const suite: SuiteRow[] = JSON.parse(readFileSync(process.argv[2], "utf8"));
// The engine's search time on the two models whose temporal properties the interpreter checks.
const LIVE_ENGINE: Record<string, number> = { "ReadersWriters MC": 0.049, TokenRing: 0.097 };

const fixed = (row: SuiteRow) => Math.min(0.04, 0.8 * row.proveit_s);
// A level-synchronous search on 4 cores: no gain below 0.1 s of search, 2.5x from 0.5 s.
const threads = (seconds: number) =>
  seconds <= 0.1 ? 1 : seconds >= 0.5 ? 2.5 : 1 + (1.5 * (seconds - 0.1)) / 0.4;

const project = (row: SuiteRow, k1: number) => {
  const total = row.proveit_s;
  const startup = fixed(row);
  const engine = LIVE_ENGINE[row.model];
  if (engine !== undefined) {
    const live = total - startup - engine;
    const search = engine / k1;
    return [
      total,
      startup + 0.002 + search + live,
      startup + 0.002 + search / threads(search) + live,
      // Liveness on the engine's graph costs about what the search costs.
      startup + 0.002 + (2 * search) / threads(search),
      0.006 + (2 * search) / threads(search),
    ];
  }
  const search = (total - startup) / k1;
  const threaded = search / threads(search);
  return [
    total,
    startup + 0.002 + search,
    startup + 0.002 + threaded,
    startup + 0.002 + threaded,
    0.006 + threaded,
  ];
};

const geomean = (values: number[]) =>
  Math.exp(values.reduce((sum, value) => sum + Math.log(value), 0) / values.length);
const fixedWidth = (value: number, width: number, digits: number) =>
  value.toFixed(digits).padStart(width);

for (const k1 of [1.3, 1.6, 2]) {
  const projections = suite.map((row) => project(row, k1));
  const stage = (index: number) => geomean(projections.map((projection) => projection[index]));
  const stages = [0, 1, 2, 3, 4];
  const tlc = geomean(suite.map((row) => row.tlc_s));
  const tlaTs = geomean(suite.map((row) => row.tlats_s));
  console.log(`single-thread engine speedup k1=${k1 === 2 ? "2.0" : k1}`);
  if (k1 === 1.6) {
    suite.forEach((row, index) =>
      console.log(
        `  ${row.model.padEnd(18)} ${projections[index].map((value) => fixedWidth(value, 6, 3)).join("  ")}`,
      ),
    );
  }
  console.log(`  geomean s: ${stages.map((index) => stage(index).toFixed(4)).join("  ")}`);
  console.log(
    `  vs TLC 1 worker: ${stages.map((index) => `${(tlc / stage(index)).toFixed(1)}x`).join("  ")}`,
  );
  console.log(
    `  vs tla-ts:       ${stages.map((index) => `${(tlaTs / stage(index)).toFixed(1)}x`).join("  ")}`,
  );
}
