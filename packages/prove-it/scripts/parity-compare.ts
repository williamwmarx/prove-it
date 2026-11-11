// Compares Z3 4.8.9's verdicts (.z3-parity-4.8.9.json) on each smt and z3 input with
// (i) tlapm's recorded verdict in proofs.json, matched by tlapm's input digest of the same text,
// (ii) main's record, (iii) the record at #313's parent, given as a path, and (iv) Z3 5.3.3's
// verdicts, from .z3-parity-5.3.3.json when it exists.
//   bun scripts/run.ts parity-compare <prover-inputs.json at 52b1c5d1> [out.json]
import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

import { CONFORMANCE_DIRECTORY } from "./corpora";
import { getInputDigest, readProofRecords } from "./proof-records";
import { getInputPath, readInputRecords } from "./prover-records";

const proved = (verdict: string | undefined) => verdict === "unsat";

const audit = (version: string) => {
  const path = join(CONFORMANCE_DIRECTORY, `.z3-parity-${version}.json`);
  if (!existsSync(path)) return undefined;
  const results: { key: string; z3: { verdict: string } }[] = JSON.parse(
    readFileSync(path, "utf8"),
  ).results;
  return new Map(results.map((result) => [result.key, result.z3.verdict]));
};

const z3489 = audit("4.8.9");
if (z3489 === undefined) throw new Error("run z3-parity --version 4.8.9 first");
const z3533 = audit("5.3.3");
const main = readInputRecords();
const parent: Record<string, { verdict: string }> = JSON.parse(
  readFileSync(process.argv[2], "utf8"),
);

// tlapm's verdict by its input digest, and where it was recorded.
const tlapm = new Map<string, { verdict: string; where: string[] }>();
for (const module of readProofRecords())
  for (const obligation of module.obligations)
    for (const prover of ["smt", "z3"] as const) {
      const backend =
        obligation.status === "proved" || obligation.status === "failed"
          ? obligation[prover]
          : undefined;
      if (backend === undefined) continue;
      const key = `${prover}/${backend.input}`;
      const entry = tlapm.get(key) ?? { verdict: backend.verdict, where: [] };
      entry.where.push(`${module.id}#${obligation.id}`);
      tlapm.set(key, entry);
    }

interface Row {
  key: string;
  z3489: string;
  tlapm?: string;
  main?: string;
  parent?: string;
  z3533?: string;
  where?: string[];
}
const rows: Row[] = [...z3489].map(([key, verdict]) => {
  const prover = key.split("/")[0];
  const recorded = tlapm.get(
    `${prover}/${getInputDigest(readFileSync(getInputPath(key), "utf8"))}`,
  );
  return {
    key,
    z3489: verdict,
    tlapm: recorded?.verdict,
    main: main[key]?.verdict,
    parent: parent[key]?.verdict,
    z3533: z3533?.get(key),
    where: recorded?.where,
  };
});

const compare = (name: string, get: (row: Row) => string | undefined) => {
  const known = rows.filter((row) => get(row) !== undefined);
  const both = known.filter((row) => proved(row.z3489) && proved(get(row)));
  const only489 = known.filter((row) => proved(row.z3489) && !proved(get(row)));
  const onlyOther = known.filter((row) => !proved(row.z3489) && proved(get(row)));
  console.log(
    `4.8.9 vs ${name}: ${known.length} inputs, both prove ${both.length}, only 4.8.9 ${only489.length}, only ${name} ${onlyOther.length}`,
  );
  return {
    name,
    only489: only489.map((row) => row.key),
    onlyOther: onlyOther.map((row) => row.key),
  };
};

const comparisons = [
  compare("tlapm", (row) => row.tlapm),
  compare("main", (row) => row.main),
  compare("52b1c5d1", (row) => row.parent),
  ...(z3533 ? [compare("5.3.3", (row) => row.z3533)] : []),
];
// What tlapm proved that main doesn't and the parent did, and the reverse.
const lost = rows.filter((row) => proved(row.tlapm) && !proved(row.main) && proved(row.parent));
const gained = rows.filter((row) => proved(row.tlapm) && proved(row.main) && !proved(row.parent));
console.log(`tlapm proves, main doesn't, 52b1c5d1 did: ${lost.length}`);
lost.forEach((row) => console.log(`  ${row.key} 4.8.9 ${row.z3489} ${row.where?.join(" ")}`));
console.log(`tlapm proves, main does, 52b1c5d1 didn't: ${gained.length}`);
gained.forEach((row) => console.log(`  ${row.key} 4.8.9 ${row.z3489} ${row.where?.join(" ")}`));
if (process.argv[3])
  writeFileSync(process.argv[3], JSON.stringify({ comparisons, lost, gained, rows }, null, 1));
