// Regenerates src/prover/isabelle/tla/logic-data.ts from the Isabelle/TLA+ heap that tlapm ships.
// It runs scripts/isabelle/export.ML in that heap, checks that every exported net key matches
// the keys tla-ts computes, and writes the theorems and nets in a compact form. It also writes
// the same data in binary for the Rust port, prove-isabelle's data/logic.bin, beside the FNV-1a
// digest of the JSON (data/logic.digest) that the crate's test checks the binary against. With
// --binary, it writes only those two, from the logic-data.ts that is checked in.
//
// Usage: bun scripts/run.ts isabelle-logic <tlapm>/lib/tlapm/backends/Isabelle-install
//        bun scripts/run.ts isabelle-logic --binary

import { spawnSync } from "node:child_process";
import { copyFileSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { etaContract } from "../src/prover/isabelle/pure/envir";
import {
  destEquals,
  stripAssumsConcl,
  stripImpConcl,
  stripImpPrems,
} from "../src/prover/isabelle/pure/logic";
import { keyOfTerm } from "../src/prover/isabelle/pure/net";
import {
  mkAbs,
  mkApp,
  mkBound,
  mkConst,
  mkFree,
  mkTFree,
  mkTVar,
  mkType,
  mkVar,
  type Term,
  type Typ,
} from "../src/prover/isabelle/pure/term";
import { LOGIC_DATA } from "../src/prover/isabelle/tla/logic-data";

type RawType = ["T", string, number[]] | ["F", string, string[]] | ["V", string, number, string[]];
type RawTerm =
  | ["C", string, number]
  | ["F", string, number]
  | ["V", string, number, number]
  | ["B", number]
  | ["A", string, number, RawTerm]
  | ["$", RawTerm, RawTerm];
type RawItem = [number, boolean, number, string];
type RawExtraItem = [number, number, boolean, number, string];
type RawRule = [number, number, number[], number, number[]];

interface RawLogic {
  types: RawType[];
  consts: [string, number, RawTerm?][];
  names: [string, string][];
  facts: [string, number[]][];
  factNames: [string, string][];
  simps: [[string, number], number, string][];
  congs: [boolean, string, number][];
  weakCongs: [boolean, string][];
  simprocs: [string, RawTerm[]][];
  loopers: string[];
  unsafeSolvers: string[];
  safeSolvers: string[];
  claset: {
    safeIs: RawRule[];
    safeEs: RawRule[];
    unsafeIs: RawRule[];
    unsafeEs: RawRule[];
    swrappers: string[];
    uwrappers: string[];
    safe0: [RawItem[], RawItem[]];
    safep: [RawItem[], RawItem[]];
    unsafe: [RawItem[], RawItem[]];
    dup: [RawItem[], RawItem[]];
    extra: [RawExtraItem[], RawExtraItem[]];
  };
  contextRules: { bang: [RawExtraItem[], RawExtraItem[]]; plain: [RawExtraItem[], RawExtraItem[]] };
  thms: RawTerm[];
}

type NetItem = [number, 0 | 1, number];
type ExtraNetItem = [number, number, 0 | 1, number];

// What logic-data.ts holds: logic.ts decodes it.
interface LogicJson {
  strings: string[];
  types: number[][];
  terms: number[][];
  thms: number[];
  consts: ([string, number] | [string, number, number])[];
  names: [string, string][];
  facts: [string, number[]][];
  factNames: [string, string][];
  simps: number[];
  congs: [boolean, string, number][];
  weakCongs: [boolean, string][];
  simprocs: [string, number[]][];
  loopers: string[];
  unsafeSolvers: string[];
  safeSolvers: string[];
  claset: {
    safeIs: RawRule[];
    safeEs: RawRule[];
    unsafeIs: RawRule[];
    unsafeEs: RawRule[];
    swrappers: string[];
    uwrappers: string[];
    safe0: [NetItem[], NetItem[]];
    safep: [NetItem[], NetItem[]];
    unsafe: [NetItem[], NetItem[]];
    dup: [NetItem[], NetItem[]];
    extra: [ExtraNetItem[], ExtraNetItem[]];
  };
  contextRules: { bang: [ExtraNetItem[], ExtraNetItem[]]; plain: [ExtraNetItem[], ExtraNetItem[]] };
}

const exportLogic = (install: string) => {
  const work = mkdtempSync(join(tmpdir(), "isabelle-logic-"));
  copyFileSync(
    new URL("../scripts/isabelle/Export.thy", import.meta.url),
    join(work, "Export.thy"),
  );
  copyFileSync(new URL("../scripts/isabelle/export.ML", import.meta.url), join(work, "export.ML"));
  const output = join(work, "logic.json");
  const heaps = ["Pure", "TLA+", "Options"].map((heap) =>
    JSON.stringify(join(install, "heaps", heap)),
  );
  const result = spawnSync(
    join(install, "poly", "poly"),
    [
      "--eval",
      `PolyML.SaveState.loadHierarchy [${heaps.join(", ")}]`,
      "--eval",
      `use_thy ${JSON.stringify(join(work, "Export"))}`,
    ],
    {
      env: {
        ...process.env,
        ISABELLE_HOME: install,
        ML_HOME: join(install, "poly"),
        ISABELLE_LOGIC_OUT: output,
      },
      stdio: ["ignore", "inherit", "inherit"],
    },
  );
  if (result.status !== 0) throw new Error(`Isabelle exited with ${result.status}`);
  const raw: RawLogic = JSON.parse(readFileSync(output, "utf8"));
  rmSync(work, { recursive: true });

  const strings: string[] = [];
  const stringIds = new Map<string, number>();
  const internString = (text: string) => {
    const known = stringIds.get(text);
    if (known !== undefined) return known;
    stringIds.set(text, strings.length);
    strings.push(text);
    return strings.length - 1;
  };

  const types = raw.types.map((type): number[] =>
    type[0] === "T"
      ? [0, internString(type[1]), ...type[2]]
      : type[0] === "F"
        ? [1, internString(type[1])]
        : [2, internString(type[1]), type[2]],
  );

  const terms: number[][] = [];
  const termIds = new Map<string, number>();
  const internTerm = (term: RawTerm): number => {
    const node =
      term[0] === "C"
        ? [0, internString(term[1]), term[2]]
        : term[0] === "F"
          ? [1, internString(term[1]), term[2]]
          : term[0] === "V"
            ? [2, internString(term[1]), term[2], term[3]]
            : term[0] === "B"
              ? [3, term[1]]
              : term[0] === "A"
                ? [4, internString(term[1]), term[2], internTerm(term[3])]
                : [5, internTerm(term[1]), internTerm(term[2])];
    const key = node.join(",");
    const known = termIds.get(key);
    if (known !== undefined) return known;
    termIds.set(key, terms.length);
    terms.push(node);
    return terms.length - 1;
  };

  const thms = raw.thms.map(internTerm);

  const toTyp = (id: number): Typ => {
    const type = raw.types[id];
    return type[0] === "T"
      ? mkType(type[1], type[2].map(toTyp))
      : type[0] === "F"
        ? mkTFree(type[1])
        : mkTVar(type[1], type[2]);
  };

  const toTerm = (term: RawTerm): Term =>
    term[0] === "C"
      ? mkConst(term[1], toTyp(term[2]))
      : term[0] === "F"
        ? mkFree(term[1], toTyp(term[2]))
        : term[0] === "V"
          ? mkVar(term[1], term[2], toTyp(term[3]))
          : term[0] === "B"
            ? mkBound(term[1])
            : term[0] === "A"
              ? mkAbs(term[1], toTyp(term[2]), toTerm(term[3]))
              : mkApp(toTerm(term[1]), toTerm(term[2]));

  const keyText = (term: Term) =>
    keyOfTerm(term)
      .map((key) => (key.kind === "Comb" ? "$" : key.kind === "Var" ? "?" : key.name))
      .join(" ");

  const checkKey = (expected: string, term: Term, what: string) => {
    const actual = keyText(term);
    if (actual !== expected)
      throw new Error(`Net key of ${what} differs: ${actual} vs ${expected}`);
  };

  for (const [name, thm, key] of raw.simps)
    checkKey(
      key,
      etaContract(destEquals(stripImpConcl(toTerm(raw.thms[thm])))[0]),
      `simp ${name[0]}`,
    );

  const brlKey = (isElim: boolean, thm: number) => {
    const prop = toTerm(raw.thms[thm]);
    return isElim ? stripAssumsConcl(stripImpPrems(prop)[0]) : stripImpConcl(prop);
  };

  const items = (pair: [RawItem[], RawItem[]]) =>
    pair.map((side) =>
      side.map((item) => {
        checkKey(item[3], brlKey(item[1], item[2]), `claset rule ${item[2]}`);
        return [item[0], item[1] ? 1 : 0, item[2]];
      }),
    );

  const extraItems = (pair: [RawExtraItem[], RawExtraItem[]]) =>
    pair.map((side) =>
      side.map((item) => {
        checkKey(item[4], brlKey(item[2], item[3]), `context rule ${item[3]}`);
        return [item[0], item[1], item[2] ? 1 : 0, item[3]];
      }),
    );

  return {
    strings,
    types,
    terms,
    thms,
    consts: raw.consts.map((entry) =>
      entry[2] === undefined ? [entry[0], entry[1]] : [entry[0], entry[1], internTerm(entry[2])],
    ),
    names: raw.names.filter((entry) => raw.consts.some((constant) => constant[0] === entry[1])),
    facts: raw.facts,
    factNames: raw.factNames.filter(
      (entry) => entry[0] !== entry[1] && raw.facts.some((fact) => fact[0] === entry[1]),
    ),
    simps: raw.simps.map((entry) => entry[1]),
    congs: raw.congs,
    weakCongs: raw.weakCongs,
    simprocs: raw.simprocs.map((entry) => [entry[0], entry[1].map(internTerm)]),
    loopers: raw.loopers,
    unsafeSolvers: raw.unsafeSolvers,
    safeSolvers: raw.safeSolvers,
    claset: {
      safeIs: raw.claset.safeIs,
      safeEs: raw.claset.safeEs,
      unsafeIs: raw.claset.unsafeIs,
      unsafeEs: raw.claset.unsafeEs,
      swrappers: raw.claset.swrappers,
      uwrappers: raw.claset.uwrappers,
      safe0: items(raw.claset.safe0),
      safep: items(raw.claset.safep),
      unsafe: items(raw.claset.unsafe),
      dup: items(raw.claset.dup),
      extra: extraItems(raw.claset.extra),
    },
    contextRules: {
      bang: extraItems(raw.contextRules.bang),
      plain: extraItems(raw.contextRules.plain),
    },
  };
};

// The binary form of LogicJson, field by field in its order: unsigned LEB128 varints, zigzag for
// the fields Rust holds as i32 (Var and Bound indexes, net tags), booleans as 0 or 1, and each
// array as its length then its elements. Strings are ids into a table that comes first, each a
// UTF-8 byte length then the bytes; the table starts with LogicJson's strings, so their ids are
// their indexes, and the strings field is only their number.
const pushUnsigned = (bytes: number[], value: number): void => {
  if (!Number.isInteger(value) || value < 0 || value > 0xffffffff)
    throw new Error(`${value} isn't a u32`);
  if (value < 0x80) {
    bytes.push(value);
    return;
  }
  bytes.push((value % 0x80) | 0x80);
  pushUnsigned(bytes, Math.floor(value / 0x80));
};

const encodeLogic = (data: LogicJson) => {
  const table = [...data.strings];
  const tableIds = new Map(table.map((text, index) => [text, index]));
  if (tableIds.size !== table.length) throw new Error("The logic's strings repeat");
  const body: number[] = [];
  const writeUnsigned = (value: number) => pushUnsigned(body, value);
  const writeSigned = (value: number) => writeUnsigned(value < 0 ? -2 * value - 1 : 2 * value);
  const writeBoolean = (value: boolean | number) => writeUnsigned(Number(value));
  const writeString = (text: string) => {
    const known = tableIds.get(text);
    if (known !== undefined) return writeUnsigned(known);
    tableIds.set(text, table.length);
    table.push(text);
    return writeUnsigned(table.length - 1);
  };
  const writeArray = <Item>(items: readonly Item[], writeItem: (item: Item) => void) => {
    writeUnsigned(items.length);
    for (const item of items) writeItem(item);
  };
  const writeIds = (ids: readonly number[]) => writeArray(ids, writeUnsigned);
  const writeStrings = (texts: readonly string[]) => writeArray(texts, writeString);
  const writeNames = (names: [string, string]) => {
    writeString(names[0]);
    writeString(names[1]);
  };
  const writeRule = (rule: RawRule) => {
    writeUnsigned(rule[0]);
    writeUnsigned(rule[1]);
    writeIds(rule[2]);
    writeUnsigned(rule[3]);
    writeIds(rule[4]);
  };
  const writeItem = (item: NetItem) => {
    writeSigned(item[0]);
    writeBoolean(item[1]);
    writeUnsigned(item[2]);
  };
  const writeExtraItem = (item: ExtraNetItem) => {
    writeUnsigned(item[0]);
    writeSigned(item[1]);
    writeBoolean(item[2]);
    writeUnsigned(item[3]);
  };
  const writePair = <Item>(pair: [Item[], Item[]], writePairItem: (item: Item) => void) => {
    writeArray(pair[0], writePairItem);
    writeArray(pair[1], writePairItem);
  };

  writeUnsigned(data.strings.length);
  writeArray(data.types, (node) => {
    writeUnsigned(node[0]);
    writeUnsigned(node[1]);
    if (node[0] === 0) writeIds(node.slice(2));
    if (node[0] === 2) writeSigned(node[2]);
  });
  writeArray(data.terms, (node) => {
    writeUnsigned(node[0]);
    if (node[0] === 2) {
      writeUnsigned(node[1]);
      writeSigned(node[2]);
      writeUnsigned(node[3]);
    }
    if (node[0] === 3) writeSigned(node[1]);
    if (node[0] !== 2 && node[0] !== 3) for (const field of node.slice(1)) writeUnsigned(field);
  });
  writeIds(data.thms);
  writeArray(data.consts, (entry) => {
    writeString(entry[0]);
    writeUnsigned(entry[1]);
    writeBoolean(entry.length === 3);
    if (entry.length === 3) writeUnsigned(entry[2]);
  });
  writeArray(data.names, writeNames);
  writeArray(data.facts, (entry) => {
    writeString(entry[0]);
    writeIds(entry[1]);
  });
  writeArray(data.factNames, writeNames);
  writeIds(data.simps);
  writeArray(data.congs, (entry) => {
    writeBoolean(entry[0]);
    writeString(entry[1]);
    writeUnsigned(entry[2]);
  });
  writeArray(data.weakCongs, (entry) => {
    writeBoolean(entry[0]);
    writeString(entry[1]);
  });
  writeArray(data.simprocs, (entry) => {
    writeString(entry[0]);
    writeIds(entry[1]);
  });
  writeStrings(data.loopers);
  writeStrings(data.unsafeSolvers);
  writeStrings(data.safeSolvers);
  writeArray(data.claset.safeIs, writeRule);
  writeArray(data.claset.safeEs, writeRule);
  writeArray(data.claset.unsafeIs, writeRule);
  writeArray(data.claset.unsafeEs, writeRule);
  writeStrings(data.claset.swrappers);
  writeStrings(data.claset.uwrappers);
  writePair(data.claset.safe0, writeItem);
  writePair(data.claset.safep, writeItem);
  writePair(data.claset.unsafe, writeItem);
  writePair(data.claset.dup, writeItem);
  writePair(data.claset.extra, writeExtraItem);
  writePair(data.contextRules.bang, writeExtraItem);
  writePair(data.contextRules.plain, writeExtraItem);

  const head: number[] = [];
  pushUnsigned(head, table.length);
  for (const text of table) {
    const bytes = new TextEncoder().encode(text);
    pushUnsigned(head, bytes.length);
    head.push(...bytes);
  }
  return Uint8Array.from([...head, ...body]);
};

// FNV-1a, 64 bits, of the text's UTF-8 bytes, in hexadecimal.
const getDigest = (text: string) =>
  new TextEncoder()
    .encode(text)
    .reduce(
      (hash, byte) => BigInt.asUintN(64, (hash ^ BigInt(byte)) * 0x100000001b3n),
      0xcbf29ce484222325n,
    )
    .toString(16)
    .padStart(16, "0");

const argument = process.argv[2];
if (argument === undefined)
  throw new Error("Usage: bun scripts/run.ts isabelle-logic <Isabelle-install> | --binary");
const isBinaryOnly = argument === "--binary";
const json = isBinaryOnly ? LOGIC_DATA : JSON.stringify(exportLogic(argument));
if (!isBinaryOnly)
  writeFileSync(
    new URL("../src/prover/isabelle/tla/logic-data.ts", import.meta.url),
    `// Generated by scripts/isabelle-logic.ts from the Isabelle/TLA+ heap that tlapm ships. Do not edit.\n// The theorems come from tlapm's Isabelle/TLA+ theories, BSD licensed, see LICENSE.\n\nexport const LOGIC_DATA = ${JSON.stringify(json)};\n`,
  );
const data: LogicJson = JSON.parse(json);
const binary = encodeLogic(data);
const dataDirectory = new URL("../native/crates/prover/isabelle/data/", import.meta.url);
writeFileSync(new URL("logic.bin", dataDirectory), binary);
writeFileSync(new URL("logic.digest", dataDirectory), `${getDigest(json)}\n`);
console.log(
  `${data.thms.length} theorems, ${data.terms.length} term nodes, ${data.strings.length} strings; ${json.length} bytes of JSON, ${binary.length} bytes of binary`,
);
