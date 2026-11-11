// Records what the TypeScript's OCaml Marshal and fingerprints file do, which the Rust ports'
// tests in native/crates/prover/prover/tests compare with byte for byte:
// - marshal.txt: one line per value, the bytes the TypeScript writes for it, then the bytes it
//   writes for what it reads back from them. A value written by hand with OCaml's sharing codes
//   gives its input bytes instead, which only reading reaches.
// - <name>.fingerprints and <name>.resaved: a fingerprints file `prove-it tlapm` writes on a
//   fixture module (Failures.tla as tlapm wrote it), and what loading and saving it writes again.
// Usage: bun scripts/tlapm-cache-fixtures.ts (after bun run build)

import { execFileSync } from "node:child_process";
import { cpSync, mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { getKnownResults, loadFingerprints } from "../src/prover/tlapm/cache";
import {
  block,
  type OcamlValue,
  readMarshaled,
  writeMarshaled,
} from "../src/prover/tlapm/ocaml-marshal";

const ROOT = join(import.meta.dirname, "..");
const OUTPUT = join(ROOT, "native/crates/prover/prover/tests/fixtures");
const CLI_FIXTURES = join(ROOT, "tests/fixtures/tlapm-cli");

const toHex = (bytes: Uint8Array) => Buffer.from(bytes).toString("hex");

const getString = (length: number) => "ab".repeat(length).slice(0, length);

const INTEGERS = [
  0, 1, 63, 64, 127, 128, -1, -64, -128, -129, 255, 256, 32767, 32768, -32768, -32769, 65535,
  2147483647, -2147483648, 20210223,
];

const FLOATS = [0, -0, 1, 0.5, 3, 15, 1e300, -2.75, Infinity, -Infinity];

const STRINGS = [...[0, 1, 31, 32, 255, 256, 1000].map(getString), "tla-ts 0.3.0", "π ≤ ∀ 🙂"];

const VALUES: OcamlValue[] = [
  ...INTEGERS,
  ...FLOATS.map((float) => ({ float })),
  ...STRINGS,
  block(0),
  block(3),
  block(0, 1, 2),
  block(15, 1, 2, 3, 4, 5, 6, 7),
  block(15, 1, 2, 3, 4, 5, 6, 7, 8),
  block(16, 1),
  block(255, "x"),
  block(0, ...Array.from({ length: 600 }, (_, index) => index)),
  block(0, block(1, block(2, "deep", { float: 1.5 }), 0), "", block(0)),
  block(0, "same", "same", block(0, { float: 2 }), block(0, { float: 2 })),
];

const header = (length: number) => {
  const bytes = new Uint8Array(20);
  const view = new DataView(bytes.buffer);
  [0x8495a6be, length, 0, 0, 0].forEach((field, index) => view.setUint32(index * 4, field));
  return bytes;
};

// OCaml's sharing codes, which the TypeScript reads but never writes: shared8, shared16 and
// shared32 to a string, a float and a block, at distances 1 and more.
const SHARED: number[][] = [
  [0xa0, 0x23, 0x61, 0x62, 0x63, 0x04, 0x01],
  [0xa0, 0x0c, 0, 0, 0, 0, 0, 0, 0xf8, 0x3f, 0x05, 0x00, 0x01],
  [0xb0, 0x21, 0x78, 0x91, 0x41, 0x06, 0, 0, 0, 0x01],
  [0xb0, 0x21, 0x61, 0x21, 0x62, 0x04, 0x02],
  [0xa0, 0x91, 0x22, 0x68, 0x69, 0x04, 0x01],
];

const getLine = (input: Uint8Array) =>
  `${toHex(input)} ${toHex(writeMarshaled(readMarshaled(input, 0).value))}`;

const lines = [
  ...VALUES.map((value) => getLine(writeMarshaled(value))),
  ...SHARED.map((data) => getLine(new Uint8Array([...header(data.length), ...data]))),
];
mkdirSync(OUTPUT, { recursive: true });
writeFileSync(join(OUTPUT, "marshal.txt"), `${lines.join("\n")}\n`);

const resave = (name: string, input: string) => {
  const table = new Map();
  loadFingerprints(table, input, false);
  cpSync(input, join(OUTPUT, `${name}.fingerprints`));
  getKnownResults(table).save(join(OUTPUT, `${name}.resaved`));
};

resave("failures-tlapm", join(CLI_FIXTURES, "Failures.fingerprints"));

// What `prove-it tlapm` itself writes, with and without --nofp, which saves over the file it loads.
const directory = mkdtempSync(join(tmpdir(), "tlapm-cache-fixtures-"));
for (const name of ["Failures", "Twice"]) {
  cpSync(join(CLI_FIXTURES, `${name}.tla`), join(directory, `${name}.tla`));
  for (const options of [[], ["--nofp"]]) {
    try {
      execFileSync("bun", [join(ROOT, "dist/cli.js"), "tlapm", ...options, `${name}.tla`], {
        cwd: directory,
        stdio: "ignore",
      });
    } catch {
      // A module with failed obligations exits non-zero, and still writes its fingerprints.
    }
    const suffix = options.length === 0 ? "" : "-nofp";
    resave(
      `${name.toLowerCase()}${suffix}`,
      join(directory, ".tlacache", `${name}.tlaps`, "fingerprints"),
    );
  }
}
rmSync(directory, { recursive: true, force: true });
