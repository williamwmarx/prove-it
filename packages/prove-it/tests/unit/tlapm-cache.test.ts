import { afterAll, describe, expect, it } from "bun:test";
import { spawnSync } from "node:child_process";
import { cpSync, mkdirSync, mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

// The fingerprints tlapm 9ed0376 wrote for tlapm-cli/Failures.tla, which `prove-it tlapm` reads and
// writes through the native engine.
const FIXTURES = join(import.meta.dirname, "../fixtures/tlapm-cli");

// What the TypeScript's cache wrote back for that file once it loaded it, as the Rust's tests hold it.
const RESAVED = join(
  import.meta.dirname,
  "../../native/crates/prover/prover/tests/fixtures/failures-tlapm.resaved",
);

const CLI = join(import.meta.dirname, "../../src/cli.ts");

const copies: string[] = [];

afterAll(() => copies.forEach((copy) => rmSync(copy, { recursive: true, force: true })));

// A copy of the fixtures whose cache holds the fingerprints tlapm wrote.
const copyWithCache = () => {
  const copy = mkdtempSync(join(tmpdir(), "prove-it-fingerprints-"));
  copies.push(copy);
  cpSync(FIXTURES, copy, { recursive: true });
  mkdirSync(join(copy, ".tlacache/Failures.tlaps"), { recursive: true });
  cpSync(join(copy, "Failures.fingerprints"), join(copy, ".tlacache/Failures.tlaps/fingerprints"));
  return copy;
};

const runTlapm = (directory: string, args: string[]) =>
  spawnSync("bun", [CLI, "tlapm", ...args, "Failures.tla"], { cwd: directory, encoding: "utf8" });

// The provers whose results each obligation reuses, in the toolbox's messages.
const getReusedProvers = (args: string[]) =>
  runTlapm(copyWithCache(), ["--noproving", "--toolbox", "0", "0", ...args])
    .stderr.split("@!!BEGIN\n")
    .filter((message) => message.includes("@!!already:true"))
    .map((message) => /^@!!prover:(.*)$/m.exec(message)?.[1]);

describe("tlapm's fingerprints file", () => {
  it("writes back what it reads, in the buckets tlapm hashes each fingerprint into", () => {
    const directory = copyWithCache();
    expect(runTlapm(directory, ["--noproving"]).status).toBe(0);
    expect(readFileSync(join(directory, ".tlacache/Failures.tlaps/fingerprints"))).toEqual(
      readFileSync(RESAVED),
    );
  });

  it("reads what each prover concluded", () => {
    expect(getReusedProvers([])).toEqual(["smt", "zenon", "zenon", "isabelle"]);
  });

  it("trusts no Zenon or Isabelle result of other versions under --safefp", () => {
    expect(getReusedProvers(["--safefp"])).toEqual(["smt"]);
  });
});
