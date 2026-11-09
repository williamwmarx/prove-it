import { afterAll, describe, expect, it } from "bun:test";
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { getStateLogDifference } from "../../scripts/state-logs";
import { getTlcFingerprint } from "../../src/tlc/fingerprint";
import { createStateDecoder } from "../../src/transfer";
import { setStringOrder } from "../../src/values";

// The CLI runs from the build, which bun run test makes first.
const CLI = join(import.meta.dirname, "../../dist/cli.js");

const directory = mkdtempSync(join(tmpdir(), "prove-it-state-log-"));

afterAll(() => rmSync(directory, { recursive: true, force: true }));

const logRun = (
  directoryPath: string,
  name: string,
  logName: string,
  environment: Record<string, string> = {},
) => {
  const path = join(directory, `${logName}.jsonl`);
  const result = spawnSync("bun", [CLI, `${name}.tla`], {
    cwd: directoryPath,
    encoding: "utf8",
    env: { ...process.env, PROVE_IT_ENGINE: "debug", PROVE_IT_STATE_LOG: path, ...environment },
  });
  return { stderr: result.stderr, log: readFileSync(path, "utf8") };
};

const FIXTURES = join(import.meta.dirname, "../fixtures");

describe("PROVE_IT_STATE_LOG", () => {
  it("writes each state's parent and TLC's fingerprint, in TLC's order", () => {
    const lines = logRun(join(FIXTURES, "cli-output"), "Success", "success").log.split("\n");
    expect(JSON.parse(lines[0])).toEqual({
      version: 1,
      variables: ["x"],
      count: 6,
      stopped: null,
      expanding: 6,
      order: [0],
      strings: expect.arrayContaining(["x"]),
    });
    const states = lines.slice(1, -1).map((line) => JSON.parse(line));
    expect(states.map((state) => state.slice(0, 3))).toEqual([
      [0, -1, -1],
      [1, -1, -1],
      [2, 0, -1],
      [3, 1, -1],
      [4, 2, -1],
      [5, 3, -1],
    ]);
    expect(states.every((state) => /^[\da-f]{16}$/.test(state[3]))).toBe(true);
    expect(new Set(states.map((state) => state[3])).size).toBe(6);
  });

  it("writes the states found before the engine stopped", () => {
    const run = logRun(join(FIXTURES, "water-jugs"), "WaterJugs", "violation");
    expect(run.stderr).toContain("handed over after");
    const header = JSON.parse(run.log.split("\n")[0]);
    expect(header.stopped).toBe("an invariant violated");
    expect(header.count).toBeGreaterThan(header.expanding);
  });

  it("names the first state two logs differ in, and prints it and its parent", () => {
    const log = logRun(join(FIXTURES, "water-jugs"), "WaterJugs", "original").log;
    const lines = log.split("\n");
    const record = JSON.parse(lines[4]);
    lines[4] = JSON.stringify([...record.slice(0, 3), "0000000000000000", ...record.slice(4)]);
    const difference = getStateLogDifference(log.split("\n"), lines) ?? "";
    expect(difference.split("\n")[0]).toBe("state 3:");
    expect(difference).toContain(`with fingerprint ${record[3]} from ${record[1]} (`);
    expect(difference).toContain("with fingerprint 0000000000000000 from");
    expect(difference).toMatch(/left reached \/\\ small = \d+ \/\\ big = \d+|left reached \w+ = /);
  });

  // Specs whose fingerprints read the state, a VIEW's value, and a representative under symmetry,
  // with model values, whose fingerprints are by TLC's order of strings.
  it.each([
    [
      "the state",
      [
        "VARIABLES x, y",
        "Init == x = 0 /\\ y = <<>>",
        "Next == x' = (x + 1) % 10 /\\ y' = IF x = 9 THEN <<>> ELSE y \\o <<x>>",
      ],
      "INIT Init\nNEXT Next",
      undefined,
    ],
    [
      "a VIEW's value",
      [
        "VARIABLES a, b",
        "Init == a = 0 /\\ b = 0",
        "Next == a' = (a + 1) % 5 /\\ b' = (b + a) % 7",
        "View == <<a, b % 3>>",
      ],
      "INIT Init\nNEXT Next\nVIEW View",
      1,
    ],
    [
      "a representative under symmetry",
      [
        "CONSTANT P",
        "VARIABLES x, z",
        "Init == x = [p \\in P |-> 0] /\\ z = CHOOSE p \\in P : TRUE",
        "Next == \\E p \\in P : x' = [x EXCEPT ![p] = (x[p] + 1) % 3] /\\ z' = p",
        "Sym == Permutations(P)",
      ],
      "CONSTANT P = {p1, p2, p3}\nINIT Init\nNEXT Next\nSYMMETRY Sym",
      2,
    ],
  ])(
    "writes what another store needs to fingerprint each state again, keyed by %s",
    (name, body, config, keyWidth) => {
      const specDirectory = mkdtempSync(join(directory, "keys-"));
      writeFileSync(
        join(specDirectory, "M.tla"),
        ["---- MODULE M ----", "EXTENDS Naturals, Sequences, TLC", ...body, "===="].join("\n"),
      );
      writeFileSync(join(specDirectory, "M.cfg"), config);
      const run = logRun(specDirectory, "M", name.replaceAll(" ", "-"));
      expect(run.stderr).toContain("[engine] checked ");
      const lines = run.log.split("\n").filter((line) => line !== "");
      const header = JSON.parse(lines[0]);
      expect(header.keyWidth).toBe(keyWidth);
      setStringOrder(header.strings);
      const width = keyWidth ?? header.variables.length;
      for (const line of lines.slice(1)) {
        const record = JSON.parse(line);
        const [words, strings] = keyWidth === undefined ? record.slice(4, 6) : record.slice(6, 8);
        const key = createStateDecoder(width)({
          words: Int32Array.from(words),
          strings,
          count: 1,
        })[0];
        const fingerprint = getTlcFingerprint(header.order.map((index: number) => key[index]));
        expect(BigInt.asUintN(64, fingerprint).toString(16).padStart(16, "0")).toBe(record[3]);
      }
      expect(lines.length).toBeGreaterThan(3);
    },
  );
});
