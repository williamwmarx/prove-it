import { describe, expect, it } from "bun:test";
import { spawnSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { getTranscript, normalizeOutput } from "../../scripts/normalize-output";

const FIXTURES = join(import.meta.dirname, "../fixtures");

const CLI = join(import.meta.dirname, "../../src/cli.ts");

// TLC's output on these, as record-tlc.ts --stdout runs it, is in tests/fixtures/tlc-output.
const MODELS = ["Success", "FailedInvariant", "Lasso"];

const RUNS = MODELS.flatMap((name) => [
  [name, []],
  [`${name}-tool`, ["-tool"]],
]) as [string, string[]][];

const readTlcOutput = (name: string) =>
  readFileSync(join(FIXTURES, "tlc-output", `${name}.out`), "utf8");

const runCli = (name: string, args: string[]) =>
  spawnSync(
    "bun",
    [
      CLI,
      "tlc2.TLC",
      "-workers",
      "1",
      "-nowarning",
      "-seed",
      "4",
      "-fp",
      "0",
      "-lncheck",
      "final",
      "-noGenerateSpecTE",
      ...args,
      `${name}.tla`,
    ],
    { cwd: join(FIXTURES, "cli-output"), encoding: "utf8" },
  ).stdout;

// Each of these changes what TLC found, everywhere it prints it, so the normalised output must
// change too.
const MUTATIONS: [RegExp, string][] = [
  [/(\d+) states generated, /g, "99 states generated, "],
  [/, (\d+) distinct states found/g, ", 99 distinct states found"],
  [/(\d+) states left on queue/g, "99 states left on queue"],
  [
    /The depth of the complete state graph search is \d+/g,
    "The depth of the complete state graph search is 99",
  ],
  [/minimum is \d+/g, "minimum is 99"],
  [/val = [\d.E-]+/g, "val = 9.9E-99"],
  [/^x = \d+$/gm, "x = 99"],
  [/^State 2: /gm, "State 3: "],
  [/@!@!@STARTMSG 2110:1 @!@!@/g, "@!@!@STARTMSG 2111:1 @!@!@"],
  [/distinct states? generated at /g, "distinct states generated after "],
  [/Inv/g, "Invariant"],
];

describe("normalizeOutput", () => {
  it.each(RUNS)("makes Prove It's output on %s the same as TLC's", (name, args) => {
    expect(normalizeOutput(runCli(name.replace(/-tool$/, ""), args))).toBe(
      normalizeOutput(readTlcOutput(name)),
    );
  });

  it.each(RUNS)("keeps every change in what TLC found on %s", (name) => {
    const output = readTlcOutput(name);
    for (const [pattern, replacement] of MUTATIONS) {
      const mutated = output.replace(pattern, replacement);
      if (mutated === output) continue;
      expect(normalizeOutput(mutated)).not.toBe(normalizeOutput(output));
      expect(normalizeOutput(mutated)).toContain(replacement.trim());
    }
  });

  it("rewrites what differs between runs", () => {
    const output = readTlcOutput("Success-tool");
    const rerun = output
      .replace(/\[pid: \d+\]/, "[pid: 1]")
      .replace(/with \d+MB heap and \d+MB offheap/, "with 1MB heap and 2MB offheap")
      .replace(/on \d+ cores/, "on 64 cores")
      .replace(/\d\d:\d\d:\d\d/g, "23:59:59")
      .replace(/\/tmp\/tlc-\d+\//g, "/tmp/tlc-1/")
      .replace(/Parsing file \/\S+\/Success.tla/, "Parsing file /elsewhere/Success.tla")
      .replace(/Finished in \d+ms/, "Finished in 61001ms")
      .replace(/TLC2 Version .*/, "TLC2 Version 2.20 of Day Month 20?? (rev: abcdef0)");
    expect(rerun).not.toBe(output);
    expect(normalizeOutput(rerun)).toBe(normalizeOutput(output));
  });

  it.each(["Lasso", "Lasso-tool"])(
    "drops the Progress lines of %s, whose presence depends on how long the run takes",
    (name) => {
      const output = readTlcOutput(name);
      expect(output).toContain("Progress(");
      expect(normalizeOutput(output)).not.toContain("Progress(");
      expect(normalizeOutput(output)).not.toContain(" 2200");
    },
  );

  it("rewrites each form of TLC's durations", () => {
    expect(
      ["494ms", "05s", "02min 05s", "01h 02min", "1d 01h"].map((duration) =>
        normalizeOutput(`Finished in ${duration} at (2026-11-08 06:59:23)`),
      ),
    ).toEqual(new Array(5).fill("Finished in _ at (_)"));
  });
});

describe("getTranscript", () => {
  it("keeps the exit code and stderr, without the engine's notes", () => {
    expect(
      getTranscript(
        "12",
        "Starting... (2026-11-08 06:59:23)\n",
        "[engine] checked 6 states\noops\n",
      ),
    ).toBe("exit 12\nStarting... (_)\n\n--- stderr\noops\n");
    expect(getTranscript("0", "done\n", "[engine] skipped: disabled\n")).toBe("exit 0\ndone\n");
  });
});
