// checkSources runs the native binary's check in-process, reading the spec's files from what it is
// given: driven through the engine with the CLI's loader, it prints what the binary prints for the
// same files.

import { describe, expect, it } from "bun:test";
import { spawnSync } from "node:child_process";
import {
  cpSync,
  existsSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { cpus, release, tmpdir, totalmem, type } from "node:os";
import { dirname, join, resolve } from "node:path";

import { getTranscript } from "../../scripts/normalize-output";
import { getBuiltAddon } from "../../scripts/platform-packages";
import { readFileKey } from "../../src/cli/shared";
import { checkAllSources, getNativeAddon } from "../../src/engine/native";

const FIXTURES = join(import.meta.dirname, "..", "fixtures");
const BINARY = join(dirname(getBuiltAddon() ?? ""), "bin", "prove-it");
const JARS = join(import.meta.dirname, "../../native/crates/prove-it-check/fixtures");

interface Case {
  name: string;
  fixture: string;
  files?: Record<string, string>;
  removed?: string[];
  // The Java launch in front of TLC's options, such as the tla2tools.jar on the class path.
  java?: string[];
  args: string[];
}

const CASES: Case[] = [
  { name: "a spec that holds", fixture: "counter", args: ["-deadlock", "Counter.tla"] },
  {
    name: "an invariant of a spec that extends a module beside it, violated with its trace",
    fixture: "counter",
    files: {
      "Bounded.tla": "---- MODULE Bounded ----\nEXTENDS Counter\nBelow == count < 2\n====\n",
      "Bounded.cfg": "INIT Init\nNEXT Next\nCONSTANT Limit = 3\nINVARIANT Below\n",
    },
    args: ["Bounded.tla"],
  },
  {
    name: "a liveness violation",
    fixture: "liveness",
    args: ["-config", "Unfair-ReachesLimit.cfg", "Liveness.tla"],
  },
  {
    name: "a missing configuration",
    fixture: "counter",
    removed: ["Counter.cfg"],
    args: ["Counter.tla"],
  },
  {
    name: "a spec that instantiates a module beside it",
    fixture: "modules",
    args: ["Counters.tla"],
  },
  {
    name: "a Java override, which both decline",
    fixture: "overrides",
    files: { "Overrides.cfg": "" },
    args: ["Overrides.tla"],
  },
  {
    name: "a Java launch with a tla2tools.jar on the class path",
    fixture: "counter",
    java: ["-cp", join(JARS, "tla2tools.jar"), "tlc2.TLC"],
    args: ["-deadlock", "Counter.tla"],
  },
  {
    name: "a Java launch with TLC 1.7.4's jar, which both decline",
    fixture: "counter",
    java: ["-cp", join(JARS, "tla2tools-1.7.4.jar"), "tlc2.TLC"],
    args: ["-deadlock", "Counter.tla"],
  },
];

// The fixture copied into a directory of its own, with the case's files written and removed.
const getDirectory = (test: Case) => {
  const directory = mkdtempSync(join(tmpdir(), "prove-it-check-sources-"));
  cpSync(join(FIXTURES, test.fixture), directory, { recursive: true });
  Object.entries(test.files ?? {}).forEach(([name, text]) =>
    writeFileSync(join(directory, name), text),
  );
  test.removed?.forEach((name) => rmSync(join(directory, name)));
  return directory;
};

const getSpecPath = (directory: string, args: string[]) => resolve(directory, args.at(-1) ?? "");

// What the engine reads of the files, by the keys check.rs names them by, as the CLI answers them
// from the directory the binary runs in.
const readKey = (directory: string, key: string) => {
  const [kind, ...rest] = key.split(":");
  if (kind === "cwd") return directory;
  return readFileKey(rest.length === 0 ? kind : `${kind}:${resolve(directory, rest.join(":"))}`);
};

// What the library answers: the spec's text, and a module beside it by its name.
const readLibraryKey = (directory: string, key: string) => {
  const [kind, ...rest] = key.split(":");
  const name = rest.join(":");
  const path = kind === "module" ? join(directory, `${name}.tla`) : resolve(directory, name);
  return ["text", "module"].includes(kind) && existsSync(path)
    ? readFileSync(path, "utf8")
    : undefined;
};

const getAddon = () => {
  const addon = getNativeAddon();
  if (typeof addon === "string") throw new Error(addon);
  return addon;
};

const checkInProcess = (directory: string, args: string[]) => {
  const result = checkAllSources(
    getAddon(),
    args.map((arg) => (arg.endsWith(".tla") ? getSpecPath(directory, [arg]) : arg)),
    [
      type(),
      release(),
      process.arch,
      cpus().length,
      Math.floor(totalmem() / 1024 / 1024),
      process.pid,
      Date.now(),
      "UTC0",
      [],
      false,
    ],
    (key) => readKey(directory, key),
  );
  return result.kind === "declined"
    ? `declined: ${result.reason}`
    : getTranscript(String(result.exitCode), result.out, result.err);
};

const checkWithBinary = (directory: string, args: string[]) => {
  const run = spawnSync(
    BINARY,
    args.map((arg) => (arg.endsWith(".tla") ? getSpecPath(directory, [arg]) : arg)),
    { cwd: directory, encoding: "utf8", env: { ...process.env, TZ: "UTC" } },
  );
  const declined = /^prove-it: not native yet: (.*)$/m.exec(run.stderr);
  return declined
    ? `declined: ${declined[1]}`
    : getTranscript(String(run.status), run.stdout, run.stderr);
};

describe("checkSources", () => {
  it.each(CASES)("prints what the binary prints, or declines as it does, for $name", (test) => {
    const directory = getDirectory(test);
    const args = [...(test.java ?? []), "-noGenerateSpecTE", ...test.args];
    expect(checkInProcess(directory, args)).toBe(checkWithBinary(directory, args));
    rmSync(directory, { recursive: true, force: true });
  });

  it("returns what it found beside what it prints, where it searched", () => {
    const getOutcome = (test: Case) => {
      const directory = getDirectory(test);
      const result = checkAllSources(
        getAddon(),
        ["-noGenerateSpecTE", getSpecPath(directory, test.args)],
        ["", "", "", 1, 0, 0, 0, "UTC0", [], true],
        (key) => readLibraryKey(directory, key),
      );
      rmSync(directory, { recursive: true, force: true });
      if (result.kind === "declined") throw new Error(result.reason);
      return result.outcome;
    };
    const outcome = getOutcome(CASES[1]);
    expect([outcome?.status, outcome?.violations.map((violation) => violation.headline)]).toEqual([
      "invariant-violation",
      ["Invariant Below is violated."],
    ]);
    expect(outcome?.violations[0].states.map((state) => [state.label, state.variables])).toEqual([
      ["Initial predicate", [["count", "0", "0"]]],
      [expect.stringMatching(/^Increment line /), [["count", "1", "1"]]],
      [expect.stringMatching(/^Increment line /), [["count", "2", "2"]]],
    ]);
    expect(getOutcome(CASES[3])).toBeUndefined();
  });

  // The CLI says before the search whether it can write each file the check writes after it, so
  // writing a counterexample's files asks for nothing that would search again.
  it.each([[[]], [["-dumpTrace", "json", "x.json"]], [["-dumpTrace", "tlc", "out/x.bin"]]])(
    "asks for every key before it searches, with %j",
    (options) => {
      const directory = getDirectory({ name: "", fixture: "water-jugs", args: [] });
      mkdirSync(join(directory, "out"));
      const getRounds = (args: string[]) => {
        const addon = getAddon();
        const rounds: string[] = [];
        const result = checkAllSources(
          {
            ...addon,
            checkSources: (...inputs) => {
              const round = addon.checkSources(...inputs);
              rounds.push(round.kind);
              return round;
            },
          },
          [...args, getSpecPath(directory, ["WaterJugs.tla"])],
          [type(), release(), process.arch, 1, 1024, process.pid, Date.now(), "UTC0", [], false],
          (key) => readKey(directory, key),
        );
        expect(result.kind).toBe("checked");
        return rounds.length;
      };
      expect(getRounds(options)).toBe(getRounds(["-noGenerateSpecTE"]));
      rmSync(directory, { recursive: true, force: true });
    },
  );

  // The library answers for files itself: the files the check writes come back in order, and the
  // binary writes the same bytes to the machine's.
  it("returns the files the library's check writes, as the binary writes them", () => {
    const test = CASES[0];
    const directory = getDirectory(test);
    const dumped = join(directory, "states.dump");
    const result = checkAllSources(
      getAddon(),
      ["-noGenerateSpecTE", "-deadlock", "-dump", dumped, getSpecPath(directory, test.args)],
      ["", "", "", 1, 0, 0, 0, "UTC0", [], true],
      (key) => readLibraryKey(directory, key),
    );
    if (result.kind !== "checked") throw new Error(JSON.stringify(result));
    const written = result.writes.reduce(
      (files, write) =>
        files.set(
          write.path,
          (write.isAppended ? (files.get(write.path) ?? "") : "") +
            new TextDecoder().decode(write.bytes),
        ),
      new Map<string, string>(),
    );
    expect([...written.keys()]).toEqual([dumped]);
    spawnSync(BINARY, ["-noGenerateSpecTE", "-deadlock", "-dump", dumped, "Counter.tla"], {
      cwd: directory,
    });
    expect(written.get(dumped)).toBe(readFileSync(dumped, "utf8"));
    rmSync(directory, { recursive: true, force: true });
  });

  // WebAssembly's frames are on the host's stack, so its engine stops recursing sooner.
  it.if(process.env.PROVE_IT_ENGINE_WASM !== undefined)(
    "declines recursion deeper than WebAssembly's stack holds, where the addon recurses",
    () => {
      const directory = mkdtempSync(join(tmpdir(), "prove-it-check-sources-"));
      writeFileSync(
        join(directory, "Deep.tla"),
        "---- MODULE Deep ----\nEXTENDS Naturals\nRECURSIVE F(_)\nF(n) == IF n = 0 THEN 0 ELSE 1 + F(n - 1)\nVARIABLE x\nInit == x = 0\nNext == x < 1 /\\ x' = F(5000) - 4999\n====\n",
      );
      writeFileSync(join(directory, "Deep.cfg"), "INIT Init\nNEXT Next\n");
      expect(checkInProcess(directory, ["-noGenerateSpecTE", "-deadlock", "Deep.tla"])).toBe(
        "declined: the engine stopped: recursion deeper than WebAssembly's stack holds",
      );
      rmSync(directory, { recursive: true, force: true });
    },
  );
});
