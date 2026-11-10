// checkSources runs the native binary's check in-process, reading the spec's files from what it is
// given: driven through the engine with the CLI's loader, it prints what the binary prints for the
// same files.

import { describe, expect, it } from "bun:test";
import { spawnSync } from "node:child_process";
import { cpSync, existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { cpus, release, tmpdir, totalmem, type } from "node:os";
import { dirname, join, resolve } from "node:path";

import { getTranscript } from "../../scripts/normalize-output";
import { getBuiltAddon } from "../../scripts/platform-packages";
import { createModuleLoader } from "../../src/cli/shared";
import { createFileDescriber } from "../../src/cli/tlc";
import { getNativeAddon, type NativeCheckSources } from "../../src/engine/native";
import type { SanyModuleOrigin } from "../../src/sany/report";

const FIXTURES = join(import.meta.dirname, "..", "fixtures");
const BINARY = join(dirname(getBuiltAddon() ?? ""), "bin", "prove-it");

interface Case {
  name: string;
  fixture: string;
  files?: Record<string, string>;
  removed?: string[];
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

// What the engine reads for the spec in the directory, by the keys check.rs names it by.
const readKey = (directory: string, args: string[], key: string) => {
  const [kind, ...rest] = key.split(":");
  const name = rest.join(":");
  if (kind === "text") {
    const path = resolve(directory, name);
    return existsSync(path) ? readFileSync(path, "utf8") : undefined;
  }
  if (kind === "module") return createModuleLoader([directory])(name);
  if (kind === "class") {
    const path = join(directory, `${name}.class`);
    return existsSync(path) ? new Uint8Array(readFileSync(path)) : undefined;
  }
  const [origin, ...moduleName] = rest;
  return createFileDescriber(
    getSpecPath(directory, args),
    [directory],
    { libraries: [], properties: new Map() },
    undefined,
    "master",
  )(moduleName.join(":"), origin as SanyModuleOrigin);
};

const checkInProcess = (directory: string, args: string[]) => {
  const addon = getNativeAddon();
  if (typeof addon === "string") throw new Error(addon);
  const known = new Map<string, string | Uint8Array | undefined>();
  const check = (): Exclude<NativeCheckSources, { kind: "needed" }> => {
    const result = addon.checkSources(
      args.map((arg) => (arg.endsWith(".tla") ? getSpecPath(directory, [arg]) : arg)),
      [...known],
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
      ],
    );
    if (result.kind !== "needed") return result;
    result.keys.forEach((key) => known.set(key, readKey(directory, args, key)));
    return check();
  };
  const result = check();
  return result.kind === "declined"
    ? `declined: ${result.reason}`
    : getTranscript(String(result.exitCode), result.out, result.err);
};

const checkWithBinary = (directory: string, args: string[]) => {
  const run = spawnSync(
    BINARY,
    [
      "-noGenerateSpecTE",
      ...args.map((arg) => (arg.endsWith(".tla") ? getSpecPath(directory, [arg]) : arg)),
    ],
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
    const args = ["-noGenerateSpecTE", ...test.args];
    expect(checkInProcess(directory, args)).toBe(checkWithBinary(directory, test.args));
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
        "declined: the engine stopped: recursion too deep",
      );
      rmSync(directory, { recursive: true, force: true });
    },
  );
});
