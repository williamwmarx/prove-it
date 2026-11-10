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
  const check = (): Extract<NativeCheckSources, { kind: "checked" }> => {
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
    if (result.kind === "checked") return result;
    result.keys.forEach((key) => known.set(key, readKey(directory, args, key)));
    return check();
  };
  const result = check();
  return getTranscript(String(result.exitCode), result.out, result.err);
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
  return getTranscript(String(run.status), run.stdout, run.stderr);
};

describe("checkSources", () => {
  it.each(CASES)("prints what the binary prints for $name", (test) => {
    const directory = getDirectory(test);
    const args = ["-noGenerateSpecTE", ...test.args];
    expect(checkInProcess(directory, args)).toBe(checkWithBinary(directory, test.args));
    rmSync(directory, { recursive: true, force: true });
  });
});
