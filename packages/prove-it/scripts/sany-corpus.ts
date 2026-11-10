// Runs the native binary on TLC's own tests of SANY, the specs of test/tla2sany/semantic's
// error_corpus, each a SANY error, and corpus, which SANY accepts, each with an empty
// configuration, and counts the specs on which it prints what TLC prints, declines, or differs.
// `--specs` runs the specs of another directory instead, such as
// native/crates/tla-front/tests/recursive-shapes.
//
// TLC runs live from the classpath of a tla2tools build (`--classpath`), and `--record` writes what
// it prints to a file instead of running the binary. `--recorded` holds the binary to such a file
// with no TLC, as Verification does with tests/conformance/sany-stdout; `--cli` holds the CLI of
// dist/ to it too. Without `--tlaplus` or `--specs`, it reads the `sany` corpus that
// fetch-corpora.ts fetches. `--main` names the class the jar runs, tlc2.TLC by default, such as
// tla2sany.xml.XMLExporter, and `--arguments` the arguments every run takes before the spec's name,
// TLC's below by default. `--names` runs only the specs it names, which may be in a directory of
// `--specs` that `-I` names. Each run is in a copy of the whole directory. XMLExporter's XML is
// recorded by its SHA-256 and length, as the corpus's would be hundreds of megabytes.
// Usage: bun scripts/sany-corpus.ts [--tlaplus <clone> | --specs <directory>]
//   (--classpath <tla2tools> [--record <file>] | --recorded <file> [--cli]) [--native <binary>]
//   [--main <class>] [--arguments "<argument> ..."] [--names <name>,...]

import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import {
  cpSync,
  mkdtempSync,
  readdirSync,
  readFileSync,
  realpathSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { basename, join, resolve } from "node:path";

import { CORPORA_DIRECTORY } from "./corpora";
import { getTranscript } from "./normalize-output";

const getOption = (name: string) => {
  const index = process.argv.indexOf(name);
  return index === -1 ? undefined : process.argv[index + 1];
};

const tlaplus = getOption("--tlaplus");
const specDirectory = getOption("--specs");
const classpath = getOption("--classpath");
const recordPath = getOption("--record");
const recordedPath = getOption("--recorded");
const isCliChecked = process.argv.includes("--cli");
if (
  (tlaplus !== undefined && specDirectory !== undefined) ||
  (classpath === undefined) === (recordedPath === undefined) ||
  (recordPath !== undefined && classpath === undefined) ||
  (isCliChecked && recordedPath === undefined)
) {
  console.error(
    "usage: bun scripts/sany-corpus.ts [--tlaplus <clone> | --specs <directory>] (--classpath <tla2tools> [--record <file>] | --recorded <file> [--cli]) [--native <binary>] [--main <class>] [--arguments \"<argument> ...\"] [--names <name>,...]",
  );
  process.exit(2);
}
// Resolved here, since each run is from a directory of its own.
const native = resolve(
  getOption("--native") ?? join(import.meta.dirname, "../native/target/release/prove-it"),
);
const cli = join(import.meta.dirname, "../dist/cli.js");
const main = getOption("--main") ?? "tlc2.TLC";
const ARGUMENTS = getOption("--arguments")?.split(" ") ?? [
  "-nowarning",
  "-noGenerateSpecTE",
  "-workers",
  "1",
  "-fp",
  "0",
  "-seed",
  "0",
];
const names = getOption("--names")?.split(",");

// What a run printed, with what differs between two runs of the same spec rewritten, and without
// the JVM's note of the options it was given. TLC built as a directory of classes reads the
// standard modules where they are, which TLC from its jar extracts to a temporary directory first.
// The directory of the run, which a missing file's message names, is written as `.`.
const run = (command: string, args: string[], directory: string) => {
  const result = spawnSync(command, args, { cwd: directory, encoding: "utf8" });
  const stdout = result.stdout.replace(
    /^(Parsing file )\S*\/tla2sany\/StandardModules\//gm,
    "$1/tmp/tlc-0/",
  );
  const stderr = result.stderr
    .replace(/^Picked up JAVA_TOOL_OPTIONS:.*\n/gm, "")
    .replaceAll(realpathSync(directory), ".")
    .replaceAll(directory, ".");
  const xml = stdout.startsWith("<?xml")
    ? `XML of SHA-256 ${createHash("sha256").update(stdout).digest("hex")}, ${Buffer.byteLength(stdout)} bytes\n`
    : stdout;
  return getTranscript(String(result.status), xml, stderr);
};

const semantic = join(
  tlaplus ?? join(CORPORA_DIRECTORY, "sany"),
  "tlatools/org.lamport.tlatools/test/tla2sany/semantic",
);
const corpora =
  specDirectory === undefined
    ? ["error_corpus", "corpus"].map((corpus) => join(semantic, corpus))
    : [resolve(specDirectory)];
const recorded: Record<string, string> =
  recordedPath === undefined ? {} : JSON.parse(readFileSync(recordedPath, "utf8"));
const recording: Record<string, string> = {};
const counts = { same: 0, declined: 0, differs: 0 };
const count = (id: string, expected: string, actual: string) => {
  const outcome = actual.includes("prove-it: not native yet: ")
    ? "declined"
    : actual === expected
      ? "same"
      : "differs";
  counts[outcome] += 1;
  if (outcome !== "same") console.log(`${outcome} ${id}`);
};
for (const source of corpora) {
  const corpus = basename(source);
  const specs =
    names ??
    readdirSync(source)
      .filter((file) => file.endsWith(".tla"))
      .map((file) => file.slice(0, -".tla".length));
  for (const name of specs.toSorted()) {
    const id = `${corpus}/${name}`;
    const directory = mkdtempSync(join(tmpdir(), "sany-corpus-"));
    cpSync(source, directory, { recursive: true });
    writeFileSync(join(directory, `${name}.cfg`), "");
    const expected =
      classpath === undefined
        ? recorded[id]
        : run("java", ["-cp", classpath, main, ...ARGUMENTS, name], directory);
    if (expected === undefined) throw new Error(`${recordedPath} records nothing for ${id}`);
    if (recordPath !== undefined) recording[id] = expected;
    else {
      count(id, expected, run(native, [main, ...ARGUMENTS, name], directory));
      if (isCliChecked) {
        count(`${id} (cli)`, expected, run("node", [cli, main, ...ARGUMENTS, name], directory));
      }
    }
    rmSync(directory, { recursive: true, force: true });
  }
}
if (recordPath !== undefined) {
  writeFileSync(recordPath, `${JSON.stringify(recording, null, 2)}\n`);
  console.log(`recorded ${Object.keys(recording).length} specs in ${recordPath}`);
  process.exit(0);
}
console.log(
  `${counts.same} print what TLC prints, ${counts.declined} decline, ${counts.differs} differ`,
);
process.exit(counts.differs === 0 ? 0 : 1);
