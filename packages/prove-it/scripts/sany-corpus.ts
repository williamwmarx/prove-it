// Runs TLC and the native binary on TLC's own tests of SANY, the specs of a tlaplus clone's
// test/tla2sany/semantic/error_corpus, each a SANY error, and corpus, which SANY accepts, each with
// an empty configuration, and counts the specs on which the binary prints what TLC prints, declines,
// or differs. TLC runs live, from the classpath of a tla2tools build; the recorded gate comes with
// the port of SANY's generator to tla-front (native/design/front.md).
// Usage: bun scripts/sany-corpus.ts --tlaplus <clone> --classpath <tla2tools> [--native <binary>]

import { spawnSync } from "node:child_process";
import { cpSync, mkdtempSync, readdirSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { getTranscript } from "./normalize-output";

const getOption = (name: string) => {
  const index = process.argv.indexOf(name);
  return index === -1 ? undefined : process.argv[index + 1];
};

const tlaplus = getOption("--tlaplus");
const classpath = getOption("--classpath");
if (tlaplus === undefined || classpath === undefined) {
  console.error(
    "usage: bun scripts/sany-corpus.ts --tlaplus <clone> --classpath <tla2tools> [--native <binary>]",
  );
  process.exit(2);
}
const native =
  getOption("--native") ?? join(import.meta.dirname, "../native/target/release/prove-it");
const ARGUMENTS = ["-nowarning", "-noGenerateSpecTE", "-workers", "1", "-fp", "0", "-seed", "0"];
const SEMANTIC = join(tlaplus, "tlatools/org.lamport.tlatools/test/tla2sany/semantic");

// What a run printed, with what differs between two runs of the same spec rewritten, and without
// the JVM's note of the options it was given. TLC built as a directory of classes reads the
// standard modules where they are, which TLC from its jar extracts to a temporary directory first.
const run = (command: string, args: string[], directory: string) => {
  const result = spawnSync(command, args, { cwd: directory, encoding: "utf8" });
  const stdout = result.stdout.replace(
    /^(Parsing file )\S*\/tla2sany\/StandardModules\//gm,
    "$1/tmp/tlc-0/",
  );
  const stderr = result.stderr.replace(/^Picked up JAVA_TOOL_OPTIONS:.*\n/gm, "");
  return getTranscript(String(result.status), stdout, stderr);
};

const counts = { same: 0, declined: 0, differs: 0 };
for (const corpus of ["error_corpus", "corpus"]) {
  const source = join(SEMANTIC, corpus);
  const specs = readdirSync(source).filter((file) => file.endsWith(".tla"));
  for (const spec of specs.toSorted()) {
    const name = spec.slice(0, -".tla".length);
    const directory = mkdtempSync(join(tmpdir(), "sany-corpus-"));
    specs.forEach((file) => cpSync(join(source, file), join(directory, file)));
    writeFileSync(join(directory, `${name}.cfg`), "");
    const expected = run("java", ["-cp", classpath, "tlc2.TLC", ...ARGUMENTS, name], directory);
    const actual = run(native, [...ARGUMENTS, name], directory);
    rmSync(directory, { recursive: true, force: true });
    const outcome = actual.includes("prove-it: not native yet: ")
      ? "declined"
      : actual === expected
        ? "same"
        : "differs";
    counts[outcome] += 1;
    if (outcome !== "same") console.log(`${outcome} ${corpus}/${name}`);
  }
}
console.log(
  `${counts.same} print what TLC prints, ${counts.declined} decline, ${counts.differs} differ`,
);
process.exit(counts.differs === 0 ? 0 : 1);
