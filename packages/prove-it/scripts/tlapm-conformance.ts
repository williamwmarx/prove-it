// Runs `prove-it tlapm` on every module of tlapm.json as record-tlapm.ts ran tlapm on it, and
// compares what it prints with what tlapm printed: each obligation's location and text byte for
// byte, or the error tlapm ended with. The native binary runs it, or with --cli the CLI of dist/,
// through the engine as an addon or as WebAssembly. tlapm finds its standard library beside its
// binary on the PATH, so the script installs the corpus's tlapm library as one.
// Usage: bun scripts/run.ts tlapm-conformance [--filter <text>] [--cli] [--verbose]

import { spawn } from "node:child_process";
import {
  existsSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  symlinkSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { basename, delimiter, dirname, join } from "node:path";

import {
  CONFORMANCE_DIRECTORY,
  CORPORA_DIRECTORY,
  getOption,
  LIBRARY_PATH,
  linkLibraryModules,
  writeResults,
} from "./corpora";
import { collapseWhitespace, getDigest, TLAPM_PATH, type TlapmDigest } from "./tlapm-digest";

type Verdict = "match" | "mismatch" | "declined";

const RESULTS_PATH = join(CONFORMANCE_DIRECTORY, ".tlapm-results.json");

const CONCURRENCY = 4;

const PACKAGE_DIRECTORY = join(import.meta.dirname, "..");

const BINARY = join(PACKAGE_DIRECTORY, "native/target/release/prove-it");

const NOT_NATIVE = "prove-it: not native yet: ";

const isCli = process.argv.includes("--cli");

// bin/tlapm, with lib/tlapm/stdlib beside it.
const installTlapm = () => {
  const root = mkdtempSync(join(tmpdir(), "prove-it-tlapm-install-"));
  mkdirSync(join(root, "bin"));
  writeFileSync(join(root, "bin/tlapm"), "");
  mkdirSync(join(root, "lib/tlapm"), { recursive: true });
  symlinkSync(join(CORPORA_DIRECTORY, "tlapm/library"), join(root, "lib/tlapm/stdlib"));
  return root;
};

const getCommand = () =>
  isCli
    ? [process.execPath, join(PACKAGE_DIRECTORY, "dist/cli.js")]
    : [process.env.PROVE_IT_BINARY ?? BINARY];

const runTlapm = (path: string) =>
  new Promise<string>((resolve) => {
    const cacheDirectory = mkdtempSync(join(tmpdir(), "prove-it-tlapm-"));
    const [command, ...prefix] = getCommand();
    const child = spawn(
      command,
      [
        ...prefix,
        "tlapm",
        "-N",
        "--printallobs",
        "--toolbox",
        "0",
        "0",
        "--cache-dir",
        cacheDirectory,
        "-I",
        LIBRARY_PATH,
        basename(path),
      ],
      {
        cwd: dirname(path),
        env: { ...process.env, PATH: `${join(install, "bin")}${delimiter}${process.env.PATH}` },
      },
    );
    const chunks: Buffer[] = [];
    child.stdout.on("data", (chunk: Buffer) => chunks.push(chunk));
    child.stderr.on("data", (chunk: Buffer) => chunks.push(chunk));
    child.on("close", () => {
      rmSync(cacheDirectory, { recursive: true, force: true });
      resolve(Buffer.concat(chunks).toString("utf8"));
    });
  });

// What record-tlapm.ts reads of tlapm's output.
const parseMessages = (output: string) =>
  output
    .split("@!!BEGIN\n")
    .slice(1)
    .map((block) => {
      const fields = new Map<string, string>();
      block
        .slice(0, block.indexOf("@!!END"))
        .split("\n@!!")
        .map((field, index) => (index === 0 ? field.replace(/^@!!/, "") : field))
        .forEach((field) => {
          const separator = field.indexOf(":");
          fields.set(field.slice(0, separator), field.slice(separator + 1));
        });
      return fields;
    });

const getError = (output: string, messages: Map<string, string>[]) =>
  [
    ...messages
      .filter((fields) => ["warning", "error"].includes(fields.get("type") ?? ""))
      .map((fields) => (fields.get("msg") ?? "").trim()),
    output
      .split("\n")
      .find((line) => line.includes("tlapm ending abnormally"))
      ?.trim() ?? "",
  ]
    .filter((line) => line !== "")
    .join("\n")
    .replaceAll(`${CORPORA_DIRECTORY}/`, "")
    .replaceAll(`${LIBRARY_PATH}/`, "");

const getActual = (id: string, output: string): TlapmDigest | { declined: string } => {
  const declined = output.split("\n").find((line) => line.startsWith(NOT_NATIVE));
  if (declined !== undefined) return { declined: declined.slice(NOT_NATIVE.length) };
  const messages = parseMessages(output);
  if (output.includes("tlapm ending abnormally"))
    return { id, status: "error", error: getError(output, messages) };
  const obligations = messages
    .filter(
      (fields) => fields.get("type") === "obligation" && fields.get("status") === "to be proved",
    )
    .map((fields) => {
      const text = (fields.get("obl") ?? "").trimEnd();
      return {
        loc: fields.get("loc") ?? "",
        text: getDigest(collapseWhitespace(text)),
        layout: getDigest(text),
      };
    });
  return { id, status: "ok", ...(obligations.length > 0 ? { obligations } : {}) };
};

const filter = getOption("--filter");
const isVerbose = process.argv.includes("--verbose");
if (!isCli && process.env.PROVE_IT_BINARY === undefined && !existsSync(BINARY)) {
  console.error(`Build the binary first: cargo build --release -p prove-it-cli (${BINARY})`);
  process.exit(1);
}
linkLibraryModules();
const install = installTlapm();
const expected: TlapmDigest[] = JSON.parse(readFileSync(TLAPM_PATH, "utf8"));
const queue = expected.filter((result) => filter === undefined || result.id.includes(filter));
const results: {
  id: string;
  verdict: Verdict;
  reason?: string;
  tlapm?: TlapmDigest;
  proveIt?: TlapmDigest;
}[] = [];
await Promise.all(
  Array.from({ length: CONCURRENCY }, async () => {
    for (let result = queue.shift(); result; result = queue.shift()) {
      const actual = getActual(result.id, await runTlapm(join(CORPORA_DIRECTORY, result.id)));
      if ("declined" in actual) {
        results.push({ id: result.id, verdict: "declined", reason: actual.declined });
        console.log(`declined ${result.id}: ${actual.declined}`);
        continue;
      }
      const isMatch = JSON.stringify(actual) === JSON.stringify(result);
      results.push(
        isMatch
          ? { id: result.id, verdict: "match" }
          : { id: result.id, verdict: "mismatch", tlapm: result, proveIt: actual },
      );
      if (isMatch) continue;
      console.log(`mismatch ${result.id}`);
      if (isVerbose) {
        console.log(`  tlapm:     ${JSON.stringify(result).slice(0, 400)}`);
        console.log(`  prove-it:  ${JSON.stringify(actual).slice(0, 400)}`);
      }
    }
  }),
);
rmSync(install, { recursive: true, force: true });
results.sort((left, right) => (left.id < right.id ? -1 : 1));
writeResults(RESULTS_PATH, results);
console.log("");
Map.groupBy(results, (result) => result.verdict).forEach((group, verdict) =>
  console.log(`${verdict}: ${group.length}`),
);
console.log(`modules: ${results.length} (${basename(RESULTS_PATH)} has the details)`);
if (results.some((result) => result.verdict === "mismatch")) process.exitCode = 1;
