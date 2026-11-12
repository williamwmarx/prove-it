// A port of aidenybai/tla-ts packages/conformance (scripts/test-file.ts, hosts.ts, transcript.ts,
// conformance.ts) that treats the upstream checkout as data. Usage:
//   bun harness.ts <suite-dir> <out.jsonl> <time-limit-seconds> <workers> <command...> [-- filters...]
// One JSON line per run: id, verdict, exit, expectedExit, transcript, stderr, exceeded.
import { spawn } from "node:child_process";
import {
  appendFileSync,
  cpSync,
  existsSync,
  mkdirSync,
  mkdtempSync,
  readdirSync,
  readFileSync,
  realpathSync,
  rmSync,
  statSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { basename, dirname, extname, join, relative } from "node:path";
import { load } from "js-yaml";

const [suiteDirectory, outPath, timeLimit, workersText, ...rest] = process.argv.slice(2);
const separator = rest.indexOf("--");
const command = separator === -1 ? rest : rest.slice(0, separator);
const filters = separator === -1 ? [] : rest.slice(separator + 1);
const workers = Number(workersText);
const limitMs = Number(timeLimit) * 1000;
const onlyIds = process.env.ONLY_IDS
  ? new Set(readFileSync(process.env.ONLY_IDS, "utf8").split("\n").filter(Boolean))
  : undefined;

// ---- test-file.ts
interface Recording { exit: number; transcript?: string }
interface Meta {
  outcome: string; flags?: string[]; contexts?: string[]; config?: string; args?: string[];
  includes?: string[]; stack?: string; correct?: Record<string, Recording>;
}
interface SuiteTest {
  id: string; suite: string; path: string; fileName: string; moduleName: string; metadata: Meta;
  source: string; recordings: Record<string, Recording> | undefined;
}
const HEADER = /^\(\*---\n([\s\S]*?)\n---\*\)\n/;
const RECORDING = /\n\(\*--- recorded\n([\s\S]*?)\n---\*\)\n$/;
const MODULE_END = /^={4,}[ \t]*$/m;
const STATE = "conformance_state";
const stateContext = (name: string, init: string, next: string, check: string) => ({
  name,
  appended: `VARIABLE ${STATE}\nInit == ${STATE} = ${init}\nNext == ${next}\nInv == ${check}`,
  config: "INIT Init\nNEXT Next\nINVARIANT Inv\n",
});
const EXPRESSION_CONTEXTS = [
  { name: "assume", appended: "ASSUME Test", config: "" },
  stateContext("init", "Test", `UNCHANGED ${STATE}`, STATE),
  stateContext("next", "TRUE", `${STATE}' = Test`, STATE),
  stateContext("invariant", "TRUE", `UNCHANGED ${STATE}`, `${STATE} /\\ Test`),
  {
    name: "property",
    appended: `VARIABLE ${STATE}\nSpec == ${STATE} = TRUE /\\ [][UNCHANGED ${STATE}]_${STATE}\nProp == [](${STATE} /\\ Test)`,
    config: "SPECIFICATION Spec\nPROPERTY Prop\n",
  },
];
const appendToModule = (source: string, text: string) => {
  const end = [...source.matchAll(new RegExp(MODULE_END, "gm"))].at(-1)?.index;
  if (end === undefined) throw new Error("The test has no module end line");
  return `${source.slice(0, end)}${text}\n${source.slice(end)}`;
};
const parseTest = (path: string, text: string): SuiteTest | undefined => {
  const header = HEADER.exec(text);
  if (!header) return undefined;
  const recording = RECORDING.exec(text);
  const id = relative(suiteDirectory, path).replace(/\.tla$/, "");
  return {
    id, suite: id.split("/")[0], path, fileName: basename(path),
    moduleName: basename(path, extname(path)), metadata: load(header[1]) as Meta,
    source: `${(recording ? text.slice(0, recording.index) : text).trimEnd()}\n`,
    recordings: recording ? (load(recording[1]) as Record<string, Recording>) : undefined,
  };
};
const listFiles = (directory: string): string[] =>
  readdirSync(directory).sort().flatMap((entry) => {
    const path = join(directory, entry);
    return statSync(path).isDirectory() ? listFiles(path) : [path];
  });
const getContexts = (test: SuiteTest) =>
  test.suite === "tlc" && test.metadata.flags?.includes("expression")
    ? EXPRESSION_CONTEXTS.filter((c) => !test.metadata.contexts || test.metadata.contexts.includes(c.name))
        .map((c) => ({ name: c.name, source: appendToModule(test.source, c.appended), config: `${c.config}${test.metadata.config ?? ""}` }))
    : [{ name: "model", source: test.source, config: test.metadata.config ?? "" }];
const getRecording = (test: SuiteTest, context: string) =>
  test.recordings?.[context] ?? test.recordings?.["all"];
const getCorrection = (test: SuiteTest, context: string) =>
  test.metadata.correct?.[context] ?? test.metadata.correct?.["all"];

// ---- transcript.ts
const MARKER = /@!@!@(?:STARTMSG (\d+):(\d+)|ENDMSG \d+) @!@!@/g;
const VOLATILE_CODES = new Set([2185, 2186, 2187, 2188, 2189, 2200, 2219, 2220, 2262, 2271, 2401]);
const VOLATILE_LINE = /^(Parsing file |Semantic processing of module |Linting of module )/;
const STACK_FRAME = /^\s+at [\w.$<>]+\(.*\)$/;
const TIMESTAMP = /\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}/g;
const BUILD_VERSION = /\bVersion \d{4}\.\d{2}\.\d{2}\.\d{6}\b/g;
const DURATION = /\b(in) (\d+h )?(\d+min )?\d+(s|ms)\b/g;
const OBJECT_IDENTITY = /\b([\w.$]+)@[0-9a-f]{5,8}\b/g;
const GENERATED_NAME = /\b(__DebuggerExpr__|__DebuggerModule__|_PossibleModule_|neg_prop_)\d+/g;
const INSTALL_FIELD = /install \|->\s+"[^"]*"/g;
const STATE_SPACE_CODES = new Set([2190, 2192, 2193, 2194, 2199, 2267, 2268]);
const cleanLine = (line: string, directories: string[]) =>
  directories.reduce((text, d) => text.replaceAll(`${d}/`, ""), line)
    .replace(TIMESTAMP, "<date>").replace(BUILD_VERSION, "Version <build>")
    .replace(DURATION, "$1 <time>").replace(GENERATED_NAME, "$1<id>").replace(OBJECT_IDENTITY, "$1@<id>");
const splitAtMarkers = (line: string) =>
  [...line.matchAll(MARKER)].reduce<{ parts: (string | RegExpExecArray)[]; offset: number }>(
    (state, match) => ({ parts: [...state.parts, line.slice(state.offset, match.index), match], offset: match.index + match[0].length }),
    { parts: [], offset: 0 });
export const normalizeTranscript = (output: string, directory: string, isStateSpaceRelevant: boolean) => {
  const directories = [directory, directory.replace(/^\/private/, "")];
  const kept: (string | undefined)[] = [];
  const open: { code: number; severity: number; lines: string[]; slot: number }[] = [];
  const addText = (text: string) => {
    const message = open.at(-1);
    if (message) { message.lines.push(text); return; }
    if (text.trim() !== "" && !VOLATILE_LINE.test(text) && !STACK_FRAME.test(text)) kept.push(`| ${cleanLine(text, directories)}`);
  };
  const closeMessage = () => {
    const message = open.pop();
    if (!message) return;
    const isDropped = VOLATILE_CODES.has(message.code) || (!isStateSpaceRelevant && STATE_SPACE_CODES.has(message.code));
    const body = message.lines.filter((inner) => !STACK_FRAME.test(inner)).map((inner) => cleanLine(inner, directories))
      .join("\n").replace(INSTALL_FIELD, 'install |-> "<install>"').trimEnd();
    kept[message.slot] = isDropped ? undefined : `${message.code}:${message.severity} ${body}`;
  };
  output.split("\n").forEach((line) => {
    const split = splitAtMarkers(line);
    split.parts.forEach((part) => {
      if (typeof part === "string") { if (part !== "") addText(part); return; }
      if (part[1] === undefined) { closeMessage(); return; }
      open.push({ code: Number(part[1]), severity: Number(part[2]), lines: [], slot: kept.length });
      kept.push(undefined);
    });
    const rest = line.slice(split.offset);
    if (split.parts.length === 0 || rest !== "") addText(rest);
  });
  return kept.filter((e) => e !== undefined).join("\n");
};
const getMessageCodes = (t: string) => [...t.matchAll(/^(\d+):\d+ /gm)].map((m) => m[1]).join(" ");

// ---- hosts.ts
const DETERMINISTIC_ARGUMENTS = ["-workers", "1", "-fp", "0", "-seed", "4", "-lncheck", "final", "-noGenerateSpecTE"];
const killGroup = (groupId: number | undefined) => {
  if (groupId === undefined) return;
  try { process.kill(-groupId, "SIGKILL"); } catch (error) {
    const code = (error as NodeJS.ErrnoException).code;
    if (code !== "ESRCH" && code !== "EPERM") throw error;
  }
};
const spawnRun = (argv: string[], cwd: string) =>
  new Promise<{ exit: number; stdout: string; stderr: string; exceeded?: "time" }>((resolve) => {
    const child = spawn(argv[0], argv.slice(1), { cwd, stdio: ["ignore", "pipe", "pipe"], detached: true });
    const groupId = child.pid;
    let exceeded: "time" | undefined;
    const timer = limitMs ? setTimeout(() => { exceeded ??= "time"; killGroup(groupId); }, limitMs) : undefined;
    const stdout: Buffer[] = [];
    const stderr: Buffer[] = [];
    child.stdout.on("data", (c: Buffer) => stdout.push(c));
    child.stderr.on("data", (c: Buffer) => stderr.push(c));
    child.on("exit", () => killGroup(groupId));
    child.on("close", (exitCode, signal) => {
      clearTimeout(timer);
      resolve({ exit: exitCode ?? (signal ? -1 : 0), stdout: Buffer.concat(stdout).toString("utf8"), stderr: Buffer.concat(stderr).toString("utf8"), ...(exceeded ? { exceeded } : {}) });
    });
  });
const runOne = async (test: SuiteTest, context: { name: string; source: string; config: string }) => {
  const directory = realpathSync(mkdtempSync(join(tmpdir(), "conformance-")));
  (test.metadata.includes ?? []).forEach((include) => {
    const target = join(directory, include);
    mkdirSync(dirname(target), { recursive: true });
    cpSync(join(dirname(test.path), include), target, { recursive: true });
  });
  const isExitOnly = test.metadata.flags?.includes("exit-only") ?? false;
  const configFile = `${test.moduleName}.cfg`;
  writeFileSync(join(directory, test.fileName), context.source);
  writeFileSync(join(directory, configFile), context.config);
  const argv = [
    ...command.map((a) => (a === "-Xss2m" && test.metadata.stack ? `-Xss${test.metadata.stack}` : a)),
    ...(isExitOnly ? [] : ["-tool"]), ...DETERMINISTIC_ARGUMENTS, "-metadir", join(directory, ".meta"),
    ...(test.metadata.args ?? []), ...(test.metadata.args?.includes("-config") ? [] : ["-config", configFile]), test.fileName,
  ];
  const started = Date.now();
  const result = await spawnRun(argv, directory);
  const millis = Date.now() - started;
  rmSync(directory, { recursive: true, force: true });
  return {
    exit: result.exit, exceeded: result.exceeded, millis,
    transcript: isExitOnly ? "" : normalizeTranscript(result.stdout, directory, context.name === "model"),
    stderr: result.stderr.split(directory + "/").join(""),
  };
};

// ---- conformance.ts
const verdictOf = (expected: Recording | undefined, actual: { exit: number; transcript: string; exceeded?: string }) => {
  if (!expected) return "unrecorded";
  if (actual.exceeded) return `${actual.exceeded}-limit`;
  if (actual.exit === -1) return "crash";
  if (actual.exit !== expected.exit) return "exit-mismatch";
  const e = expected.transcript ?? "";
  if (getMessageCodes(actual.transcript) !== getMessageCodes(e)) return "message-mismatch";
  return actual.transcript === e ? "pass" : "text-mismatch";
};
const isTlcHost = command.some((a) => a === "tlc2.TLC");

const tests = listFiles(suiteDirectory)
  .filter((p) => filters.length === 0 || filters.some((f) => p.includes(f)))
  .flatMap((p) => parseTest(p, readFileSync(p, "utf8")) ?? [])
  .filter((t) => t.suite === "tlc");
const jobs = tests.flatMap((test) => getContexts(test).map((context) => ({ test, context, id: context.name === "model" ? test.id : `${test.id}#${context.name}` })))
  .filter((j) => !onlyIds || onlyIds.has(j.id));
if (process.env.COUNT_ONLY) { console.log(`${tests.length} tests, ${jobs.length} runs`); process.exit(0); }

const done = new Set<string>();
if (existsSync(outPath)) readFileSync(outPath, "utf8").split("\n").filter(Boolean).forEach((l) => done.add(JSON.parse(l).id));
const todo = jobs.filter((j) => !done.has(j.id));
console.log(`${jobs.length} runs, ${done.size} already done, ${todo.length} to go`);
let next = 0;
let finished = 0;
await Promise.all(Array.from({ length: workers }, async () => {
  while (next < todo.length) {
    const job = todo[next++];
    const actual = await runOne(job.test, job.context);
    const expected = (isTlcHost ? undefined : getCorrection(job.test, job.context.name)) ?? getRecording(job.test, job.context.name);
    appendFileSync(outPath, `${JSON.stringify({ id: job.id, verdict: verdictOf(expected, actual), expectedExit: expected?.exit, ...actual })}\n`);
    if (++finished % 1000 === 0) console.log(`${finished}/${todo.length} ${new Date().toISOString()}`);
  }
}));
console.log("done");
