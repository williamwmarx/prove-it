// Writes every text tla-ts's prove sends a backend on the recorded modules to .prover-inputs, one
// file per distinct input of each prover, named by its digest, for prover-differential.ts to decide
// again, and .prover-inputs/time-limits.json, the time limits in seconds, null for none, that
// prove sent each input with, for z3-parity.ts to run Z3 under.
//
// Which backends prove tries on an obligation depends on what the earlier ones answered, so the
// texts come from proving each module. By default the answers come from prover-inputs.json, which
// makes the run quick and the inputs the same on every machine. With --record, each backend decides
// each input anew, and prover-inputs.json is rewritten: first with tlapm's time limit, to find the
// steps the backend takes within it on this machine, then again with those steps as its step limit
// and no time limit. The second answer and its statistics are what is recorded, and what any port of
// the backend must reproduce from the same step limit, on any machine. A recording keeps each
// module's answers in .prover-inputs/recording.jsonl as it finishes it, and a recording that
// finds the file goes on from it, so a recording stopped part way loses only the modules it was
// in. Run it, replaying or recording, under Node with a larger heap than the default, as the
// solver's heap fills on a few modules, and the run fails when it loses a module:
//   NODE_OPTIONS=--max-old-space-size=4500 bun scripts/run.ts prover-inputs [--record] [--jobs n]

import { existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { join } from "node:path";

import { TlaError, TlaProverError } from "../src/errors";
import { BACKENDS, decide, hasTypeScriptDecider } from "../src/prover/deciders";
import { proveObligations } from "../src/prover/prove";
import type { Decision } from "../src/prover/verdict";
import { CORPORA_DIRECTORY, getOption } from "./corpora";
import { appendJournal, readJournal, repairJournal } from "./journal";
import { runModuleWorkers } from "./module-workers";
import {
  getModuleObligations,
  getObligationCount,
  type ModuleProofRecord,
  readProofRecords,
} from "./proof-records";
import {
  getInputKey,
  getInputPath,
  getMergedTimeLimits,
  type InputRecord,
  PROVER_INPUTS_DIRECTORY,
  PROVER_INPUTS_PATH,
  readInputRecords,
  TIME_LIMITS_PATH,
  useTypeScriptBackends,
  writeInputRecords,
} from "./prover-records";
import { getDigest } from "./tlapm-digest";

useTypeScriptBackends();

const isRecording = process.argv.includes("--record");

// What is recorded already. A recording of some modules, with --filter, keeps the others' inputs.
const records: Record<string, InputRecord> =
  isRecording && (getOption("--filter") === undefined || !existsSync(PROVER_INPUTS_PATH))
    ? {}
    : readInputRecords();

// The recorded answer, as prove's decide gives it: a decision, or the TlaProverError the backend
// threw.
const replay = (record: InputRecord): Decision => {
  if (record.error !== undefined) throw new TlaProverError(record.error);
  return { verdict: record.verdict, timeUsedMs: 0, statistics: record.statistics };
};

const record = (prover: string, text: string, timeLimitMs: number): InputRecord => {
  const getRecord = (): InputRecord => {
    const steps = Number(decide(prover, text, { timeLimitMs }).statistics.steps);
    const decision = decide(prover, text, { timeLimitMs: Infinity }, steps);
    return { prover, stepLimit: steps, verdict: decision.verdict, statistics: decision.statistics };
  };
  try {
    return getRecord();
  } catch (error) {
    if (!(error instanceof TlaProverError)) throw error;
    return { prover, verdict: "unknown", statistics: {}, error: error.message };
  }
};

// A backend without a TypeScript decider, as Zenon, SMT and Z3 are, is recorded from its Rust port.
if (isRecording)
  BACKENDS.filter((backend) => !hasTypeScriptDecider(backend)).forEach((backend) =>
    console.log(`${backend} has no TypeScript decider: its Rust port's answers are recorded`),
  );

const RECORDING_PATH = join(PROVER_INPUTS_DIRECTORY, "recording.jsonl");

interface ModuleInputs {
  inputs: Record<string, InputRecord>;
  timeLimits: Record<string, (number | null)[]>;
}

interface RecordedModule extends ModuleInputs {
  id: string;
}

// The modules this recording has finished. The parent cuts what a stop left unfinished, before
// any worker appends.
const readRecording = () =>
  new Map(readJournal<RecordedModule>(RECORDING_PATH).map((recorded) => [recorded.id, recorded]));

if (isRecording && !process.argv.includes("--worker")) repairJournal(RECORDING_PATH);

// The inputs of a module's proofs, and the time limits each was sent with, by key.
const writeModuleInputs = async (module: ModuleProofRecord): Promise<ModuleInputs> => {
  const finished = isRecording ? readRecording().get(module.id) : undefined;
  if (finished !== undefined) return finished;
  const inputs: Record<string, InputRecord> = {};
  const timeLimits: Record<string, (number | null)[]> = {};
  const obligations = (() => {
    try {
      return getModuleObligations(join(CORPORA_DIRECTORY, module.id));
    } catch (error) {
      if (!(error instanceof TlaError)) throw error;
      return [];
    }
  })();
  await proveObligations(obligations, {
    decide: async (prover, text, options) => {
      const key = getInputKey(prover, getDigest(text));
      const path = getInputPath(key);
      mkdirSync(join(path, ".."), { recursive: true });
      writeFileSync(path, text);
      const seconds = Number.isFinite(options.timeLimitMs) ? options.timeLimitMs / 1000 : null;
      timeLimits[key] = [...new Set([...(timeLimits[key] ?? []), seconds])];
      const recorded = inputs[key] ?? (isRecording ? undefined : records[key]);
      if (!isRecording && recorded === undefined)
        throw new Error(`${module.id}: input ${key} isn't in prover-inputs.json`);
      inputs[key] = recorded ?? record(prover, text, options.timeLimitMs);
      return replay(inputs[key]);
    },
  });
  if (isRecording) {
    mkdirSync(PROVER_INPUTS_DIRECTORY, { recursive: true });
    appendJournal(RECORDING_PATH, { id: module.id, inputs, timeLimits });
  }
  return { inputs, timeLimits };
};

const modules = readProofRecords();
const byModule = await runModuleWorkers(modules, getObligationCount, writeModuleInputs, 1);
const inputs: Record<string, InputRecord> = Object.assign(
  {},
  ...[...byModule.values()].map((module) => module.inputs),
);
const timeLimits: Record<string, (number | null)[]> = {};
for (const module of byModule.values())
  for (const [key, limits] of Object.entries(module.timeLimits))
    timeLimits[key] = [...new Set([...(timeLimits[key] ?? []), ...limits])];
mkdirSync(PROVER_INPUTS_DIRECTORY, { recursive: true });
// A run over some modules (--filter, --skip) keeps the time limits of the inputs it didn't write.
const earlierTimeLimits = existsSync(TIME_LIMITS_PATH)
  ? JSON.parse(readFileSync(TIME_LIMITS_PATH, "utf8"))
  : {};
writeFileSync(
  TIME_LIMITS_PATH,
  `${JSON.stringify(getMergedTimeLimits(earlierTimeLimits, timeLimits))}\n`,
);
if (isRecording && byModule.size === modules.length) {
  writeInputRecords({ ...records, ...inputs });
  rmSync(RECORDING_PATH);
}
const count = Object.keys(inputs).length;
console.log(
  `${count} inputs from ${byModule.size} of ${modules.length} modules in ${PROVER_INPUTS_DIRECTORY}`,
);
// A module lost with its worker leaves its inputs unwritten, so the differential can't read them.
if (byModule.size < modules.length) {
  console.error(`${modules.length - byModule.size} modules lost with their workers`);
  process.exitCode = 1;
}
