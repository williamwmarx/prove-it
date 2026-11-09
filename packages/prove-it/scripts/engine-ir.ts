// Lowers every corpus model to the engine IR and holds the IR to M3's acceptance in native/DESIGN.md:
// each model has an IR or a reason it has none; each IR decodes and encodes again byte for byte in
// Rust; the golden models' IR matches tests/conformance/ir; and each IR's string table is TLC's
// string order, as createTlcOrder and getStringRank give it.
//
// Usage: bun scripts/run.ts engine-ir [--filter <text>] [--concurrency <n>] [--timeout-ms <ms>]
//        [--update]
// --update rewrites the golden files. --timeout-ms stops a model that hasn't reached the engine
// by then, and counts it as a failure; without it nothing does. Cargo must be on the PATH, for the Rust round trip.

import { spawn, spawnSync } from "node:child_process";
import { copyFileSync, existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";

import { parseConfig } from "../src/config";
import { createTlcOrder } from "../src/tlc/order";
import { getStringRank, setStringOrder } from "../src/values";
import type { ModelOutcome } from "./check-model";
import {
  CONFORMANCE_DIRECTORY,
  type CorpusModel,
  EXPECTED_PATH,
  findModels,
  getLibraryModules,
  getOption,
} from "./corpora";

// The models whose IR tests/conformance/ir keeps: the suite's corpus models, then models that
// reach what the suite doesn't: a specification in an instance's scope, TLC's actions for
// ENABLED, a VIEW, action constraints, properties checked as invariants, action properties and
// initial predicates, invariants that print, recursion, LAMBDA, function definitions, values
// TLC computes at startup, invariants an initial state violates, the run-time errors whose
// messages and call stacks tla-trace's evaluate_failure gives, tableau nodes that accept every
// behavior, assumptions that print, the records TLC sorts as it permutes a state under
// SYMMETRY, a lasso under a VIEW, action composition, an operator the configuration defines
// by its values, a postcondition that reads the _POSSIBLE counts, and one that reads a lasso
// stuttering at its initial state.
const GOLDEN_MODELS = [
  "examples/specifications/btree/MCbtree.cfg",
  "examples/specifications/TeachingConcurrency/SimpleRegular.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/pcal/SyncCons.cfg",
  "examples/specifications/transaction_commit/2PCwithBTM.cfg",
  "examples/specifications/byihive/VoucherRedeem.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/suite/test19.cfg",
  "examples/specifications/Bakery-Boulangerie/MCBakery.cfg",
  "examples/specifications/lamport_mutex/MCLamportMutex.cfg",
  "ccf/tla/consistency/MCSingleNode.cfg",
  "examples/specifications/Disruptor/MCDisruptor_MPMC.cfg",
  "summerset/tla+/paxos/Paxos_MC.cfg",
  "examples/specifications/ReadersWriters/MC.cfg",
  "examples/specifications/ewd426/TokenRing.cfg",
  "examples/specifications/acp/ACP_SB_TLC.cfg",
  "examples/specifications/Chameneos/Chameneos.cfg",
  "examples/specifications/transaction_commit/TCommit.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/suite/test61.cfg",
  "kafka/transactions/diary/01_InitPidRequest/tlaplus/kafka_transactions.cfg",
  "pingcap/Percolator/Test1.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/examples/SpecifyingSystems/TLC/ABCorrectness.cfg",
  "tla-rs/test_cases/should_pass/view_symmetry.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/Echo/MCEcho.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/TLCGetLevel.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/EWD840/MC02.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/suite/test216.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/examples/SpecifyingSystems/Liveness/LiveHourClock.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/Github1389ViolatedB.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/suite/test37.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/Github648.cfg",
  "spectacle/specs/with_state_graphs/simple_folds.cfg",
  "raft/specifications/standard-raft/RaftWithReconfigJointConsensus.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/Github746.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/suite/test57.cfg",
  "examples/specifications/acp/ACP_NB_WRONG_TLC.cfg",
  "examples/specifications/glowingRaccoon/stages.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/suite/etest9.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/suite/etest10.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/suite/etest11.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/suite/etest14.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/AssertExpressionStack.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/Github461.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/TESpecTest/TESpecRuntimeErrorTest.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/EvaluatingValueTest.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/DoInitFunctor/DoInitFunctorEvalException.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/DoInitFunctor/DoInitFunctorMinimalErrorStack.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/cdot/CdotWithContextB.cfg",
  "spectacle/specs/bfs_anim.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/suite/etest4.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/suite/etest6.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/pcal/Euclid.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/RandomElement.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/RandomElementXandY.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/RandomSubset.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/RandomSubsetNextTuples.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/coverage/I.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/IncompleteNextMultipleActions.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/Github179c.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/FingerprintExceptionInit.cfg",
  "spectacle/specs/with_state_graphs/Elevator.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/Github1389Counting.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/Github710b.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/Github710d.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/examples/FiniteMonotonic/MCDistributedReplicatedLog.cfg",
  "mongodb-txns/MultiShardTxn/Storage.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/examples/ewd998/AsyncTerminationDetection.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/cdot/CdotWithContextA.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/ConstantOperatorConfiguration.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/PossibleCountsTest.cfg",
  "etcd-raft/tla/etcdraft.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/examples/allocator/SchedulingAllocator.cfg",
  "raft/specifications/pull-raft/PullRaft.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/examples/SpecifyingSystems/Liveness/MCLiveWriteThroughCache.cfg",
];

const GOLDEN_DIRECTORY = join(CONFORMANCE_DIRECTORY, "ir");
const OUT_DIRECTORY = join(CONFORMANCE_DIRECTORY, ".ir");
const NATIVE_DIRECTORY = join(import.meta.dirname, "../native");
const timeoutOption = getOption("--timeout-ms");
const timeoutMilliseconds = timeoutOption === undefined ? undefined : Number(timeoutOption);
const TIMED_OUT = "timed out before the engine";

const filter = getOption("--filter");
const concurrency = Number(getOption("--concurrency") ?? 4);
const isUpdate = process.argv.includes("--update");

interface IrRun {
  id: string;
  // The IR's size, or why there is none.
  bytes?: number;
  reason?: string;
}

const getIrPath = (directory: string, id: string) => join(directory, id.replace(/\.cfg$/, ".ir"));

// Runs a model until the engine reports its IR, or says why it built none.
const lowerModel = (model: CorpusModel) =>
  new Promise<IrRun>((resolve) => {
    const path = getIrPath(OUT_DIRECTORY, model.id);
    mkdirSync(dirname(path), { recursive: true });
    const child = spawn(
      process.execPath,
      [
        "--stack-size=8000",
        "--max-old-space-size=6144",
        join(import.meta.dirname, "check-model.js"),
        model.specPath,
        model.configPath,
      ],
      {
        stdio: ["ignore", "pipe", "pipe"],
        env: { ...process.env, PROVE_IT_ENGINE: "debug", PROVE_IT_IR_DUMP: path },
      },
    );
    const run: { result?: IrRun } = {};
    const timer =
      timeoutMilliseconds === undefined
        ? undefined
        : setTimeout(() => {
            run.result ??= { id: model.id, reason: TIMED_OUT };
            child.kill("SIGKILL");
          }, timeoutMilliseconds);
    const stdout: Buffer[] = [];
    const stderr: string[] = [];
    child.stdout.on("data", (chunk: Buffer) => stdout.push(chunk));
    child.stderr.on("data", (chunk: Buffer) => {
      stderr.push(chunk.toString("utf8"));
      const lines = stderr.join("");
      const lowered = /^\[engine\] native: ir: (?:(\d+) bytes|declined: (.*)) in /m.exec(lines);
      const skipped = /^\[engine\] skipped: (.*)$/m.exec(lines);
      if (!lowered && !skipped) return;
      run.result ??= lowered?.[1]
        ? { id: model.id, bytes: Number(lowered[1]) }
        : { id: model.id, reason: `declined: ${lowered?.[2] ?? `skipped: ${skipped?.[1]}`}` };
      child.kill("SIGKILL");
    });
    child.on("close", () => {
      clearTimeout(timer);
      const output = Buffer.concat(stdout).toString("utf8");
      const outcome: ModelOutcome | undefined = output.startsWith("{")
        ? JSON.parse(output)
        : undefined;
      // A check that succeeds without reaching the engine has no Init or Next for it to search.
      const ending = !outcome
        ? "it crashed"
        : outcome.status === "success"
          ? "success, with no Init or Next"
          : `${outcome.status}${outcome.error ? `: ${outcome.error.split("\n")[0]}` : ""}`;
      resolve(
        run.result ?? { id: model.id, reason: `the check ended before the engine: ${ending}` },
      );
    });
  });

// The IR's texts, and how many TLC ranks.
const readTexts = (ir: Uint8Array) => {
  const words = new Int32Array(ir.buffer, ir.byteOffset, ir.byteLength >> 2);
  const text = new TextDecoder().decode(ir.subarray(words[2] * 4, words[2] * 4 + words[3]));
  const count = words[5];
  return {
    rankedCount: words[4],
    texts: Array.from({ length: count }, (_, index) =>
      text.slice(index === 0 ? 0 : words[5 + index], words[6 + index]),
    ),
  };
};

const libraryModules = getLibraryModules();

// Why the IR's string table isn't TLC's string order, if it isn't: it starts with the order
// createTlcOrder gives the model, and getStringRank ranks every text in it by its position.
const checkStringOrder = (model: CorpusModel, ir: Uint8Array) => {
  const loadModule = (name: string) => {
    const besideSpec = join(model.directory, `${name}.tla`);
    const libraryPath = libraryModules.get(name);
    return existsSync(besideSpec)
      ? readFileSync(besideSpec, "utf8")
      : libraryPath && readFileSync(libraryPath, "utf8");
  };
  const order = createTlcOrder(readFileSync(model.specPath, "utf8"), loadModule);
  const tlcOrder = [
    ...new Set(order.getStringOrder(parseConfig(readFileSync(model.configPath, "utf8")))),
  ];
  const table = readTexts(ir);
  const prefix = tlcOrder.findIndex((text, index) => table.texts[index] !== text);
  if (prefix !== -1) return `text ${prefix} is ${table.texts[prefix]}, not ${tlcOrder[prefix]}`;
  setStringOrder(tlcOrder);
  const misranked = table.texts
    .slice(0, table.rankedCount)
    .findIndex((text, index) => getStringRank(text) !== index);
  return misranked === -1 ? undefined : `getStringRank ranks text ${misranked} otherwise`;
};

const expectedIds = new Set(
  (JSON.parse(readFileSync(EXPECTED_PATH, "utf8")) as { id: string }[]).map((result) => result.id),
);
const models = findModels().filter(
  (model) => expectedIds.has(model.id) && (filter === undefined || model.id.includes(filter)),
);
rmSync(OUT_DIRECTORY, { recursive: true, force: true });
const runs: IrRun[] = [];
const queue = [...models];
await Promise.all(
  Array.from({ length: concurrency }, async () => {
    for (let model = queue.shift(); model; model = queue.shift()) {
      const run = await lowerModel(model);
      runs.push(run);
      console.log(
        `[${runs.length}/${models.length}] ${run.bytes === undefined ? `no IR: ${run.reason}` : `${run.bytes} bytes`}  ${model.id}`,
      );
    }
  }),
);

const failures: string[] = [];
// A model stopped before it reached the engine had its IR checked by nothing.
for (const run of runs) {
  if (run.reason === TIMED_OUT) failures.push(`${run.id}: ${TIMED_OUT}`);
}
const lowered = runs.filter((run) => run.bytes !== undefined);
for (const run of lowered) {
  const model = models.find((candidate) => candidate.id === run.id)!;
  const failure = checkStringOrder(model, readFileSync(getIrPath(OUT_DIRECTORY, run.id)));
  if (failure) failures.push(`${run.id}: the string table: ${failure}`);
}

const roundTrip = spawnSync(
  "cargo",
  ["run", "--release", "--locked", "-q", "-p", "tla-ir", "--bin", "ir-round-trip", OUT_DIRECTORY],
  { cwd: NATIVE_DIRECTORY, encoding: "utf8" },
);
if (roundTrip.status !== 0) failures.push(`the round trip: ${roundTrip.stderr.trim()}`);

const goldenIds = GOLDEN_MODELS.filter((id) => models.some((model) => model.id === id));
for (const id of goldenIds) {
  const path = getIrPath(OUT_DIRECTORY, id);
  const golden = getIrPath(GOLDEN_DIRECTORY, id);
  if (!existsSync(path)) {
    failures.push(`${id}: a golden model without an IR`);
  } else if (isUpdate) {
    mkdirSync(dirname(golden), { recursive: true });
    copyFileSync(path, golden);
  } else if (!existsSync(golden) || !readFileSync(path).equals(readFileSync(golden))) {
    failures.push(`${id}: the IR differs from ${golden}`);
  }
}

const reasons = new Map<string, number>();
for (const run of runs) {
  if (run.reason) reasons.set(run.reason, (reasons.get(run.reason) ?? 0) + 1);
}
writeFileSync(
  join(CONFORMANCE_DIRECTORY, ".ir-results.json"),
  `${JSON.stringify(
    runs.sort((left, right) => left.id.localeCompare(right.id)),
    null,
    2,
  )}\n`,
);
console.log(`\n${lowered.length} of ${runs.length} models have an IR.`);
for (const [reason, count] of [...reasons].sort((left, right) => right[1] - left[1])) {
  console.log(`${String(count).padStart(5)}  ${reason}`);
}
console.log(roundTrip.stdout.trim());
console.log(
  `${goldenIds.length} golden models ${isUpdate ? "written" : "compared"}; string tables checked on ${lowered.length}.`,
);
if (failures.length > 0) {
  console.log(`\n${failures.join("\n")}`);
  process.exit(1);
}
