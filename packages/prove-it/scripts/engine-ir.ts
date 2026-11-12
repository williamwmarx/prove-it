// Lowers every corpus model to the engine IR through the Rust front end, as the binary does, and
// holds the IR to M3's acceptance in native/DESIGN.md: each model has an IR or the front end's
// reason it has none; each IR decodes and encodes again byte for byte in Rust; the golden models'
// IR matches tests/conformance/ir; and each IR's string table is TLC's string order. front-dump's
// model-full lowers the models in batches, as tla_front::model::lower_model does for prove-it, and
// its order mode gives TLC's string order of each.
//
// Usage: bun scripts/run.ts engine-ir [--filter <text>] [--concurrency <n>] [--update]
// --update rewrites the golden files. --concurrency is how many front-dump batches run at once.
// Cargo must be on the PATH: it builds front-dump and runs the Rust round trip.

import { spawn, spawnSync } from "node:child_process";
import { copyFileSync, existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";

import {
  CONFORMANCE_DIRECTORY,
  type CorpusModel,
  EXPECTED_PATH,
  findModels,
  getOption,
  LIBRARY_PATH,
  linkLibraryModules,
} from "./corpora";

// The models whose IR tests/conformance/ir keeps: the suite's corpus models, then models that
// reach what the suite doesn't: a specification in an instance's scope, TLC's actions for
// ENABLED, a VIEW, action constraints, properties checked as invariants, action properties and
// initial predicates, invariants that print, recursion, LAMBDA, function definitions, values
// TLC computes at startup, invariants an initial state violates, the run-time errors whose
// messages and call stacks tla-trace's evaluate_failure gives, an expansion TLC replays after an
// invariant fails to evaluate, tableau nodes that accept every behavior, assumptions that print,
// the records TLC sorts as it permutes a state under SYMMETRY, a lasso under a VIEW, action
// composition, an operator the configuration defines by its values, a postcondition that reads
// the _POSSIBLE counts, and one that reads a lasso stuttering at its initial state.
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
  "tlc/tlatools/org.lamport.tlatools/test-model/FingerprintExceptionHang.cfg",
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
  "tlc/tlatools/org.lamport.tlatools/test-model/Github607.cfg",
  "tla-rs/test_cases/should_error/liveness_error.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/examples/FiniteMonotonic/MCDistributedReplicatedLog.cfg",
  "mongodb-txns/MultiShardTxn/Storage.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/examples/ewd998/AsyncTerminationDetection.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/cdot/CdotWithContextA.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/ConstantOperatorConfiguration.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/PossibleCountsTest.cfg",
  "etcd-raft/tla/etcdraft.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/examples/allocator/SchedulingAllocator.cfg",
  "raft/specifications/pull-raft/PullRaft.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/EmptySubsetEq.cfg",
  "tlc/tlatools/org.lamport.tlatools/test-model/examples/SpecifyingSystems/Liveness/MCLiveWriteThroughCache.cfg",
];

const GOLDEN_DIRECTORY = join(CONFORMANCE_DIRECTORY, "ir");
const OUT_DIRECTORY = join(CONFORMANCE_DIRECTORY, ".ir");
const NATIVE_DIRECTORY = join(import.meta.dirname, "../native");
// Batches keep each front-dump's output, the IR in hex, well under a string's largest size.
const BATCH = 25;

const filter = getOption("--filter");
const concurrency = Number(getOption("--concurrency") ?? 4);
const isUpdate = process.argv.includes("--update");

interface IrRun {
  id: string;
  // The IR's size, or why there is none.
  bytes?: number;
  reason?: string;
}

// What front-dump writes for a model it couldn't lower or order.
interface FrontFailure {
  error?: string;
  notYet?: string;
}

const getIrPath = (directory: string, id: string) => join(directory, id.replace(/\.cfg$/, ".ir"));

const build = spawnSync(
  "cargo",
  ["build", "--release", "--locked", "--quiet", "-p", "tla-front", "--bin", "front-dump"],
  { cwd: NATIVE_DIRECTORY, stdio: "inherit" },
);
if (build.status !== 0) process.exit(build.status ?? 1);
const FRONT_DUMP = join(NATIVE_DIRECTORY, "target/release/front-dump");
linkLibraryModules();

// front-dump's line for each model, in the mode given.
const runFrontDump = (mode: "model-full" | "order", batch: CorpusModel[]) =>
  new Promise<string[]>((resolve, reject) => {
    const child = spawn(FRONT_DUMP, [mode, "--library", LIBRARY_PATH], {
      stdio: ["pipe", "pipe", "pipe"],
    });
    const stdout: Buffer[] = [];
    const stderr: Buffer[] = [];
    child.stdout.on("data", (chunk: Buffer) => stdout.push(chunk));
    child.stderr.on("data", (chunk: Buffer) => stderr.push(chunk));
    child.on("error", reject);
    child.on("close", (status) => {
      const lines = Buffer.concat(stdout).toString("utf8").split("\n").slice(0, batch.length);
      if (status === 0 && lines.length === batch.length) return resolve(lines);
      reject(
        new Error(
          `front-dump ${mode} failed on ${batch[0].id} and the ${batch.length - 1} models after it: ${Buffer.concat(stderr).toString("utf8")}`,
        ),
      );
    });
    child.stdin.end(batch.map((model) => `${model.configPath}\t${model.specPath}\n`).join(""));
  });

const describeFailure = (failure: FrontFailure) =>
  failure.notYet === undefined
    ? (failure.error ?? JSON.stringify(failure))
    : `not native yet: ${failure.notYet}`;

// Writes each model's IR to OUT_DIRECTORY, or says why the front end built none.
const lowerBatch = async (batch: CorpusModel[]) =>
  (await runFrontDump("model-full", batch)).map((line, index): IrRun => {
    const { id } = batch[index];
    const written = JSON.parse(line) as { ir?: string } & FrontFailure;
    if (written.ir === undefined) return { id, reason: describeFailure(written) };
    const ir = Buffer.from(written.ir, "hex");
    const path = getIrPath(OUT_DIRECTORY, id);
    mkdirSync(dirname(path), { recursive: true });
    writeFileSync(path, ir);
    return { id, bytes: ir.length };
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

// Why the IR's string table isn't TLC's string order, if it isn't: it starts with the order
// front-dump gives the model, and the texts it ranks are that order's, each at its rank.
const checkStringOrder = (line: string, ir: Uint8Array) => {
  const written = JSON.parse(line) as { strings?: string[] } & FrontFailure;
  if (written.strings === undefined) return `no string order: ${describeFailure(written)}`;
  const tlcOrder = [...new Set(written.strings)];
  const table = readTexts(ir);
  const prefix = tlcOrder.findIndex((text, index) => table.texts[index] !== text);
  if (prefix !== -1) return `text ${prefix} is ${table.texts[prefix]}, not ${tlcOrder[prefix]}`;
  const ranks = new Map(tlcOrder.map((text, rank) => [text, rank]));
  const misranked = table.texts
    .slice(0, table.rankedCount)
    .findIndex((text, index) => ranks.get(text) !== index);
  return misranked === -1 ? undefined : `TLC's order ranks text ${misranked} otherwise`;
};

const expectedIds = new Set(
  (JSON.parse(readFileSync(EXPECTED_PATH, "utf8")) as { id: string }[]).map((result) => result.id),
);
const models = findModels().filter(
  (model) => expectedIds.has(model.id) && (filter === undefined || model.id.includes(filter)),
);
rmSync(OUT_DIRECTORY, { recursive: true, force: true });
const batches = Array.from({ length: Math.ceil(models.length / BATCH) }, (_, index) =>
  models.slice(index * BATCH, (index + 1) * BATCH),
);
const runs: IrRun[] = [];
const failures: string[] = [];
const queue = [...batches];
await Promise.all(
  Array.from({ length: concurrency }, async () => {
    for (let batch = queue.shift(); batch; batch = queue.shift()) {
      const batchRuns = await lowerBatch(batch);
      for (const run of batchRuns) {
        runs.push(run);
        console.log(
          `[${runs.length}/${models.length}] ${run.bytes === undefined ? `no IR: ${run.reason}` : `${run.bytes} bytes`}  ${run.id}`,
        );
      }
      const batchLowered = batch.filter((_, index) => batchRuns[index].bytes !== undefined);
      if (batchLowered.length === 0) continue;
      const orders = await runFrontDump("order", batchLowered);
      batchLowered.forEach((model, index) => {
        const failure = checkStringOrder(
          orders[index],
          readFileSync(getIrPath(OUT_DIRECTORY, model.id)),
        );
        if (failure) failures.push(`${model.id}: the string table: ${failure}`);
      });
    }
  }),
);
const lowered = runs.filter((run) => run.bytes !== undefined);

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
  console.log(`${String(count).padStart(5)}  ${reason.replace(/\s*\n\s*/g, " ")}`);
}
console.log(roundTrip.stdout.trim());
console.log(
  `${goldenIds.length} golden models ${isUpdate ? "written" : "compared"}; string tables checked on ${lowered.length}.`,
);
if (failures.length > 0) {
  console.log(`\n${failures.join("\n")}`);
  process.exit(1);
}
