// Ported from Z3 (src/util/rlimit.h, src/util/rlimit.cpp, src/util/memory_manager.cpp), MIT
// license, see z3-license.txt. The resource limit of an ast_manager, shared by every context and
// rewriter that uses the manager. It cancels the work at the deadline, in milliseconds since the
// epoch, when the signal aborts, or when the heap is nearly full.
import type { GCProfiler } from "node:v8";

import { SmtCanceledError } from "../../../errors";
import { createSteps, isStepLimitReached, type Steps } from "../../verdict";

export class ResourceLimit {
  // Why the work was canceled, once it is.
  stopReason: "steps" | "time" | "signal" | "heap" | undefined = undefined;
  // Watches for a full collection while the used size is past the threshold.
  private profiler: GCProfiler | null = null;

  // steps.count is m_count, the steps taken, which MBQI also uses as a random seed, and
  // steps.limit is m_limit, Z3's own rlimit, checked on every step.
  constructor(
    private deadline: number,
    private signal?: AbortSignal,
    private steps: Steps = createSteps(),
  ) {}

  get count() {
    return this.steps.count;
  }

  // inc: counts a step and returns whether the work may go on. The clock and the heap are read on
  // every 256th step, since a step costs less than reading them. A step can allocate kilobytes, so
  // reading the heap less often lets it fill between two readings.
  inc() {
    const isOverStepLimit = isStepLimitReached(this.steps);
    if (this.stopReason !== undefined) return false;
    const stopReason = isOverStepLimit
      ? "steps"
      : (this.steps.count & CLOCK_CHECK_MASK) !== 0
        ? undefined
        : Date.now() > this.deadline
          ? "time"
          : this.signal?.aborted === true
            ? "signal"
            : this.isHeapNearlyFull()
              ? "heap"
              : undefined;
    if (stopReason === undefined) return true;
    this.stopReason = stopReason;
    this.release();
    return false;
  }

  // tactic::checkpoint: counts a step, and throws once the work is canceled.
  checkpoint() {
    if (!this.inc()) throw new SmtCanceledError();
  }

  // The used size counts garbage, such as what earlier work left, until the collector runs. So once
  // it passes the threshold, the size after the next full collection decides.
  private isHeapNearlyFull() {
    if (v8 === undefined) return false;
    const statistics = v8.getHeapStatistics();
    const threshold = HEAP_FRACTION * (statistics.used_heap_size + statistics.total_available_size);
    if (statistics.used_heap_size <= threshold) {
      this.release();
      return false;
    }
    if (this.profiler === null) {
      this.profiler = new v8.GCProfiler();
      this.profiler.start();
      return false;
    }
    const collection = this.profiler
      .stop()
      .statistics.findLast((event) => event.gcType === "MarkSweepCompact");
    this.profiler.start();
    if (collection === undefined) return false;
    this.release();
    return collection.afterGC.heapStatistics.usedHeapSize > threshold;
  }

  // Stops watching the collector, which the work does when it ends.
  release() {
    this.profiler?.stop();
    this.profiler = null;
  }
}

// Z3 runs as its own process, where running out of memory ends only that process and tlapm counts
// the obligation as failed. The solver shares its caller's process instead, which running out of
// heap would end, so it stops before the heap fills, like Z3's max_memory in memory::allocate. The
// heap statistics come from node:v8. In V8, which Node and Deno use, the used and the available
// size add up to the heap limit. Bun reports the memory of the machine and no full collections,
// and its getHeapStatistics walks every live object, which made a proof 100 times slower, so the
// check is off there.
const HEAP_FRACTION = 0.8;
const CLOCK_CHECK_MASK = 255;
const v8 =
  typeof process === "undefined" || process.versions.bun !== undefined
    ? undefined
    : process.getBuiltinModule?.("node:v8");
