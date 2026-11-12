// Proves a module's obligations with Prove It's own backends, in tlapm's order, or with tlapm.

import {
  getNativeAddon,
  loadWasmEngine,
  type NativeAddon,
  type NativeProve,
} from "../engine/native";
import {
  EngineInvariantError,
  EngineUnavailableError,
  TlapmBugError,
  TlaProofError,
  TlaProverError,
  TlaSyntaxError,
  TlaUnsupportedError,
} from "../errors";
import { isWorkerSupported } from "../worker";
import { createDecidePool, type DecidePool } from "./decide-pool";
import { decide } from "./deciders";
import type { TlapmResult } from "./tlapm/tlapm";
import type { Decision } from "./verdict";

interface ObligationBase {
  id: number;
  location: string;
  text: string;
}

export interface ProvedObligation extends ObligationBase {
  status: "proved";
  prover: string;
}

export interface TrivialObligation extends ObligationBase {
  status: "trivial";
}

export interface UnprovedObligation extends ObligationBase {
  status: "failed" | "unsupported";
  reason: string;
}

export type ProofObligation = ProvedObligation | TrivialObligation | UnprovedObligation;

export type ProofStatus = ProofObligation["status"];

export interface ProveResult {
  obligations: ProofObligation[];
  missingProofCount: number;
  omittedProofCount: number;
}

export interface ProveOptions {
  source: string;
  loadModule?: (name: string) => string | undefined;
  backend?: "tla-ts" | "tlapm";
  signal?: AbortSignal;
  onObligation?: (obligation: ProofObligation) => void;
  workers?: number;
}

const getModuleName = (source: string) => /-{4,}\s*MODULE\s+(\w+)/.exec(source)?.[1] ?? "Main";

const BUG_MESSAGE = new TlapmBugError().message;

// The error the Rust driver reports, as the TypeScript would throw it.
const getDriverError = (result: Extract<NativeProve, { kind: "error" }>) => {
  if (result.name === "TlaProofError")
    return result.message === BUG_MESSAGE
      ? new TlapmBugError(result.exception)
      : new TlaProofError(
          result.message,
          result.failure === undefined
            ? { exception: result.exception }
            : { failure: result.failure },
        );
  if (result.name === "TlaSyntaxError") return new TlaSyntaxError(result.message);
  if (result.name === "TlaUnsupportedError") return new TlaUnsupportedError(result.message);
  return new TlaProverError(result.message);
};

// A decision as the Rust driver reads it: the verdict and the time it took, or the message of the
// TlaProverError the backend threw. Its strings hold only well-formed UTF-16.
const getAnswer = (decision: Promise<Decision>) =>
  decision.then(
    (answer) => {
      if (
        !["unsat", "sat", "unknown"].includes(answer.verdict) ||
        typeof answer.timeUsedMs !== "number"
      )
        throw new EngineInvariantError(`a backend answered ${JSON.stringify(answer)}`);
      return `${answer.verdict} ${answer.timeUsedMs}`;
    },
    (error: unknown) => {
      if (!(error instanceof TlaProverError || error instanceof TlaUnsupportedError)) throw error;
      if (!error.message.isWellFormed())
        throw new EngineInvariantError("a backend's message isn't well-formed UTF-16");
      return `${error instanceof TlaProverError ? "error" : "unsupported"}:${error.message}`;
    },
  );

// prove with the Rust driver, which proves in rounds: each asks for the modules and the decisions
// it needs, which this answers through the engine's decide, in the pool when there is one, and the
// next starts again from the beginning with them (design/prover.md, section 4c).
// The engine declines a source or module with a lone surrogate, which its strings can't hold.
const proveNatively = async (
  options: ProveOptions,
  name: string,
  native: NativeAddon,
): Promise<ProveResult> => {
  const workerCount = options.workers ?? 1;
  const pool =
    workerCount > 1 && isWorkerSupported() ? await createDecidePool(workerCount) : undefined;
  const decideText: DecidePool["decide"] =
    pool?.decide ?? (async (prover, text, decideOptions) => decide(prover, text, decideOptions));
  const onAbort = () => pool?.terminate(options.signal?.reason);
  options.signal?.addEventListener("abort", onAbort);
  const known = new Map<string, string | undefined>();
  // The decisions that threw what ends the run, by key.
  const failures = new Map<string, unknown>();
  // The decisions being made, by key.
  const inFlight = new Map<string, Promise<unknown>>();
  let reportedCount = 0;
  // As the TypeScript driver does, each report waits for an abort to land first.
  const report = async (reports: ProofObligation[]) => {
    for (const obligation of reports.slice(reportedCount)) {
      options.signal?.throwIfAborted();
      reportedCount++;
      options.onObligation?.(obligation);
      // HACK: the driver runs synchronously, so yield to let an abort land, as the TypeScript does.
      await new Promise((resolve) => setTimeout(resolve));
    }
  };
  try {
    for (;;) {
      const result = native.prove(`${name}.tla`, options.source, [...known]);
      if (result.kind === "error") {
        // An obligation's error waits for an abort, as the TypeScript driver checks the signal at
        // each obligation; getObligations's has no reports.
        if (result.reports !== undefined) {
          await report(result.reports);
          options.signal?.throwIfAborted();
        }
        throw getDriverError(result);
      }
      await report(result.reports);
      if (result.kind === "proved")
        return {
          obligations: result.reports,
          missingProofCount: result.missingProofCount,
          omittedProofCount: result.omittedProofCount,
        };
      // Only the first module it needs, as the TypeScript reads the next one only once it has
      // read this one, and stops at one that doesn't parse.
      const [key] = result.keys;
      if (key !== undefined) {
        const moduleName = key.slice("module:".length, key.lastIndexOf("#"));
        known.set(key, options.loadModule?.(moduleName));
        continue;
      }
      // A decision that threw ends the run once no earlier obligation needs a decision, as the
      // TypeScript driver decides each obligation's in turn.
      const failed = result.requests
        .filter((request) => failures.has(request.key))
        .toSorted((left, right) => left.priority - right.priority)[0];
      const requests = result.requests.filter(
        (request) => failed === undefined || request.priority < failed.priority,
      );
      if (failed !== undefined && requests.length === 0) {
        options.signal?.throwIfAborted();
        throw failures.get(failed.key);
      }
      if (requests.length > 0) options.signal?.throwIfAborted();
      for (const request of requests) {
        if (inFlight.has(request.key)) continue;
        // A decide that throws at once is read as one that rejects, as the TypeScript awaits it.
        const decided = getAnswer(
          Promise.resolve().then(() =>
            decideText(
              request.prover,
              request.text,
              { timeLimitMs: request.timeLimitMs, signal: options.signal },
              request.priority,
            ),
          ),
        ).then(
          (answer) => known.set(`decide:${request.key}`, answer),
          (error: unknown) => failures.set(request.key, error),
        );
        inFlight.set(
          request.key,
          decided.then(() => inFlight.delete(request.key)),
        );
      }
      // The next round starts once a decision settles, with every other that settled with it, so
      // that obligations are reported as they settle and their next methods start, as with the
      // TypeScript driver.
      if (inFlight.size > 0) await Promise.race(inFlight.values());
      await new Promise((resolve) => setTimeout(resolve));
    }
  } finally {
    options.signal?.removeEventListener("abort", onAbort);
    pool?.terminate(new TlaProverError("prove stopped"));
  }
};

// The obligations of the module, as the Rust driver reads them, each with the last result tlapm
// reported for it.
const proveWithTlapm = async (
  options: ProveOptions,
  name: string,
  native: NativeAddon,
): Promise<ProveResult> => {
  if (typeof process === "undefined" || process.versions?.node === undefined)
    throw new TlaUnsupportedError("The tlapm backend runs only in Node and Bun.");
  const modules = new Map<string, string>();
  const known = new Map<string, string | undefined>();
  for (;;) {
    const result = native.obligations(`${name}.tla`, options.source, [...known], []);
    if (result.kind === "error") throw getDriverError(result);
    if (result.kind === "needed") {
      // A module's n-th read, `module:<name>#<n>`, and the file it came from, `path:<name>#<n>`,
      // which is `<name>.tla` as loadModule names none.
      for (const key of result.keys) {
        if (!key.startsWith("module:")) {
          known.set(key, undefined);
          continue;
        }
        const moduleName = key.slice("module:".length, key.lastIndexOf("#"));
        const source = options.loadModule?.(moduleName);
        if (source !== undefined) modules.set(moduleName, source);
        known.set(key, source);
      }
      continue;
    }
    const getObligation = (
      obligation: (typeof result.obligations)[number],
      tlapmResult: TlapmResult | undefined,
    ): ProofObligation => ({
      id: obligation.id,
      location: obligation.location,
      text: obligation.text,
      ...(tlapmResult ?? { status: "unsupported", reason: "tlapm reported no result" }),
    });
    const byId = new Map(result.obligations.map((obligation) => [obligation.id, obligation]));
    const tlapm = await import("./tlapm/tlapm");
    const reported = await tlapm.proveWithTlapm(
      name,
      new Map([[name, options.source], ...modules]),
      {
        signal: options.signal,
        onResult: (id, tlapmResult) => {
          const obligation = byId.get(id);
          if (obligation) options.onObligation?.(getObligation(obligation, tlapmResult));
        },
      },
    );
    return {
      obligations: result.obligations.map((obligation) =>
        getObligation(obligation, reported.get(obligation.id)),
      ),
      missingProofCount: result.missingProofCount,
      omittedProofCount: result.omittedProofCount,
    };
  }
};

export const prove = async (options: ProveOptions): Promise<ProveResult> => {
  const name = getModuleName(options.source);
  await loadWasmEngine();
  const native = getNativeAddon();
  if (typeof native === "string") throw new EngineUnavailableError(native);
  return options.backend === "tlapm"
    ? proveWithTlapm(options, name, native)
    : proveNatively(options, name, native);
};
