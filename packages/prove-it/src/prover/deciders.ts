// How each of tla-ts's backends decides the text tlapm would send its prover, by the prover of the
// method that selects it: in TypeScript, or with the backend's Rust port in the native engine.

import { getNativeAddon } from "../engine/native";
import { getEnvironmentSetting, reportEngine } from "../engine/settings";
import { EngineUnavailableError, SmtParseError, TlaProverError } from "../errors";
import { decideIsabelle } from "./isabelle/decide";
import { decideSmt } from "./smt/solver/solver";
import { createSteps, type DecideOptions, type Decision, type Verdict } from "./verdict";

// Z3 rejects malformed input with an error, and tlapm counts that as a failure.
const decideZ3 = (text: string, options: DecideOptions) => {
  try {
    return decideSmt(text, options);
  } catch (error) {
    if (error instanceof SmtParseError) throw new TlaProverError(error.message, error);
    throw error;
  }
};

// The backends prove decides with, by the prover of the method that selects them.
export const BACKENDS: readonly string[] = ["smt", "z3", "zenon", "isabelle", "ls4"];

// The backends whose TypeScript decider is still kept. The others are decided by their Rust port
// alone.
export const DECIDERS: Partial<Record<string, (text: string, options: DecideOptions) => Verdict>> =
  {
    smt: decideZ3,
    z3: decideZ3,
    isabelle: decideIsabelle,
  };

export const isBackend = (prover: string) => BACKENDS.includes(prover);

export const hasTypeScriptDecider = (prover: string) => DECIDERS[prover] !== undefined;

// The backends whose Rust port decides by default, each once it decides every recorded input as
// the TypeScript backend does (design/prover.md, section 4).
const RUST_BACKENDS = new Set<string>(["ls4", "zenon", "isabelle"]);

// Which port decides a backend's inputs: the Rust port alone for a backend without a TypeScript
// decider, else PROVE_IT_PROVER_<PROVER>, such as PROVE_IT_PROVER_SMT, for one backend, else
// PROVE_IT_PROVER for all, each "ts" or "rust", else the default.
const isRust = (prover: string) => {
  if (!hasTypeScriptDecider(prover)) return true;
  const setting =
    getEnvironmentSetting(`PROVE_IT_PROVER_${prover.toUpperCase()}`) ??
    getEnvironmentSetting("PROVE_IT_PROVER");
  return setting === undefined ? RUST_BACKENDS.has(prover) : setting === "rust";
};

// The Rust port's decision, or why it gives none: no native engine loads, or the port declines.
const decideNatively = (
  prover: string,
  text: string,
  options: DecideOptions,
  stepLimit: number | undefined,
) => {
  const addon = getNativeAddon();
  if (typeof addon === "string") return { kind: "unavailable" as const, reason: addon };
  const decision = addon.decide(prover, text, options.timeLimitMs, stepLimit, options.cancel);
  if (decision.kind === "error") throw new TlaProverError(decision.message);
  return decision;
};

// The decision, with the backend's statistics. A step limit, which only scripts set, stops the
// backend after that many steps. A native backend sees only the cancel cell, so an input whose
// signal has aborted already goes to TypeScript, which answers unknown, or is unknown at once for a
// backend without a TypeScript decider. Where no native engine loads, or the port declines, the
// TypeScript backend decides; a backend without one throws.
export const decide = (
  prover: string,
  text: string,
  options: DecideOptions,
  stepLimit?: number,
): Decision => {
  const start = performance.now();
  const isAborted = options.signal?.aborted === true;
  const native =
    isRust(prover) && !isAborted ? decideNatively(prover, text, options, stepLimit) : undefined;
  if (native?.kind === "decided")
    return {
      verdict: native.verdict,
      timeUsedMs: performance.now() - start,
      statistics: native.statistics,
    };
  const typescript = DECIDERS[prover];
  if (native !== undefined) {
    if (typescript === undefined && native.kind === "unavailable")
      throw new EngineUnavailableError(native.reason);
    const reason =
      native.kind === "unavailable"
        ? `no native engine for ${prover}: ${native.reason}`
        : `${prover} declined: ${native.reason}`;
    if (typescript === undefined) throw new TlaProverError(reason);
    reportEngine(`prover: ${reason}`);
  }
  if (typescript === undefined)
    return { verdict: "unknown", timeUsedMs: performance.now() - start, statistics: {} };
  const statistics = {};
  const verdict = typescript(text, { ...options, steps: createSteps(stepLimit), statistics });
  return { verdict, timeUsedMs: performance.now() - start, statistics };
};
