// How each of tla-ts's backends decides the text tlapm would send its prover, by the prover of the
// method that selects it: with the backend's Rust port in the native engine.

import { getNativeAddon } from "../engine/native";
import { EngineUnavailableError, TlaProverError } from "../errors";
import type { DecideOptions, Decision } from "./verdict";

// The backends prove decides with, by the prover of the method that selects them.
const BACKENDS: readonly string[] = ["smt", "z3", "zenon", "isabelle", "ls4"];

export const isBackend = (prover: string) => BACKENDS.includes(prover);

// The decision, with the backend's statistics. A step limit, which only scripts set, stops the
// backend after that many steps. The native backend sees only the cancel cell, so an input whose
// signal has aborted already is unknown at once. Where no native engine loads, or the port declines,
// there is no decision, and it throws.
export const decide = (
  prover: string,
  text: string,
  options: DecideOptions,
  stepLimit?: number,
): Decision => {
  const start = performance.now();
  if (options.signal?.aborted === true)
    return { verdict: "unknown", timeUsedMs: performance.now() - start, statistics: {} };
  const addon = getNativeAddon();
  if (typeof addon === "string") throw new EngineUnavailableError(addon);
  const decision = addon.decide(prover, text, options.timeLimitMs, stepLimit, options.cancel);
  if (decision.kind === "error") throw new TlaProverError(decision.message);
  if (decision.kind === "declined")
    throw new TlaProverError(`${prover} declined: ${decision.reason}`);
  return {
    verdict: decision.verdict,
    timeUsedMs: performance.now() - start,
    statistics: decision.statistics,
  };
};
