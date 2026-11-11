// How each of tla-ts's backends decides the text tlapm would send its prover, by the prover of the
// method that selects it: in TypeScript, or with the backend's Rust port in the native engine.

import { getNativeAddon } from "../engine/native";
import { getEnvironmentSetting, reportEngine } from "../engine/settings";
import { SmtParseError, TlaProverError } from "../errors";
import { decideIsabelle } from "./isabelle/decide";
import { decidePtl } from "./ptl/decide";
import { decideSmt } from "./smt/solver/solver";
import { createSteps, type DecideOptions, type Decision, type Verdict } from "./verdict";
import { decideZenon } from "./zenon/decide";

// Z3 rejects malformed input with an error, and tlapm counts that as a failure.
const decideZ3 = (text: string, options: DecideOptions) => {
  try {
    return decideSmt(text, options);
  } catch (error) {
    if (error instanceof SmtParseError) throw new TlaProverError(error.message, error);
    throw error;
  }
};

export const DECIDERS: Record<string, (text: string, options: DecideOptions) => Verdict> = {
  smt: decideZ3,
  z3: decideZ3,
  zenon: (text, options) => decideZenon(text, options).verdict,
  isabelle: decideIsabelle,
  ls4: decidePtl,
};

// The backends whose Rust port decides by default, each once it decides every recorded input as
// the TypeScript backend does (design/prover.md, section 4).
const RUST_BACKENDS = new Set<string>(["ls4", "zenon"]);

// Which port decides a backend's inputs: PROVE_IT_PROVER_<PROVER>, such as PROVE_IT_PROVER_ZENON,
// for one backend, else PROVE_IT_PROVER for all, each "ts" or "rust", else the default.
const isRust = (prover: string) => {
  const setting =
    getEnvironmentSetting(`PROVE_IT_PROVER_${prover.toUpperCase()}`) ??
    getEnvironmentSetting("PROVE_IT_PROVER");
  return setting === undefined ? RUST_BACKENDS.has(prover) : setting === "rust";
};

// The Rust port's decision, or undefined where no native engine loads or the port declines, so
// that the TypeScript backend decides.
const decideNatively = (
  prover: string,
  text: string,
  options: DecideOptions,
  stepLimit: number | undefined,
) => {
  const addon = getNativeAddon();
  if (typeof addon === "string") {
    reportEngine(`prover: no native engine for ${prover}: ${addon}`);
    return undefined;
  }
  const decision = addon.decide(prover, text, options.timeLimitMs, stepLimit, options.cancel);
  if (decision.kind === "error") throw new TlaProverError(decision.message);
  if (decision.kind === "decided") return decision;
  reportEngine(`prover: ${prover} declined: ${decision.reason}`);
  return undefined;
};

// The decision, with the backend's statistics. A step limit, which only scripts set, stops the
// backend after that many steps. A native backend sees only the cancel cell, so an input whose
// signal has aborted already goes to TypeScript, which answers unknown.
export const decide = (
  prover: string,
  text: string,
  options: DecideOptions,
  stepLimit?: number,
): Decision => {
  const start = performance.now();
  const native =
    isRust(prover) && options.signal?.aborted !== true
      ? decideNatively(prover, text, options, stepLimit)
      : undefined;
  const statistics = native?.statistics ?? {};
  const verdict =
    native?.verdict ??
    DECIDERS[prover](text, { ...options, steps: createSteps(stepLimit), statistics });
  return { verdict, timeUsedMs: performance.now() - start, statistics };
};
