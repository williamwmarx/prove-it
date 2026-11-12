// The library's progress events for a native check, from the messages TLC prints, which the check
// records with its outcome. They arrive once the check ends, in TLC's order among what the spec
// printed.

import type { CheckStatus } from "./check";
import type { CheckProgress, Violation } from "./check-result";
import type { ModelConfig } from "./config";
import type { NativeCheckOutcome } from "./engine/native";
import { MESSAGE_CODE, MESSAGE_LEVEL } from "./tlc/messages";

// TLC's text of a count, with the thousands separated.
const toCount = (text: string) => Number(text.replaceAll(",", ""));

// The messages that report a violation -continue goes on past, by the status the check gives it.
const CONTINUED_STATUSES = new Map<number, CheckStatus>([
  [MESSAGE_CODE.invariantViolatedInitial, "invariant-violation"],
  [MESSAGE_CODE.invariantViolatedBehavior, "invariant-violation"],
  [MESSAGE_CODE.propertyViolatedInitial, "liveness-violation"],
  [MESSAGE_CODE.actionPropertyViolatedBehavior, "liveness-violation"],
]);

// The warnings the events name apart from a warning's code and text, and those of a violation's
// report, which the result holds.
const NAMED_WARNINGS = new Set<number>([
  MESSAGE_CODE.noSpecificationButProperty,
  MESSAGE_CODE.noFairnessButProperty,
  MESSAGE_CODE.constantLevelInvariant,
  MESSAGE_CODE.stateLevelProperty,
  MESSAGE_CODE.livenessSymmetry,
  MESSAGE_CODE.livenessConstraints,
  MESSAGE_CODE.javaOverrideMismatch,
]);

const PROGRESS =
  /^Progress\((\d+)\) at [^:]+:\d\d:\d\d: ([\d,]+) states generated(?: \([^)]*\))?, ([\d,]+) distinct states found(?: \([^)]*\))?, ([\d,]+) states left on queue\.$/;

const getStatistics = (text: string) => {
  const match = PROGRESS.exec(text);
  return match
    ? {
        generatedStates: toCount(match[2]),
        distinctStates: toCount(match[3]),
        queuedStates: toCount(match[4]),
        depth: toCount(match[1]),
      }
    : undefined;
};

// Each message's events, with how many of what the spec printed come before them.
export const getNativeProgress = (
  outcome: NativeCheckOutcome,
  violations: Violation[],
  config: ModelConfig,
  isContinued: boolean,
) => {
  const events: { progress: CheckProgress; printsBefore: number }[] = [];
  const add = (progress: CheckProgress, printsBefore: number) =>
    events.push({ progress, printsBefore });
  const continued = [...violations];
  const messages = outcome.messages;
  messages.forEach(([code, level, text, printsBefore, counts], index) => {
    const next = messages[index + 1];
    switch (code) {
      case MESSAGE_CODE.starting:
        return add({ kind: "parsed" }, printsBefore);
      case MESSAGE_CODE.constantLevelInvariant: {
        const name = /^The invariant (.+?) is a constant-level formula/.exec(text)?.[1];
        return name && add({ kind: "constant-level-invariant", name }, printsBefore);
      }
      case MESSAGE_CODE.stateLevelProperty: {
        const name = /^The formula (.+?) is a state-level formula/.exec(text)?.[1];
        return name && add({ kind: "state-level-property", name }, printsBefore);
      }
      case MESSAGE_CODE.javaOverrideLoaded:
      case MESSAGE_CODE.javaOverrideMismatch: {
        const match =
          /^(?:Loading|Failed to match) (.+?) operator override from .*?\/([^/]+)\.class with signature: <Java Method: (.*)>\.$/s.exec(
            text,
          );
        return (
          match &&
          add(
            {
              kind: "java-override",
              module: match[2],
              operator: match[1],
              signature: match[3],
              isMatched: code === MESSAGE_CODE.javaOverrideLoaded,
            },
            printsBefore,
          )
        );
      }
      case MESSAGE_CODE.temporalBranches: {
        const branches = /has (\d+) branch/.exec(text)?.[1];
        // TLC warns about the liveness checker before it builds it, and the symmetry it warns of
        // is the configuration's.
        add(
          {
            kind: "liveness-initializing",
            isSymmetric: config.symmetry !== undefined,
            isConstrained: config.constraints.length > 0 || config.actionConstraints.length > 0,
          },
          printsBefore,
        );
        return (
          branches && add({ kind: "liveness-prepared", branches: Number(branches) }, printsBefore)
        );
      }
      case MESSAGE_CODE.computingInit:
        return add({ kind: "initial-states-started" }, printsBefore);
      case MESSAGE_CODE.computingInitProgress: {
        const count = /^Computed ([\d,]+) initial states/.exec(text)?.[1];
        return (
          count && add({ kind: "initial-states-progress", count: toCount(count) }, printsBefore)
        );
      }
      case MESSAGE_CODE.initGenerated1:
      case MESSAGE_CODE.initGenerated2: {
        const match =
          /^Finished computing initial states: ([\d,]+) (?:distinct state|state)s? generated(?:, with ([\d,]+) of them distinct)? at /.exec(
            text,
          );
        if (!match) return;
        const generated = toCount(match[1]);
        const distinct = match[2] === undefined ? generated : toCount(match[2]);
        return add(
          { kind: "initial-states-computed", initialStates: { generated, distinct } },
          printsBefore,
        );
      }
      case MESSAGE_CODE.progress: {
        // TLC reports how far the search got before it checks the temporal properties, which the
        // event that starts that check carries.
        if (next?.[0] === MESSAGE_CODE.checkingTemporal) return;
        const statistics = getStatistics(text);
        return statistics && add({ kind: "progress", statistics }, printsBefore);
      }
      case MESSAGE_CODE.checkingTemporal: {
        const match =
          /^Checking (?:(\d+) branches of )?temporal properties for the (complete|current) state space with ([\d,]+) total distinct states/.exec(
            text,
          );
        const previous = messages[index - 1];
        const statistics = counts
          ? {
              generatedStates: counts[0],
              distinctStates: counts[1],
              queuedStates: counts[2],
              depth: counts[3],
            }
          : previous?.[0] === MESSAGE_CODE.progress
            ? getStatistics(previous[2])
            : undefined;
        return (
          match &&
          add(
            {
              kind: "liveness-started",
              branches: Number(match[1] ?? 1),
              isComplete: match[2] === "complete",
              states: toCount(match[3]),
              statistics: statistics ?? {
                generatedStates: outcome.generatedStates,
                distinctStates: outcome.distinctStates,
                queuedStates: outcome.queuedStates,
                depth: outcome.depth,
              },
            },
            printsBefore,
          )
        );
      }
      case MESSAGE_CODE.checkingTemporalEnd: {
        // TLC ends a check that found a counterexample after the counterexample, which the
        // result reports.
        const started = messages
          .slice(0, index)
          .findLastIndex((message) => message[0] === MESSAGE_CODE.checkingTemporal);
        const isViolated = messages
          .slice(started, index)
          .some((message) => message[0] === MESSAGE_CODE.temporalPropertyViolated);
        return isViolated || add({ kind: "liveness-finished" }, printsBefore);
      }
    }
    const status = CONTINUED_STATUSES.get(code);
    if (isContinued && status !== undefined) {
      const violation = continued.shift();
      return violation && add({ kind: "violation", status, violation }, printsBefore);
    }
    if (level === MESSAGE_LEVEL.warning && !NAMED_WARNINGS.has(code)) {
      add({ kind: "warning", code, text }, printsBefore);
    }
  });
  return events;
};
