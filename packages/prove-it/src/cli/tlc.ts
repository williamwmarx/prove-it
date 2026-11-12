import {
  appendFileSync,
  existsSync,
  mkdirSync,
  readFileSync,
  readSync,
  writeFileSync,
  writeSync,
} from "node:fs";
import { arch, availableParallelism, EOL, release, type } from "node:os";
import { basename, delimiter, dirname, resolve, sep } from "node:path";
import { pathToFileURL } from "node:url";
import { getHeapStatistics } from "node:v8";

import { version } from "../../package.json";
import type { Expression } from "../ast";
import type {
  CheckProgress,
  CheckResult,
  CheckStatus,
  InitialStates,
  OutputLine,
  SearchStatistics,
  TraceStep,
  Violation,
} from "../check";
import { parseConfig } from "../config";
import { checkAllSources, getNativeAddon, loadWasmEngine, resolveAllFiles } from "../engine/native";
import { isTypeScriptCheckAsked, reportEngine } from "../engine/settings";
import {
  EngineUnavailableError,
  getErrorExitCode,
  getUnexpectedException,
  TlaConfigError,
  TlaError,
  TlaSanyFatalError,
  TlaSyntaxError,
  TlaUnsupportedError,
} from "../errors";
import { describeRange } from "../evaluate";
import { EXIT_STATUS } from "../exit-codes";
import { checkParsed } from "../parallel";
import { SANY_174_STANDARD_MODULES } from "../sany/modules";
import { getSanyReport, type SanyModuleOrigin } from "../sany/report";
import { readSanySnapshot } from "../sany/snapshot";
import type { StateDump } from "../state-graph";
import {
  getFailureHeadline,
  getInitialViolationHeadline,
  getMessageHeadline,
  getViolationHeadline,
  isInitialViolation,
} from "../tlc/headlines";
import {
  createMessagePrinter,
  formatNestedMessage,
  formatTlcDate,
  formatTlcDuration,
  MESSAGE_CODE,
  MESSAGE_LEVEL,
  type MessagePrinter,
} from "../tlc/messages";
import {
  formatProbability,
  getActualProbability,
  getOptimisticProbability,
  getOutDegreeSummary,
} from "../tlc/summary";
import type { TlcVersion } from "../tlc/version";
import { formatState } from "../values";
import { CHECK_COMMAND, type ParsedArgs, USAGE } from "./options";
import { getNativeSanyReport } from "./sany-text";
import {
  getInputPaths,
  getMachine,
  type JavaProperties,
  NOT_NATIVE_EXIT_CODE,
  printError,
  readFileKey,
  reportErrors,
} from "./shared";

// Writes to stdout or stderr at once. The first write through process.stdout sets up a stream,
// which costs Bun several milliseconds of a run; a pipe that is full or non-blocking takes the
// rest of the text when it can.
const writeOutput = (fd: number, text: string) => {
  const bytes = Buffer.from(text);
  let offset = 0;
  while (offset < bytes.length) {
    try {
      offset += writeSync(fd, bytes, offset);
    } catch (error) {
      if ((error as { code?: string }).code !== "EAGAIN") throw error;
    }
  }
};
const EXIT_CODES: Record<CheckStatus, number> = {
  success: EXIT_STATUS.success,
  "assumption-violation": EXIT_STATUS.assumptionViolation,
  deadlock: EXIT_STATUS.deadlock,
  "invariant-violation": EXIT_STATUS.safetyViolation,
  "property-violation": EXIT_STATUS.safetyViolation,
  "liveness-violation": EXIT_STATUS.livenessViolation,
  "postcondition-violation": EXIT_STATUS.assumptionViolation,
  error: EXIT_STATUS.error,
};

const isJavaLong = (text: string) =>
  /^[+-]?\d+$/.test(text) && BigInt.asIntN(64, BigInt(text)) === BigInt(text);

const getWorkerCount = (values: string[] | undefined) => {
  if (!values) return 1;
  return values[0] === "auto"
    ? availableParallelism()
    : Math.max(1, Number.parseInt(values[0], 10) || 1);
};

const UNSUPPORTED_DUMP_FORMATS = ["constrained", "stuttering", "strict"];

// TLC names the file of a -dump by its format unless the name already ends that way.
const getDumpPath = (path: string, extension: string) =>
  path.endsWith(extension) ? path : `${path}${extension}`;

const getStateDump = (values: string[]): StateDump => {
  if (values.length === 1) return { path: getDumpPath(values[0], ".dump") };
  const format = values[0].toLowerCase();
  return {
    path: getDumpPath(values[1], ".dot"),
    dot: true,
    colorize: format.includes("colorize"),
    actionLabels: format.includes("actionlabels"),
    snapshot: format.includes("snapshot"),
  };
};

const printInitialStatesProgress = (printer: MessagePrinter, count: number) =>
  printer.print(
    MESSAGE_CODE.computingInitProgress,
    MESSAGE_LEVEL.none,
    `Computed ${count} initial states...`,
  );

// What the spec prints as TLC rebuilds a trace, before it prints the states or after.
const printTraceOutput = (printer: MessagePrinter, lines: OutputLine[] | undefined) =>
  lines?.forEach((line) => {
    if (typeof line === "string") return console.log(line);
    if (line.kind === "initial-states-progress") {
      return printInitialStatesProgress(printer, line.count);
    }
    const headline = getInitialViolationHeadline(line.status, line.name);
    printer.print(
      headline.code,
      MESSAGE_LEVEL.error,
      `${headline.text}\n${formatState(line.state)}`,
    );
  });

const printTrace = (
  printer: MessagePrinter,
  trace: TraceStep[],
  heading: { code: number; text: string } = {
    code: MESSAGE_CODE.behaviorUpToThisPoint,
    text: "The behavior up to this point is:",
  },
  isRebuiltAfterHeading = false,
) => {
  if (trace.length > 0) printer.print(heading.code, MESSAGE_LEVEL.error, heading.text);
  trace.forEach((step, index) => {
    if (index > 0 || isRebuiltAfterHeading) printTraceOutput(printer, step.output);
    printer.print(
      MESSAGE_CODE.statePrint2,
      MESSAGE_LEVEL.state,
      `${index + 1}: <${step.label ?? step.action ?? "Initial predicate"}>\n${formatState(step.state)}`,
    );
  });
};

const COUNTER_EXAMPLE = {
  code: MESSAGE_CODE.counterExample,
  text: "The following behavior constitutes a counter-example:\n",
};

// TLC's FingerprintException#getTrace: the range of each source, innermost first, skipping a
// source the same as the one inside it.
const formatFingerprintTrace = (sources: Expression[]) =>
  sources
    .filter((source, index) => source !== sources[index - 1])
    .map((source, index) => `${index}) ${describeRange(source)}\n`)
    .toReversed()
    .join("");

// TLC's CallStack.toString: the range of each expression, skipping an expression that it evaluates
// again right inside itself.
const formatCallStack = (expressions: Expression[]) => {
  if (expressions.length === 0) return "    The error call stack is empty.\n";
  const lines: string[] = [];
  expressions.forEach((expression, index) => {
    const range = expression.location.range;
    if (expression === expressions[index - 1] || !range) return;
    lines.push(
      `${lines.length}. Line ${range.start.line}, column ${range.start.column} to line ${range.end.line}, column ${range.end.column} in ${range.module}\n`,
    );
  });
  return `${lines.join("")}\n`;
};

const printInitialStates = (printer: MessagePrinter, initialStates: InitialStates) => {
  const generated = initialStates.generated;
  const distinct = initialStates.distinct;
  const date = formatTlcDate(new Date());
  if (generated === distinct) {
    printer.print(
      MESSAGE_CODE.initGenerated1,
      MESSAGE_LEVEL.none,
      `Finished computing initial states: ${distinct} distinct state${distinct === 1 ? "" : "s"} generated at ${date}.`,
    );
    return;
  }
  printer.print(
    MESSAGE_CODE.initGenerated2,
    MESSAGE_LEVEL.none,
    `Finished computing initial states: ${generated} state${generated === 1 ? "" : "s"} generated, with ${distinct} of them distinct at ${date}.`,
  );
};

interface Timing {
  startTime: number;
  // Whether TLC has printed that SANY finished.
  isParsed: boolean;
  livenessStartTime: number | undefined;
}

// TLC reports a depth of at least 1, even before it finds a state, and rates a minute only once the
// search has started.
const printProgress = (
  printer: MessagePrinter,
  statistics: SearchStatistics,
  startTime?: number,
) => {
  const minutes = Math.max(Date.now() - (startTime ?? 0), 1) / 60_000;
  const formatCount = (count: number) => count.toLocaleString("en-US");
  const getRate = (count: number, unit: string) =>
    startTime === undefined ? "" : ` (${formatCount(Math.floor(count / minutes))} ${unit}/min)`;
  printer.print(
    MESSAGE_CODE.progress,
    MESSAGE_LEVEL.none,
    `Progress(${Math.max(statistics.depth, 1)}) at ${formatTlcDate(new Date())}: ${formatCount(statistics.generatedStates)} states generated${getRate(statistics.generatedStates, "s")}, ${formatCount(statistics.distinctStates)} distinct states found${getRate(statistics.distinctStates, "ds")}, ${formatCount(statistics.queuedStates)} states left on queue.`,
  );
};

const printCheckProgress = (
  printer: MessagePrinter,
  progress: CheckProgress,
  timing: Timing,
  findClass: (module: string) => string | undefined,
) => {
  const print = printer.print;
  switch (progress.kind) {
    case "parsed":
      timing.isParsed = true;
      if (printer.isTool) print(MESSAGE_CODE.sanyFinished, MESSAGE_LEVEL.none, "SANY finished.");
      print(
        MESSAGE_CODE.starting,
        MESSAGE_LEVEL.none,
        `Starting... (${formatTlcDate(new Date())})`,
      );
      return;
    // TLC 1.7.4 warns about neither a constant-level invariant nor a state-level property.
    case "constant-level-invariant":
      if (printer.version === "1.7.4") return;
      print(
        MESSAGE_CODE.constantLevelInvariant,
        MESSAGE_LEVEL.warning,
        `The invariant ${progress.name} is a constant-level formula (i.e., it contains no variables, primes, or temporal operators) and evaluates to TRUE. To assert constant-level formulas in your spec, use ASSUME ConstInv. If you optionally want to give the assumption a name, write ASSUME YourAssumption == ConstInv instead. See https://explain.tlapl.us/assumptions-and-invariants for additional details.`,
      );
      return;
    case "state-level-property":
      if (printer.version === "1.7.4") return;
      print(
        MESSAGE_CODE.stateLevelProperty,
        MESSAGE_LEVEL.warning,
        `The formula ${progress.name} is a state-level formula, but it was used as a PROPERTY (or PROPERTIES), where a temporal formula is typically expected. State-level formulas used as PROPERTY or PROPERTIES are only checked in the initial state. To verify that the formula ${progress.name} holds in all states of every behavior, use INVARIANT ${progress.name} instead. Alternatively, applying the "always" temporal operator ([]) to the state-level formula ${progress.name} changes it into a temporal formula, asserting that ${progress.name} holds in all states of every behavior. See https://explain.tlapl.us/invariants-and-properties for additional details.`,
      );
      return;
    case "liveness-initializing":
      if (progress.isSymmetric) {
        print(
          MESSAGE_CODE.livenessSymmetry,
          MESSAGE_LEVEL.warning,
          "Declaring symmetry during liveness checking is dangerous. It might cause TLC to miss violations of the stated liveness properties. Please check liveness without symmetry defined.",
        );
      }
      // Only TLC 1.7.4 warns about constraints.
      if (progress.isConstrained && printer.version === "1.7.4") {
        print(
          MESSAGE_CODE.livenessConstraints,
          MESSAGE_LEVEL.warning,
          "Declaring state or action constraints during liveness checking is dangerous: Please read section 14.3.5 on page 247 of Specifying Systems (https://lamport.azurewebsites.net/tla/book.html) and optionally the discussion at https://discuss.tlapl.us/msg00994.html for more details.",
        );
      }
      return;
    case "liveness-prepared":
      print(
        MESSAGE_CODE.temporalBranches,
        MESSAGE_LEVEL.none,
        `Implied-temporal checking--satisfiability problem has ${progress.branches} branches.`,
      );
      return;
    case "java-override": {
      // Class#getResource, which names the class file TLC loads the override from by the path its
      // resolver made, with . and .. resolved by name.
      const location = pathToFileURL(
        resolve(findClass(progress.module) ?? `${progress.module}.class`),
      ).href;
      print(
        progress.isMatched ? MESSAGE_CODE.javaOverrideLoaded : MESSAGE_CODE.javaOverrideMismatch,
        progress.isMatched ? MESSAGE_LEVEL.none : MESSAGE_LEVEL.warning,
        `${progress.isMatched ? "Loading" : "Failed to match"} ${progress.operator} operator override from ${location.replace("file:///", "file:/")} with signature: <Java Method: ${progress.signature}>.`,
      );
      return;
    }
    case "initial-states-started":
      print(MESSAGE_CODE.computingInit, MESSAGE_LEVEL.none, "Computing initial states...");
      return;
    case "initial-states-progress":
      printInitialStatesProgress(printer, progress.count);
      return;
    case "initial-states-computed":
      printInitialStates(printer, progress.initialStates);
      return;
    case "progress":
      printProgress(printer, progress.statistics, timing.startTime);
      return;
    case "liveness-started": {
      timing.livenessStartTime = Date.now();
      // TLC reports how far the search got before it checks the complete state graph.
      if (progress.isComplete) printProgress(printer, progress.statistics);
      const branches = progress.branches > 1 ? `${progress.branches} branches of ` : "";
      print(
        MESSAGE_CODE.checkingTemporal,
        MESSAGE_LEVEL.none,
        `Checking ${branches}temporal properties for the ${progress.isComplete ? "complete" : "current"} state space with ${progress.states} total distinct states at (${formatTlcDate(new Date())})`,
      );
      return;
    }
    case "liveness-finished":
      printLivenessEnd(printer, timing);
      return;
    case "warning":
      print(progress.code, MESSAGE_LEVEL.warning, progress.text);
      return;
    case "violation":
      printViolation(progress.status, progress.violation, printer);
  }
};

const printLivenessEnd = (printer: MessagePrinter, timing: Timing) => {
  if (timing.livenessStartTime === undefined) return;
  printer.print(
    MESSAGE_CODE.checkingTemporalEnd,
    MESSAGE_LEVEL.none,
    `Finished checking temporal properties in ${formatTlcDuration(Date.now() - timing.livenessStartTime)} at ${formatTlcDate(new Date())}`,
  );
  timing.livenessStartTime = undefined;
};

// Prints a violation, and returns whether TLC goes on to print the statistics of the search.
const printViolation = (status: CheckStatus, violation: Violation, printer: MessagePrinter) => {
  const print = printer.print;
  const loopStart = violation.loopStart;
  const isInitial = isInitialViolation(status, violation);
  const headline = getViolationHeadline(status, violation, printer.isTool, printer.version);
  // A safety property's counterexample ends where it breaks, and a liveness one loops back.
  const isProperty = status === "property-violation";
  const isLasso = loopStart !== undefined && !isProperty;
  const isCounterExample = isProperty || isLasso;
  // TLC rebuilds a liveness counterexample before it reports the violation, and 1.7.4's
  // LiveWorker#printTrace after it prints the heading of the counterexample.
  const isRebuiltFirst = isCounterExample && printer.version !== "1.7.4";
  if (isRebuiltFirst) printTraceOutput(printer, violation.trace[0]?.output);
  if (violation.counts) console.log(violation.counts);
  if (headline) {
    // TLC prints the initial state that violates a property in the same message.
    const text = isInitial
      ? `${headline.text}\n${formatState(violation.trace[0].state)}`
      : headline.text;
    print(headline.code, MESSAGE_LEVEL.error, text);
  }
  if (!isInitial) {
    if (!isCounterExample) printTraceOutput(printer, violation.trace[0]?.output);
    printTrace(
      printer,
      violation.trace,
      isCounterExample ? COUNTER_EXAMPLE : undefined,
      isCounterExample && !isRebuiltFirst,
    );
    printTraceOutput(printer, violation.traceOutput);
  }
  if (isLasso) {
    const label = violation.loopLabel;
    if (loopStart === violation.trace.length - 1)
      print(MESSAGE_CODE.statePrint3, MESSAGE_LEVEL.state, `${loopStart + 2}: Stuttering`);
    else if (printer.isTool)
      print(
        MESSAGE_CODE.backToState,
        MESSAGE_LEVEL.state,
        `${loopStart + 1}: Back to state${label ? `: <${label}>\n` : ""}`,
      );
    else console.log(`Back to state ${loopStart + 1}${label ? `: <${label}>\n` : ""}`);
  }
  // TLC 1.7.4 doesn't explain a stuttering counterexample.
  if (violation.warning && printer.version !== "1.7.4")
    print(violation.warning.code, MESSAGE_LEVEL.warning, violation.warning.text);
  // TLC checks the postconditions after it prints a counterexample.
  const postcondition =
    violation.unwitnessed ??
    (status === "postcondition-violation" ? undefined : violation.postcondition);
  if (postcondition?.counts) console.log(postcondition.counts);
  if (postcondition) print(postcondition.code, MESSAGE_LEVEL.error, postcondition.message);
  // TLC checks assumptions before it starts the search, so it has no statistics to print.
  return !isInitial && status !== "assumption-violation";
};

const printNestedExpressions = (printer: MessagePrinter, callStack: Expression[]) =>
  printer.print(
    MESSAGE_CODE.nestedExpression,
    MESSAGE_LEVEL.error,
    `The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n${formatCallStack(callStack)}`,
  );

const printResult = (result: CheckResult, printer: MessagePrinter, timing: Timing) => {
  const print = printer.print;
  if (result.failure) {
    const failure = result.failure;
    const printCallStack = () => {
      const fingerprint = failure.fingerprint;
      if (fingerprint) {
        // TLC prints the call stack when the replay has one, and otherwise the sources of the
        // values it failed to fingerprint, innermost first. TLC 1.7.4 always prints the sources.
        const trace =
          failure.callStack?.length && printer.version !== "1.7.4"
            ? formatCallStack(failure.callStack)
            : formatFingerprintTrace(fingerprint.sources);
        print(
          MESSAGE_CODE.fingerprintFailed,
          MESSAGE_LEVEL.error,
          `TLC was unable to fingerprint.\n\nFingerprint Stack Trace:\n${trace}\nReason:\n${formatNestedMessage(fingerprint.reason, printer.isTool)}`,
        );
        return;
      }
      if (failure.callStack) printNestedExpressions(printer, failure.callStack);
    };
    if (failure.isCallStackFirst) printCallStack();
    const headline = getFailureHeadline(failure, printer.isTool);
    print(headline.code, MESSAGE_LEVEL.error, headline.text);
    printTraceOutput(printer, failure.trace[0]?.output);
    printTrace(printer, failure.trace);
    const traceFailure =
      failure.traceFailure && getMessageHeadline(failure.traceFailure, printer.isTool);
    if (traceFailure) print(traceFailure.code, MESSAGE_LEVEL.error, traceFailure.text);
    printTraceOutput(printer, failure.traceOutput);
    const postcondition = failure.postcondition;
    if (postcondition?.counts) console.log(postcondition.counts);
    if (postcondition) print(postcondition.code, MESSAGE_LEVEL.error, postcondition.message);
    if (!failure.isCallStackFirst) printCallStack();
  } else if (result.violation) {
    if (!printViolation(result.status, result.violation, printer)) return;
    // TLC adds a deadlocked state to the behavior graph after it reports the deadlock, which can
    // violate a temporal property too.
    const additionalViolation = result.additionalViolation;
    if (additionalViolation) printViolation("property-violation", additionalViolation, printer);
    if (result.liveCallStack) printNestedExpressions(printer, result.liveCallStack);
  } else {
    printLivenessEnd(printer, timing);
    const optimistic = getOptimisticProbability(result.distinctStates, result.generatedStates);
    const actual =
      result.fingerprintDistance === undefined
        ? []
        : [
            `  based on the actual fingerprints:  val = ${formatProbability(getActualProbability(result.fingerprintDistance))}`,
          ];
    print(
      MESSAGE_CODE.success,
      MESSAGE_LEVEL.none,
      [
        "Model checking completed. No error has been found.",
        "  Estimates of the probability that TLC did not check all reachable states",
        "  because two distinct states had the same fingerprint:",
        `  calculated (optimistic):  val = ${formatProbability(optimistic)}`,
        ...actual,
      ].join("\n"),
    );
  }
  if (result.failure?.isWithoutStatistics) return;
  if (result.status !== "success") printLivenessEnd(printer, timing);
  if (printer.isTool) printProgress(printer, result, timing.startTime);
  print(
    MESSAGE_CODE.stats,
    MESSAGE_LEVEL.none,
    `${result.generatedStates} states generated, ${result.distinctStates} distinct states found, ${result.queuedStates} states left on queue.`,
  );
  // ModelChecker#printSummary prints the depth, which TLC 1.7.4 prints only after a search it
  // reports as successful, and as at least 1, and then the outdegree of a successful search.
  const is174 = printer.version === "1.7.4";
  const outDegrees = is174 ? (result.outDegrees ?? result.violationOutDegrees) : result.outDegrees;
  if (!is174 || outDegrees) {
    print(
      MESSAGE_CODE.searchDepth,
      MESSAGE_LEVEL.none,
      `The depth of the complete state graph search is ${is174 ? Math.max(result.depth, 1) : result.depth}.`,
    );
  }
  const outDegree = outDegrees && getOutDegreeSummary(outDegrees);
  if (outDegree) print(MESSAGE_CODE.stateGraphOutdegree, MESSAGE_LEVEL.none, outDegree);
};

const printWelcome = (printer: MessagePrinter) =>
  printer.print(MESSAGE_CODE.version, MESSAGE_LEVEL.none, `TLC2 Version ${version} (rev: tla-ts)`);

// TLC.printErrorMsg: TLC says which version it is, then why it can't read its options.
const printCommandLineError = (printer: MessagePrinter, message: string) => {
  printWelcome(printer);
  printer.print(
    MESSAGE_CODE.commandLineError,
    MESSAGE_LEVEL.error,
    `${message}\nUsage: java tlc2.TLC [-help] [-option] inputfile`,
  );
  return 1;
};

// The heap limit the banner reports. Bun's getHeapStatistics walks the whole heap, which took 5 to
// 14 ms of a run's startup, and reports ten times the process's resident memory as the limit, which
// this reads without the walk.
const getHeapLimit = () =>
  process.versions.bun === undefined
    ? getHeapStatistics().heap_size_limit
    : 10 * process.memoryUsage.rss();

// TLC.printStartupBanner, with what runs tla-ts in place of the JVM. tla-ts keeps its fingerprints
// and its queue of states in memory.
const printStartupBanner = (printer: MessagePrinter, seed: string, workers: number) =>
  printer.print(
    MESSAGE_CODE.modelChecking,
    MESSAGE_LEVEL.none,
    `Running breadth-first search Model-Checking with fp 0 and seed ${BigInt(seed)} with ${workers} worker${workers === 1 ? "" : "s"} on ${availableParallelism()} cores with ${Math.floor(getHeapLimit() / 1024 / 1024)}MB heap and 0MB offheap memory [pid: ${process.pid}] (${type()} ${release()} ${arch()}, Node.js ${process.versions.node} ${process.arch.endsWith("64") ? 64 : 32}bit, MemFPSet, MemStateQueue).`,
  );

// TLC loads Integers for the binary trace that its trace exploration spec records. -generateSpecTE
// turns the spec on, and -tool, -continue, -noGenerateSpecTE and -noTE turn it off, as
// -noGenerateSpecTEBin and -noTEBin turn off the binary trace. TLC 1.7.4 records no such trace.
const getFlags = (args: ParsedArgs) => {
  const flags = [...args.unknown, ...args.options.map((option) => option.name)];
  return (name: string, alias = name) =>
    flags.some((flag) => flag === name || flag.toLowerCase() === alias.toLowerCase());
};

// Whether TLC writes the trace exploration spec of an error trace.
const isTraceSpecWritten = (args: ParsedArgs, version: TlcVersion) => {
  const hasFlag = getFlags(args);
  return (
    version !== "1.7.4" &&
    (hasFlag("-generateSpecTE") ||
      (!hasFlag("-noGenerateSpecTE", "-noTE") && !hasFlag("-tool") && !hasFlag("-continue")))
  );
};

const isTraceRecorded = (args: ParsedArgs, version: TlcVersion) =>
  isTraceSpecWritten(args, version) && !getFlags(args)("-noGenerateSpecTEBin", "-noTEBin");

// Where TLC finds the files of the spec it was `given`, as the binary finds them (prove-it-host's
// resolveFiles), throwing where the binary declines what TLC does. `resolverLine` is the Java launch
// and the options that name files, which this check parsed (getResolverLine).
const createFileResolver = (resolverLine: string[], given: string) => {
  const addon = getNativeAddon();
  if (typeof addon === "string") throw new EngineUnavailableError(addon, false);
  const known = new Map<string, string | Uint8Array | undefined>();
  const resolveFile = (request: string) => {
    const resolved = resolveAllFiles(addon, resolverLine, given, request, readFileKey, known);
    if (resolved.kind === "declined") throw new TlaUnsupportedError(resolved.reason);
    return resolved;
  };
  return {
    getSpec: () => {
      const spec = resolveFile("spec");
      if (spec.kind !== "spec") throw new TlaUnsupportedError(`the spec's files as ${spec.kind}`);
      return spec;
    },
    loadModule: (name: string) => {
      const module = resolveFile(`module:${name}`);
      if (module.kind === "unreadable") {
        throw new TlaUnsupportedError(
          `a module's file TLC finds but can't read, such as a directory: ${module.path}`,
        );
      }
      return module.kind === "module" ? module.text : undefined;
    },
    getClass: (name: string) => {
      const found = resolveFile(`class:${name}`);
      return found.kind === "class" ? found : undefined;
    },
    getText: (request: string) => {
      const text = resolveFile(request);
      return text.kind === "text" ? text.text : "";
    },
  };
};

const checkSpec = async (
  resolverLine: string[],
  given: string,
  args: ParsedArgs,
  java: JavaProperties,
  printer: MessagePrinter,
) => {
  // TLC.handleParameters: TLC reads its options before it says which version it is.
  const seed = args.has("-seed") ? args.get("-seed")?.[0] : "0";
  if (seed === undefined) return printCommandLineError(printer, "Error: seed required.");
  if (!isJavaLong(seed)) {
    return printCommandLineError(
      printer,
      `Error: An integer for seed required. But encountered ${seed}`,
    );
  }
  const livenessCheck = args.has("-lncheck") ? args.get("-lncheck")?.[0]?.toLowerCase() : "default";
  if (livenessCheck === undefined) {
    return printCommandLineError(
      printer,
      "Error: expect a strategy such as final for -lncheck option.",
    );
  }
  const dumpValues = args.get("-dump");
  if (dumpValues?.length === 0) {
    return printCommandLineError(printer, "Error: A file name for dumping states required.");
  }
  const unsupportedFormat =
    dumpValues?.length === 2 &&
    UNSUPPORTED_DUMP_FORMATS.find((format) => dumpValues[0].toLowerCase().includes(format));
  if (unsupportedFormat) {
    console.error(`Error: tla-ts does not support the -dump format ${unsupportedFormat}.`);
    return 1;
  }
  const fingerprintIndex = args.get("-fp")?.[0];
  if (fingerprintIndex !== undefined && Number(fingerprintIndex) !== 0) {
    console.error(
      `Error: tla-ts fingerprints states as TLC does with -fp 0, not -fp ${fingerprintIndex}.`,
    );
    return 1;
  }
  const workers = getWorkerCount(args.get("-workers"));
  const version = printer.version;
  printWelcome(printer);
  printStartupBanner(printer, seed, workers);
  const files = createFileResolver(resolverLine, given);
  const spec = files.getSpec();
  if (spec.missingConfig !== undefined) {
    printer.print(
      MESSAGE_CODE.configFileError,
      MESSAGE_LEVEL.error,
      `TLC encountered the following error when trying to read the configuration file ${spec.missingConfig}:\nFile not found.`,
    );
    return EXIT_STATUS.configParseError;
  }
  // TLC prints that it can't read a file it finds that isn't one, such as a directory, which
  // tla-ts doesn't.
  if (spec.unreadable !== undefined) {
    throw new TlaUnsupportedError(
      `a file TLC finds but can't read, such as a directory: ${spec.unreadable}`,
    );
  }
  const specPath = spec.path;
  const configPath = spec.config ?? "";
  const fileName = basename(specPath, ".tla");
  const timing: Timing = { startTime: Date.now(), livenessStartTime: undefined, isParsed: false };
  // Without -tool, TLC prints how long it ran for a person to read.
  const printFinished = () => {
    const runtime = Date.now() - timing.startTime;
    printer.print(
      MESSAGE_CODE.finished,
      MESSAGE_LEVEL.none,
      `Finished in ${printer.isTool ? `${runtime}ms` : formatTlcDuration(runtime)} at (${formatTlcDate(new Date())})`,
    );
  };
  const printParsingFailed = () =>
    printer.print(
      MESSAGE_CODE.parsingFailed,
      MESSAGE_LEVEL.error,
      "Parsing or semantic analysis failed.",
    );
  // TLC prints how long it ran even when it stops at an error.
  const printFailure = (error: TlaError) => {
    if (error instanceof TlaSyntaxError) {
      printParsingFailed();
    } else {
      printError(error, printer);
    }
    printFinished();
    return getErrorExitCode(error);
  };
  // TLC reads the configuration file before it parses the spec, and prints how long it ran even
  // when it can't read it.
  const config = (() => {
    try {
      return parseConfig(readFileSync(configPath, "utf8"), version);
    } catch (error) {
      if (!(error instanceof TlaConfigError)) throw error;
      return error;
    }
  })();
  // TLC 1.7.4 reports a configuration file it can't parse as an exception it didn't expect.
  if (config instanceof TlaConfigError && version === "1.7.4") {
    printer.print(
      MESSAGE_CODE.general,
      MESSAGE_LEVEL.error,
      `${getUnexpectedException("tlc2.tool.ConfigFileException")}${formatNestedMessage(config.message, printer.isTool)}`,
    );
    printFinished();
    return EXIT_STATUS.error;
  }
  if (config instanceof TlaConfigError) return printFailure(config);
  if (args.has("-deadlock")) config.checkDeadlock = false;
  const loadModule = files.loadModule;
  const findClass = (name: string) => files.getClass(name)?.path;
  const isRecorded = isTraceRecorded(args, version);
  if (printer.isTool) {
    printer.print(MESSAGE_CODE.startingSany, MESSAGE_LEVEL.none, "Starting SANY...");
  }
  // SANY names the spec as TLC's arguments do.
  const specName = spec.name;
  if (spec.missing !== undefined) console.error(spec.missing);
  const describeFile = (name: string, origin: SanyModuleOrigin) =>
    files.getText(`file:${origin}:${name}`);
  // TLC prints what SANY prints as it parses the spec, and the errors it rejects the spec for, as
  // tla-front writes them where it does. It doesn't write TLC 1.7.4's, nor the trace exploration
  // spec's TLC parses with the spec, which the TypeScript report does.
  const nativeSany =
    version === "master" && !isRecorded && existsSync(specPath)
      ? getNativeSanyReport(specPath, readFileSync(specPath, "utf8"), version, {
          fileName: specName,
          loadModule,
          describeFile,
        })
      : undefined;
  if (nativeSany) writeOutput(1, nativeSany.text);
  const sany =
    nativeSany ??
    getSanyReport(
      specPath,
      // TLC 1.7.4's SANY reports each module it can't find as it looks for it.
      version === "1.7.4"
        ? (name: string) => {
            const text = loadModule(name);
            if (text === undefined && !SANY_174_STANDARD_MODULES.has(name)) {
              console.error(files.getText(`missing:${name}.tla`));
            }
            return text;
          }
        : loadModule,
      {
        fileName: specName,
        describeFile,
        version,
        // TLC's trace exploration spec records the trace with the post condition of _TLCTrace.
        rootExtendees: isRecorded ? ["_TLCTrace"] : undefined,
        precomputed: version === "master" ? readSanySnapshot() : undefined,
        onPrint: (text) => writeOutput(1, text),
        onPrintError: (text) => writeOutput(2, text),
      },
    );
  if (sany.isFailed) {
    printCheckProgress(printer, { kind: "parsed" }, timing, findClass);
    printParsingFailed();
    printFinished();
    return EXIT_STATUS.specParseError;
  }
  // SANY rejected a spec whose module isn't named for its file, so check reads the spec's module.
  try {
    const source = readFileSync(specPath, "utf8");
    const result = await checkParsed(
      {
        workers,
        livenessCheck: ["final", "seqfinal", "off"].includes(livenessCheck) ? "final" : "default",
        seed: BigInt(seed),
        // What a JVM sets of the platform, then what the launch sets.
        systemProperties: new Map([
          ["file.separator", sep],
          ["path.separator", delimiter],
          ["line.separator", EOL],
          ["user.dir", process.cwd()],
          ...java.properties,
        ]),
        dump: dumpValues && getStateDump(dumpValues),
        isTool: printer.isTool,
        isContinued: args.has("-continue"),
        isTraceRecorded: isRecorded,
        isSanyReported: true,
        isWarningEnabled: !args.has("-nowarning"),
        version,
        onProgress: (progress) => printCheckProgress(printer, progress, timing, findClass),
        source,
        config,
        onPause: () => readSync(0, Buffer.alloc(1)),
        loadModule,
        loadClass: (name) => files.getClass(name)?.bytes,
        readFile: (path) => (existsSync(path) ? readFileSync(path, "utf8") : undefined),
        writeFile: (path, content) => {
          mkdirSync(dirname(resolve(path)), { recursive: true });
          writeFileSync(path, content);
        },
      },
      sany.readings,
    );
    // TLC writes the trace exploration spec of a trace of two states or more and prints its path,
    // which only the native check writes.
    if (
      isTraceSpecWritten(args, version) &&
      !fileName.includes("_TTrace") &&
      [result.violation, result.failure].some((error) => (error?.trace.length ?? 0) > 1)
    ) {
      console.error("prove-it: not native yet: the trace exploration spec of an error trace");
      return NOT_NATIVE_EXIT_CODE;
    }
    printResult(result, printer, timing);
    printFinished();
    return result.failure?.exitCode ?? EXIT_CODES[result.status];
  } catch (error) {
    if (!(error instanceof TlaError)) throw error;
    if (error instanceof TlaSyntaxError) console.log(formatSanyErrors(error, fileName));
    if (!timing.isParsed) printCheckProgress(printer, { kind: "parsed" }, timing, findClass);
    return printFailure(error);
  }
};

// What SANY prints about a spec it rejects: a module it can't find or parse is a fatal error, and
// it reports the other errors as semantic errors.
const formatSanyErrors = (error: TlaSyntaxError, specName: string) => {
  const isFatal = error instanceof TlaSanyFatalError;
  if (!isFatal && !error.failure)
    return `Semantic errors:\n\n*** Errors: 1\n\n${error.message}\n\n`;
  const report = !isFatal
    ? `In module ${specName}\n\nCould not parse module ${specName} from file ${specName}.tla`
    : error.location === undefined
      ? `Unknown location\n\n${error.message}`
      : `In module ${error.location}\n\n${error.message}`;
  const parseError = error.failure ? `***Parse Error***\n${error.message}\n\n` : "";
  return `${parseError}\nFatal errors while parsing TLA+ spec in file ${specName}\n\n${report}\n*** Errors: 1\n\n${report}\n\n\n`;
};

// The specs the command line names: like TLC, a spec named without an extension is the .tla file
// of that name. A glob also matches modules that only other specs import, which have no
// configuration.
const getSpecPaths = (parsed: ParsedArgs) =>
  getInputPaths(parsed.positionals)
    .map((input) => ({
      ...input,
      path:
        input.isGlobbed || /\.(tla|cfg)$/.test(input.path)
          ? input.path.replace(/\.cfg$/, ".tla")
          : `${input.path}.tla`,
    }))
    .filter(
      (input) =>
        input.path.endsWith(".tla") &&
        (!input.isGlobbed ||
          parsed.has("-config") ||
          existsSync(input.path.replace(/\.tla$/, ".cfg"))),
    )
    .map((input) => input.path);

// The check the native binary runs for the command line, run in-process: its exit code, once it
// printed what the binary prints, or undefined where it declines the model or no engine loads, for
// the TypeScript check to check it. The command line is TLC's as given, the Java launch's included.
// What the check prints waits until it is known not to decline, which it can do part way through
// the search, so that a model it declines prints only once.
export const checkNatively = async (commandLine: string[]) => {
  if (isTypeScriptCheckAsked()) return undefined;
  const startedAt = performance.now();
  await loadWasmEngine();
  const addon = getNativeAddon();
  if (typeof addon === "string") return undefined;
  const result = checkAllSources(addon, commandLine, getMachine(), readFileKey);
  if (result.kind === "declined") {
    reportEngine(`native: checkSources declined: ${result.reason}`);
    return undefined;
  }
  reportEngine(
    `native: checkSources: exit ${result.exitCode} (${(performance.now() - startedAt).toFixed(2)} ms)`,
  );
  // What the check wrote, in its order, into the directories the CLI said it can write.
  result.writes.forEach((write) =>
    (write.isAppended ? appendFileSync : writeFileSync)(write.path, write.bytes),
  );
  process.stdout.write(result.out);
  process.stderr.write(result.err);
  return result.exitCode;
};

export const checkSpecs = async (
  commandLine: string[],
  args: string[],
  java: JavaProperties,
  isTlcLaunch = false,
) => {
  // Only the native check writes -dumpTrace's files, such as where it can't write them.
  if (args.includes("-dumpTrace")) {
    console.error("prove-it: not native yet: -dumpTrace");
    return NOT_NATIVE_EXIT_CODE;
  }
  const parsed = CHECK_COMMAND.parse(args);
  const isConfigured = parsed.has("-config");
  const specPaths = getSpecPaths(parsed);
  // TLC reads every option before it finds no spec, as the native check does and this doesn't.
  if (specPaths.length === 0 && isTlcLaunch) {
    throw new TlaUnsupportedError("a TLC command line without a spec");
  }
  if (specPaths.length === 0) {
    console.error(USAGE);
    return 1;
  }
  if (isConfigured && specPaths.length > 1) {
    console.error("Error: -config applies to one specification, but several were given.");
    return 1;
  }
  // The command line the resolver reads: the Java launch, before TLC's `args`, with the TLC version
  // the launch already read from its jar first, so that no request reads the jar again; then the
  // options that name files, as this check parsed them, since the binary's parser declines some
  // options this check takes.
  const resolverLine = [
    ...(java.tlcVersion === undefined ? [] : [`-Dtla-ts.tlc=${java.tlcVersion}`]),
    ...commandLine.slice(0, commandLine.length - args.length),
    ...["-config", "-metadir"].flatMap((name) => {
      const value = parsed.get(name)?.[0];
      // TLC reports the option's missing value where it reads it, among the other options.
      if (parsed.has(name) && value === undefined) {
        throw new TlaUnsupportedError(`${name} without a value`);
      }
      return value === undefined ? [] : [name, value];
    }),
  ];
  // TLC checks a spec it finds on the library path once however it is named.
  await loadWasmEngine();
  const paths = [
    ...new Map(
      specPaths.map((given) => [createFileResolver(resolverLine, given).getSpec().path, given]),
    ).entries(),
  ];
  // Each spec is checked as TLC would in a process of its own, so an error in one leaves the others
  // to report. The exit code is the first that is not success.
  const exitCodes: number[] = [];
  for (const [index, [path, given]] of paths.entries()) {
    if (index > 0) console.log("");
    // TLC checks one spec, so tla-ts names each of several it checks.
    if (paths.length > 1)
      console.log(`Checking ${basename(path)} with ${basename(path, ".tla")}.cfg`);
    const printer = createMessagePrinter(
      parsed.has("-tool"),
      !parsed.has("-nowarning"),
      java.tlcVersion ?? "master",
    );
    exitCodes.push(
      await reportErrors(() => checkSpec(resolverLine, given, parsed, java, printer), printer),
    );
  }
  return exitCodes.find((exitCode) => exitCode !== EXIT_STATUS.success) ?? EXIT_STATUS.success;
};
