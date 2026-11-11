import type { SourceRange } from "./ast";
import { EXIT_STATUS, getExitCode, setExitCode } from "./exit-codes";
import type { PcalNode } from "./pcal/ast";
import type { Value } from "./values";

// The start of TLC's message for an exception of a Java class it didn't expect.
export const getUnexpectedException = (exceptionClass: string) =>
  `TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a ${exceptionClass}\n: `;

// How TLC reports a RuntimeException it did not expect, such as one raised while computing next
// states.
export const UNEXPECTED_EXCEPTION = getUnexpectedException("java.lang.RuntimeException");

export const UNEXPECTED_EVAL_EXCEPTION = getUnexpectedException("tlc2.tool.EvalException");

// The RangeError for a stack overflow, which TLC raises as a Java StackOverflowError. V8 and
// JavaScriptCore word it the same, but JavaScriptCore ends it with a period.
export const isStackOverflow = (error: unknown) =>
  error instanceof RangeError && /^Maximum call stack size exceeded\.?$/.test(error.message);

export class TlaError extends Error {
  constructor(message: string, cause?: unknown) {
    super(message, { cause });
    this.name = "TlaError";
  }
}

export interface SyntaxFailure {
  reason: string;
  line: number;
  column: number;
  isEnd: boolean;
}

// An error SANY reports at a location, such as "In module M" or a range in a module.
export interface SanyError {
  location: string;
  message: string;
}

// The errors SANY reports for a spec, and the warnings it prints before them. A fatal error stops it
// before semantic analysis. SANY's parser prints its message for a module it rejects before the
// report.
interface SanyReport {
  errors: SanyError[];
  warnings: SanyError[];
  isFatal: boolean;
  parseError?: string;
}

export class TlaSyntaxError extends TlaError {
  failure: SyntaxFailure | undefined;
  sany: SanyReport | undefined;

  constructor(message: string, cause?: unknown, failure?: SyntaxFailure, sany?: SanyReport) {
    super(message, cause);
    this.name = "TlaSyntaxError";
    this.failure = failure;
    this.sany = sany;
  }
}

// A fatal error of SANY's parsing phase: a module SANY can't find or parse, a file whose name
// doesn't match its module's, or a circular dependency. SANY reports it in the module that imports
// or holds the failed one, or without a location, after its JavaCC parser's report of a module it
// failed to parse. It keeps the name TlaSyntaxError, and index.ts doesn't export it.
export class TlaSanyFatalError extends TlaSyntaxError {
  location: string | undefined;
  parseError: string | undefined;

  constructor(message: string, location: string | undefined, parseError?: string) {
    super(message);
    this.location = location;
    this.parseError = parseError;
  }
}

// A module that another imports and SANY can't find, which SANY reports in the importer, except
// TLC 1.7.4's SANY, which gives it no location.
export class TlaMissingModuleError extends TlaSanyFatalError {
  constructor(name: string, importer: string | undefined, isLocated = true) {
    super(
      `Cannot find source file for module ${name} imported in module ${importer}.`,
      isLocated ? importer : undefined,
    );
  }
}

export const createSanyError = (
  errors: SanyError[],
  isFatal = false,
  parseError?: string,
  warnings: SanyError[] = [],
) =>
  new TlaSyntaxError(
    errors.map((error) => `${error.location}\n\n${error.message}`).join("\n\n"),
    undefined,
    undefined,
    { errors, warnings, isFatal, parseError },
  );

export const createMissingModuleError = (name: string, importer: string | undefined) =>
  createSanyError(
    [
      {
        location: `In module ${importer}`,
        message: `Cannot find source file for module ${name} imported in module ${importer}.`,
      },
    ],
    true,
  );

// How SANY prints the warnings it reports, which do not stop TLC.
export const formatSanyWarnings = (warnings: SanyError[]) =>
  `*** Warnings: ${warnings.length}\n\n${warnings.map((warning) => `${warning.location}\n\n${warning.message}\n\n\n`).join("\n")}`;

export const formatRange = (range: SourceRange) =>
  `line ${range.start.line}, col ${range.start.column} to line ${range.end.line}, col ${range.end.column} of module ${range.module}`;

export const createSemanticError = (message: string, range: SourceRange) =>
  createSanyError([{ location: formatRange(range), message }]);

export class TlaConfigError extends TlaError {
  constructor(message: string, cause?: unknown) {
    super(message, cause);
    this.name = "TlaConfigError";
  }
}

export class TlaEvaluationError extends TlaError {
  constructor(message: string, cause?: unknown) {
    super(message, cause);
    this.name = "TlaEvaluationError";
  }
}

export const STACK_OVERFLOW_MESSAGE =
  "This was a Java StackOverflowError. It was probably the result\nof an incorrect recursive function definition that caused TLC to enter\nan infinite loop when trying to compute the function or its application\nto an element in its putative domain.";

// A Java StackOverflowError, which TLC catches only at the top, unlike the exceptions of evaluation.
export class TlaStackOverflowError extends TlaEvaluationError {
  constructor() {
    super(STACK_OVERFLOW_MESSAGE);
  }
}

// TLC reports a stack overflow outside the computation of states on its own, and exits with 255.
export const createStackOverflowError = () =>
  setExitCode(new TlaStackOverflowError(), EXIT_STATUS.error);

// A next-state action left variables of a successor state unassigned. TLC reports the partial
// state, with null for each unassigned variable.
export class TlaIncompleteSuccessorError extends TlaEvaluationError {
  state: (Value | undefined)[];
  action: string | undefined;
  variables: string[];

  constructor(
    message: string,
    state: (Value | undefined)[],
    action: string | undefined,
    variables: string[],
  ) {
    super(message);
    this.state = state;
    this.action = action;
    this.variables = variables;
  }
}

// An expression read a variable that its state doesn't assign. It keeps the name
// TlaEvaluationError, and index.ts doesn't export it.
export class TlaUnassignedError extends TlaEvaluationError {
  variable: string;

  constructor(message: string, variable: string) {
    super(message);
    this.variable = variable;
  }
}

// An evaluation error that TLC raises as an EvalException from a standard module's Java code. It
// keeps the name TlaEvaluationError, and index.ts doesn't export it.
export class TlaModuleError extends TlaEvaluationError {
  exitCode: number;

  constructor(message: string, exitCode: number = EXIT_STATUS.error) {
    super(message);
    this.name = "TlaEvaluationError";
    this.exitCode = exitCode;
  }
}

// TLC reports an initial state that the initial predicate leaves incomplete as an illegal state.
export class TlaIllegalStateError extends TlaEvaluationError {
  state: (Value | undefined)[];

  constructor(state: (Value | undefined)[]) {
    super("current state is not a legal state");
    this.name = "TlaEvaluationError";
    this.state = state;
  }
}

interface TlapmReport {
  failure?: string;
  exception?: string;
}

export class TlaProofError extends TlaError {
  failure: string | undefined;
  exception: string;

  constructor(message: string, report: TlapmReport = {}) {
    super(message);
    this.name = "TlaProofError";
    this.failure = report.exception === undefined ? (report.failure ?? message) : undefined;
    this.exception = report.exception ?? `Failure(${JSON.stringify(this.failure)})`;
  }
}

// tlapm fails one of its own assertions, which it reports as a bug in itself. It keeps the name
// TlaProofError, and index.ts doesn't export it.
export class TlapmBugError extends TlaProofError {
  constructor(exception = "Assert_failure") {
    super("Oops, this seems to be a bug in TLAPM.", { exception });
    this.name = "TlaProofError";
  }
}

// A backend can't take an obligation, which tlapm reports as not tried.
export class TlaProverError extends TlaError {
  constructor(message: string, cause?: unknown) {
    super(message, cause);
    this.name = "TlaProverError";
  }
}

export class TlaUnsupportedError extends TlaError {
  constructor(message: string, cause?: unknown) {
    super(message, cause);
    this.name = "TlaUnsupportedError";
  }
}

// The engine broke one of its own invariants, or one of its self-checks (PROVE_IT_EPOCH_CHECK,
// PROVE_IT_LIVE_CHECK, PROVE_IT_FINGERPRINT=check) found two ways of computing one answer that
// disagree: a bug in the engine rather than in the spec. index.ts doesn't export it.
export class EngineInvariantError extends TlaError {
  constructor(message: string) {
    super(message);
    this.name = "EngineInvariantError";
  }
}

// No native engine loads: no platform package for this system is installed, its addon fails to
// load, or, where there is no process.dlopen, the WebAssembly engine doesn't. check doesn't fall
// back to a slower search unasked: PROVE_IT_ENGINE=0 checks with the interpreter.
export class EngineUnavailableError extends Error {
  constructor(reason: string) {
    super(
      `The native engine is unavailable: ${reason}. Install @atemp/prove-it with its optional dependencies on a supported platform, or set PROVE_IT_ENGINE=0 to check with the interpreter.`,
    );
    this.name = "EngineUnavailableError";
  }
}

// The engine as WebAssembly runs on the host's call stack, so it stops a recursion deeper than that
// stack holds (MAXIMUM_RECURSION in machine.rs), or traps where a deeper frame exhausts it. check
// doesn't search again with a slower engine unasked: the addon and the binary recurse further.
export class WebAssemblyStackError extends Error {
  constructor() {
    super(
      "The WebAssembly engine ran out of stack: the spec recurses deeper than the host's stack holds there, about 1,000 calls of a recursive operator. Check it with the native addon or the prove-it binary, which recurse to 20,000 calls, or set PROVE_IT_ENGINE=0 to check with the interpreter.",
    );
    this.name = "WebAssemblyStackError";
  }
}

// A file the build puts beside the bundle, such as a worker's entry or SANY's snapshot of the
// standard modules, isn't there: the build left it out, or put it where the bundle doesn't look.
// index.ts doesn't export it.
export class MissingBuildFileError extends TlaError {
  constructor(url: URL) {
    super(`Cannot find ${url.href}, which the build puts beside the bundle.`);
    this.name = "MissingBuildFileError";
  }
}

export const getErrorExitCode = (error: TlaError) =>
  getExitCode(error) ??
  (error instanceof TlaSyntaxError
    ? EXIT_STATUS.specParseError
    : error instanceof TlaConfigError
      ? EXIT_STATUS.configParseError
      : error instanceof TlaEvaluationError
        ? EXIT_STATUS.specEvaluationFailure
        : EXIT_STATUS.error);

// pcal.UnrecoverableException and its subclasses: an error the PlusCal translator reports as
// "Unrecoverable error". UnrecoverablePositionedException adds the statement the error is at.
export class PcalError extends TlaError {
  node: PcalNode | undefined;

  constructor(message: string, node?: PcalNode) {
    super(message);
    this.name = "PcalError";
    this.node = node;
  }
}

// A RuntimeException the translator's Java code throws, such as an index out of bounds, which
// ParseAlgorithm.getAlgorithm turns into a parsing error.
export class PcalRuntimeError extends TlaError {
  constructor(message: string) {
    super(message);
    this.name = "PcalRuntimeError";
  }
}

// PcalDebug.ReportBug: the translator found itself in a state it considers a bug, and throws a
// java.lang.Error that nothing in SANY catches.
export class PcalBugError extends TlaError {
  constructor(message: string) {
    super(
      `You have discovered a bug in pcal.trans.\nSend the following information and the\ninput file to the current maintainer(s).\n\n -- ${message}.`,
    );
    this.name = "PcalBugError";
  }
}
