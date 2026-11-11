// The native engine's prover, for the scripts and tests that compare it with tlapm: a module's
// obligations as tlapm prints them, the texts Prep sends their backends and their fingerprints,
// each of which throws the error the obligations throw, and the Rust driver's proof of them.

import {
  getNativeAddon,
  type NativeDecideRequest,
  type NativeObligationError,
} from "../src/engine/native";
import {
  EngineUnavailableError,
  TlapmBugError,
  TlaProofError,
  TlaProverError,
  TlaSyntaxError,
  TlaUnsupportedError,
} from "../src/errors";

// A module that another reads, and the file it came from, which errors name.
interface LoadedModule {
  file: string;
  source: string;
}

type ModuleLoader = (name: string) => LoadedModule | undefined;

interface Needed {
  kind: "needed";
  keys: string[];
}

const BUG_MESSAGE = new TlapmBugError().message;

// The error the obligations threw, as its class in errors.ts.
export const getObligationError = (error: NativeObligationError) => {
  if (error.name === "TlaProofError")
    return error.message === BUG_MESSAGE
      ? new TlapmBugError(error.exception)
      : new TlaProofError(
          error.message,
          error.failure === undefined ? { exception: error.exception } : { failure: error.failure },
        );
  if (error.name === "TlaSyntaxError") return new TlaSyntaxError(error.message);
  if (error.name === "TlaUnsupportedError") return new TlaUnsupportedError(error.message);
  return new TlaProverError(error.message);
};

const getAddon = () => {
  const addon = getNativeAddon();
  if (typeof addon === "string") throw new EngineUnavailableError(addon);
  return addon;
};

// What call returns once it has every module it reads, each read as loadModule finds it: a key
// `module:<name>#<n>` and `path:<name>#<n>` names its n-th read.
const readModules = <Result extends { kind: string }>(
  call: (known: [string, string | undefined][]) => Result | Needed | NativeObligationError,
  loadModule: ModuleLoader,
): Result => {
  const known = new Map<string, string | undefined>();
  for (;;) {
    const result = call([...known]);
    if ("keys" in result) {
      result.keys.forEach((key) => {
        const read = key.slice(key.indexOf(":") + 1);
        const loaded = loadModule(read.slice(0, read.lastIndexOf("#")));
        known.set(`module:${read}`, loaded?.source);
        known.set(`path:${read}`, loaded?.file);
      });
      continue;
    }
    if ("name" in result) throw getObligationError(result);
    return result;
  }
};

// The obligations of the module in file, every result's in order, and the text each backend
// receives for each [id, prover] of encode, or the error that stops it. The SMT encoder counts its
// CASE errors across encode, in order.
export const getObligations = (
  file: string,
  source: string,
  loadModule: ModuleLoader,
  encode: [number, string][] = [],
) => {
  const result = readModules(
    (known) => getAddon().obligations(file, source, known, encode),
    loadModule,
  );
  return {
    obligations: result.obligations,
    encodings: result.encodings.map((encoding) =>
      encoding.kind === "text" ? encoding.text : getObligationError(encoding),
    ),
  };
};

// The text one backend receives for an obligation, as prove would send it.
export const encodeForBackend = (
  file: string,
  source: string,
  loadModule: ModuleLoader,
  id: number,
  prover: string,
) => {
  const encoding = getObligations(file, source, loadModule, [[id, prover]]).encodings[0];
  if (encoding instanceof Error) throw encoding;
  return encoding;
};

// Each obligation's fingerprint, as tlapm's fp_sequent makes it, or the error that stops it.
export const getFingerprints = (file: string, source: string, loadModule: ModuleLoader) =>
  readModules((known) => getAddon().fingerprint(file, source, known), loadModule).fingerprints.map(
    (entry) => ({
      id: entry.id,
      fingerprint:
        typeof entry.fingerprint === "string"
          ? entry.fingerprint
          : getObligationError(entry.fingerprint),
    }),
  );

// What the Rust driver proves of the module in file, in rounds: each asks for the modules and the
// decisions it needs, which loadModule and answer give, and the next starts again with them. An
// answer is "<verdict> <timeUsedMs>", "error:<message>" for a TlaProverError the backend threw, or
// "unsupported:<message>" for a TlaUnsupportedError.
export const proveInRounds = (
  file: string,
  source: string,
  loadModule: (name: string) => string | undefined,
  answer: (request: NativeDecideRequest) => string,
) => {
  const known = new Map<string, string | undefined>();
  for (;;) {
    const result = getAddon().prove(file, source, [...known]);
    if (result.kind !== "needed") return result;
    result.keys.forEach((key) =>
      known.set(key, loadModule(key.slice("module:".length, key.lastIndexOf("#")))),
    );
    result.requests.forEach((request) => known.set(`decide:${request.key}`, answer(request)));
  }
};
