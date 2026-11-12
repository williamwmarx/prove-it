// The enumeration oracle (native/DESIGN.md 6.8): seeded small sets TLC keeps lazy, each
// enumerated in the order a quantifier binds its elements and the order x' \in S assigns them, by
// TLC's own classes (native/oracle/ValueOracle.java) and by the native engine (replay enumerate).
// Where both answer, they must list the same elements in the same order. --record freezes a sample of the cases, with TLC's
// answers, into tests/conformance/enumeration, which cargo test (replay's tests) and
// tests/unit/enumeration-oracle.test.ts check without Java.
// Usage: TLA2TOOLS_JAR=... bun scripts/run.ts enumeration-oracle [--cases 100000] [--seed 1]
//        [--record 400]

import { spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { getOption } from "./corpora";
import { CASE_STRINGS, encodeText, toCaseAnswers, toRequests } from "./enumeration-cases";

const caseCount = Number(getOption("--cases") ?? 100000);
const seed = Number(getOption("--seed") ?? 1);
const recordCount = getOption("--record");
const jar = process.env.TLA2TOOLS_JAR;
if (!jar) {
  console.error("Set TLA2TOOLS_JAR to tla2tools.jar");
  process.exit(2);
}

const NATIVE_DIRECTORY = join(import.meta.dirname, "../native");
const RECORD_DIRECTORY = join(import.meta.dirname, "../tests/conformance/enumeration");
const BATCH = 5000;

const directory = mkdtempSync(join(tmpdir(), "enumeration-oracle-"));
const compiled = spawnSync(
  "javac",
  ["-cp", jar, "-d", directory, join(NATIVE_DIRECTORY, "oracle/ValueOracle.java")],
  { stdio: "inherit" },
);
if (compiled.status !== 0) process.exit(compiled.status ?? 1);
const built = spawnSync("cargo", ["build", "--release", "--locked", "-p", "replay"], {
  cwd: NATIVE_DIRECTORY,
  stdio: "inherit",
});
if (built.status !== 0) process.exit(built.status ?? 1);

const random = { state: seed >>> 0 || 1 };
const next = (bound: number) => {
  random.state ^= random.state << 13;
  random.state ^= random.state >>> 17;
  random.state ^= random.state << 5;
  random.state >>>= 0;
  return random.state % bound;
};

interface Generated {
  tokens: string;
  // At most how many elements the set has.
  size: number;
}

const LIMIT = 300;

// The atoms of a case: integers or strings, mostly one kind a case, so most of its sets compare.
const atom = { isText: false };
const generateAtom = () =>
  (next(20) === 0 ? next(2) === 0 : atom.isText)
    ? `s${encodeText(CASE_STRINGS[next(CASE_STRINGS.length)])}`
    : `i${next(5)}`;

// A set enumeration of a few atoms, or of sets of them.
const generateSet = (depth: number): Generated => {
  const size = next(4);
  const isNested = depth > 0 && next(4) === 0;
  const elements = Array.from({ length: size }, () =>
    isNested ? generateSet(depth - 1).tokens : generateAtom(),
  );
  return { tokens: [`S${size}`, ...elements].join(" "), size };
};

const combine = (prefix: string, parts: Generated[], size: number): Generated => ({
  tokens: [prefix, ...parts.map((part) => part.tokens)].join(" "),
  size,
});

// A lazy set of at most LIMIT elements, over set enumerations and lazy sets.
const generate = (depth: number): Generated => {
  if (depth === 0) return generateSet(1);
  const generated = generateLazy(depth);
  return generated.size > LIMIT ? generate(depth) : generated;
};

const generateLazy = (depth: number): Generated => {
  switch (next(9)) {
    case 0:
      return generateSet(1);
    case 1: {
      const base = generate(depth - 1);
      return combine("Lp", [base], 2 ** base.size);
    }
    case 2: {
      const domain = generate(depth - 1);
      const range = generate(depth - 1);
      return combine("Lf", [domain, range], range.size ** domain.size);
    }
    case 3: {
      const names = CASE_STRINGS.filter(() => next(2) === 0);
      const fields = (names.length === 0 ? ["a"] : names).sort(() => next(3) - 1);
      const sets = fields.map(() => generate(depth - 1));
      return {
        tokens: [
          `Lr${fields.length}`,
          ...fields.map((name, index) => `s${encodeText(name)} ${sets[index].tokens}`),
        ].join(" "),
        size: sets.reduce((product, set) => product * set.size, 1),
      };
    }
    case 4: {
      const factors = Array.from({ length: 1 + next(3) }, () => generate(depth - 1));
      return combine(
        `Lx${factors.length}`,
        factors,
        factors.reduce((product, factor) => product * factor.size, 1),
      );
    }
    default: {
      const operator = "uuid"[next(4)];
      const left = generate(depth - 1);
      // Half the time a set of the left one's shape with other atoms, whose elements compare.
      const right =
        next(2) === 0
          ? { tokens: left.tokens.replace(/\bi\d+/g, () => generateAtom()), size: left.size }
          : generate(depth - 1);
      return combine(`L${operator}`, [left, right], left.size + right.size);
    }
  }
};

const isFailure = (answer: string) => answer.startsWith("!");
const isAgreed = (left: string, right: string) =>
  left === right || (isFailure(left) && isFailure(right));

// How an answer compares with the answer it's checked against: the same, a stop where the other
// answers (which costs a hand-over), an answer where the other fails (which skips a failure TLC
// reports), or other elements or another order.
const classify = (answer: string, expected: string) =>
  isAgreed(answer, expected)
    ? "same"
    : isFailure(answer)
      ? "stopsAlone"
      : isFailure(expected)
        ? "missesFailure"
        : "differs";

const tally: Record<string, number> = { cases: 0, enumerations: 0, allAnswer: 0, allFail: 0 };
const count = (name: string) => {
  tally[name] = (tally[name] ?? 0) + 1;
};
const examples: string[] = [];
const recorded: { tokens: string; answers: [string, string] }[] = [];
const seen = new Set<string>();

for (let start = 0; start < caseCount; start += BATCH) {
  const cases: string[] = [];
  while (cases.length < Math.min(BATCH, caseCount - start)) {
    atom.isText = next(2) === 0;
    const tokens = generate(3).tokens;
    cases.push(tokens);
  }
  const requests = `${toRequests(cases).join("\n")}\n`;
  const tlc = spawnSync("java", ["-cp", `${jar}:${directory}`, "ValueOracle"], {
    input: requests,
    encoding: "utf8",
    maxBuffer: 1 << 30,
  });
  const requestPath = join(directory, "requests.txt");
  writeFileSync(requestPath, requests);
  const native = spawnSync(
    join(NATIVE_DIRECTORY, "target/release/replay"),
    ["enumerate", requestPath],
    {
      encoding: "utf8",
      maxBuffer: 1 << 30,
    },
  );
  const tlcAnswers = toCaseAnswers(tlc.stdout.split("\n"));
  const nativeAnswers = toCaseAnswers(native.stdout.split("\n"));
  cases.forEach((tokens, index) => {
    count("cases");
    for (const order of [0, 1]) {
      count("enumerations");
      const fromTlc = tlcAnswers[index * 2 + order];
      const fromNative = nativeAnswers[index * 2 + order];
      const describe = `${order === 0 ? "q" : "s"} ${tokens}: TLC ${fromTlc}, native ${fromNative}`;
      const outcome = classify(fromNative, fromTlc);
      if (outcome !== "same") {
        count(`native against TLC: ${outcome}`);
        if (examples.length < 20 && outcome !== "stopsAlone") examples.push(describe);
      }
      if ([fromTlc, fromNative].every(isFailure)) count("allFail");
      else if (fromTlc === fromNative) count("allAnswer");
    }
    // A sample of the cases, each shape once, where both agree.
    const shape = tokens.replace(/[is][0-9a-f]+/g, "v").replace(/S\d+/g, "S");
    const answers: [string, string] = [tlcAnswers[index * 2], tlcAnswers[index * 2 + 1]];
    if (
      recordCount !== undefined &&
      recorded.length < Number(recordCount) &&
      !seen.has(shape) &&
      answers.every((answer, order) => isAgreed(answer, nativeAnswers[index * 2 + order]))
    ) {
      seen.add(shape);
      recorded.push({ tokens, answers });
    }
  });
}

console.table(tally);
for (const example of examples) console.log(example);
if (recordCount !== undefined) {
  mkdirSync(RECORD_DIRECTORY, { recursive: true });
  writeFileSync(
    join(RECORD_DIRECTORY, "requests.txt"),
    `${toRequests(recorded.map((item) => item.tokens)).join("\n")}\n`,
  );
  writeFileSync(
    join(RECORD_DIRECTORY, "answers.txt"),
    `${recorded.flatMap((item) => item.answers).join("\n")}\n`,
  );
  console.log(`Froze ${recorded.length} cases in ${RECORD_DIRECTORY}.`);
}
// Where the native engine and TLC both answer, the engine must enumerate as TLC does; it may stop
// where TLC doesn't.
const isExact = Object.keys(tally).every(
  (name) => !name.startsWith("native") || name.endsWith("stopsAlone"),
);
console.log(
  isExact
    ? "The native engine enumerates every set as TLC does where both answer."
    : "The native engine's enumerations differ.",
);
process.exit(isExact ? 0 : 1);
