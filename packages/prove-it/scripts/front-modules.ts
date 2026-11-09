// Writes the standard modules the TypeScript front end holds as strings, for each TLC version, to
// native/crates/tla-front/modules as .tla files, and the Rust index that compiles them into the
// crate, so the Rust front end reads the same texts. It also writes the operators that tla-ts
// implements natively for the standard modules, as getStandardModule and CORE_OPERATORS give them,
// to src/standard_builtins.rs, and the texts SANY and TLC intern, with TLC's own module sources, to
// src/tlc_data.rs. With --check, it writes nothing and fails if a file differs, as
// Verification runs it.
// Usage: bun scripts/front-modules.ts [--check]

import { existsSync, mkdirSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { join, relative } from "node:path";

import { BUNDLED_MODULES } from "../src/bundled-modules";
import type { Builtin } from "../src/evaluate";
import { createRuntime } from "../src/runtime";
import { SANY_174_STANDARD_MODULES, SANY_STANDARD_MODULES } from "../src/sany/modules";
import { getStandardRange, STANDARD_LEVELS } from "../src/standard-definitions";
import { CORE_OPERATORS, getStandardModule, STANDARD_DEPENDENCIES } from "../src/standard-modules";
import {
  SANY_BUILTINS,
  SANY_NODE_NAMES,
  SANY_OPERATOR_SYNONYMS,
  TLC_MODULE_SOURCES,
  TLC_RUNTIME_STRINGS,
  TLC_STARTUP_STRINGS,
  USER_STANDARD_MODULES,
} from "../src/tlc/jar-data";
import type { TlcVersion } from "../src/tlc/version";

const CRATE_DIRECTORY = join(import.meta.dirname, "../native/crates/tla-front");
const MODULES_DIRECTORY = join(CRATE_DIRECTORY, "modules");
const INDEX_PATH = join(CRATE_DIRECTORY, "src/standard_modules.rs");
const BUILTINS_PATH = join(CRATE_DIRECTORY, "src/standard_builtins.rs");
const TLC_DATA_PATH = join(CRATE_DIRECTORY, "src/tlc_data.rs");

const SETS = [
  { directory: "master", constant: "MASTER", modules: SANY_STANDARD_MODULES },
  { directory: "1.7.4", constant: "TLC_174", modules: SANY_174_STANDARD_MODULES },
  { directory: "bundled", constant: "BUNDLED", modules: BUNDLED_MODULES },
  { directory: "tlc", constant: "TLC_SOURCES", modules: TLC_MODULE_SOURCES },
];

const files = new Map<string, string>(
  SETS.flatMap((set) =>
    [...set.modules].map(([name, text]): [string, string] => [
      join(MODULES_DIRECTORY, set.directory, `${name}.tla`),
      text,
    ]),
  ),
);
files.set(
  INDEX_PATH,
  [
    "//! The standard modules of SANY for each TLC version, and the modules TLC bundles, as",
    "//! `src/sany/modules.ts` and `src/bundled-modules.ts` hold them. `scripts/front-modules.ts`",
    "//! writes this file and the texts it includes; don't edit them by hand.",
    "",
    "macro_rules! module {",
    "    ($directory:literal, $name:literal) => {",
    "        (",
    "            $name,",
    '            include_str!(concat!("../modules/", $directory, "/", $name, ".tla")),',
    "        )",
    "    };",
    "}",
    "",
    ...SETS.flatMap((set) => [
      `pub const ${set.constant}: &[(&str, &str)] = &[`,
      ...[...set.modules.keys()].map((name) => `    module!("${set.directory}", "${name}"),`),
      "];",
      "",
    ]),
  ].join("\n"),
);

const getFlags = (builtin: Builtin) =>
  (builtin.isStateLevel ? 1 : 0) |
  (builtin.isLevelConstant ? 2 : 0) |
  (builtin.isLazy ? 4 : 0) |
  (builtin.isNaturalsGeq ? 16 : 0);

const writeRange = (range: ReturnType<typeof getStandardRange>) =>
  range
    ? `Some([${range.start.line}, ${range.start.column}, ${range.end.line}, ${range.end.column}])`
    : "None";

const writeStandardModules = (version: TlcVersion) => {
  const runtime = createRuntime(true, undefined);
  runtime.version = version;
  const files = { readFile: () => undefined, writeFile: () => {} };
  return [...STANDARD_DEPENDENCIES.keys(), "Naturals"]
    .filter((name, index, names) => names.indexOf(name) === index)
    .toSorted()
    .flatMap((name) => {
      const module = getStandardModule(name, () => {}, runtime, files, new Map());
      if (!module) return [];
      return [
        "    StandardModule {",
        `        name: ${JSON.stringify(name)},`,
        `        extends: &[${module.extends.map((extended) => JSON.stringify(extended)).join(", ")}],`,
        "        operators: &[",
        ...module.operators.map((operator) => {
          const params = STANDARD_LEVELS.get(operator.name)?.formals.map((formal) => formal.arity);
          return `            StandardOperator { name: ${JSON.stringify(operator.name)}, arity: ${operator.arity}, flags: ${getFlags(operator)}, params: ${params ? `Some(&[${params.join(", ")}])` : "None"}, range: ${writeRange(getStandardRange(name, operator.name))} },`;
        }),
        "        ],",
        "    },",
      ];
    });
};

files.set(
  BUILTINS_PATH,
  [
    "//! The operators that tla-ts implements natively, as `CORE_OPERATORS` and `getStandardModule` in",
    "//! `src/standard-modules.ts` give them for each TLC version, with the arities of their",
    "//! parameters and their ranges from `src/standard-definitions.ts`. `scripts/front-modules.ts`",
    "//! writes this file; don't edit it by hand.",
    "",
    "/// A builtin's flags: state-level, level-constant, lazy, Naturals' >=, as the IR writes them.",
    "pub struct StandardOperator {",
    "    pub name: &'static str,",
    "    pub arity: usize,",
    "    pub flags: u32,",
    "    pub params: Option<&'static [usize]>,",
    "    pub range: Option<[u32; 4]>,",
    "}",
    "",
    "pub struct StandardModule {",
    "    pub name: &'static str,",
    "    pub extends: &'static [&'static str],",
    "    pub operators: &'static [StandardOperator],",
    "}",
    "",
    "pub const CORE_OPERATORS: &[(&str, usize, u32)] = &[",
    ...CORE_OPERATORS.map(
      (operator) =>
        `    (${JSON.stringify(operator.name)}, ${operator.arity}, ${getFlags(operator)}),`,
    ),
    "];",
    "",
    "pub const STANDARD_DEPENDENCIES: &[(&str, &[&str])] = &[",
    ...[...STANDARD_DEPENDENCIES].map(
      ([name, dependencies]) =>
        `    (${JSON.stringify(name)}, &[${dependencies.map((dependency) => JSON.stringify(dependency)).join(", ")}]),`,
    ),
    "];",
    "",
    `pub const USER_STANDARD_MODULES: &[&str] = &[${[...USER_STANDARD_MODULES].map((name) => JSON.stringify(name)).join(", ")}];`,
    "",
    "pub const MASTER: &[StandardModule] = &[",
    ...writeStandardModules("master"),
    "];",
    "",
    "pub const TLC_174: &[StandardModule] = &[",
    ...writeStandardModules("1.7.4"),
    "];",
    "",
  ].join("\n"),
);

const writeTexts = (texts: readonly string[]) =>
  texts.map((text) => `    ${JSON.stringify(text)},`);

files.set(
  TLC_DATA_PATH,
  [
    "//! The texts SANY and TLC intern, as `src/tlc/jar-data.ts` holds them, which TLC's string order",
    "//! reads. `scripts/front-modules.ts` writes this file; don't edit it by hand.",
    "",
    "pub const SANY_BUILTINS: &[&str] = &[",
    ...writeTexts(SANY_BUILTINS),
    "];",
    "",
    "pub const SANY_NODE_NAMES: &[&str] = &[",
    ...writeTexts(SANY_NODE_NAMES),
    "];",
    "",
    "pub const SANY_OPERATOR_SYNONYMS: &[&[&str]] = &[",
    ...SANY_OPERATOR_SYNONYMS.map(
      (synonyms) => `    &[${synonyms.map((name) => JSON.stringify(name)).join(", ")}],`,
    ),
    "];",
    "",
    "pub const TLC_STARTUP_STRINGS: &[&str] = &[",
    ...writeTexts(TLC_STARTUP_STRINGS),
    "];",
    "",
    "pub const TLC_RUNTIME_STRINGS: &[&str] = &[",
    ...writeTexts(TLC_RUNTIME_STRINGS),
    "];",
    "",
  ].join("\n"),
);

const written = existsSync(MODULES_DIRECTORY)
  ? readdirSync(MODULES_DIRECTORY, { recursive: true, encoding: "utf8" })
      .map((path) => join(MODULES_DIRECTORY, path))
      .filter((path) => path.endsWith(".tla"))
  : [];
const stale = [
  ...[...files].filter(([path, text]) => !existsSync(path) || readFileSync(path, "utf8") !== text),
  ...written.filter((path) => !files.has(path)).map((path): [string, string] => [path, ""]),
];

if (process.argv.includes("--check")) {
  stale.forEach(([path]) => console.log(`out of date: ${relative(CRATE_DIRECTORY, path)}`));
  if (stale.length > 0) {
    console.log("Run bun scripts/front-modules.ts to write the standard modules again.");
    process.exit(1);
  }
  console.log(`${files.size - 3} standard modules, their builtins and TLC's texts are up to date`);
} else {
  rmSync(MODULES_DIRECTORY, { recursive: true, force: true });
  files.forEach((text, path) => {
    mkdirSync(join(path, ".."), { recursive: true });
    writeFileSync(path, text);
  });
  console.log(`wrote ${files.size - 3} standard modules, their builtins and TLC's texts`);
}
