// Writes the standard modules the TypeScript front end holds as strings, for each TLC version, to
// native/crates/tla-front/modules as .tla files, and the Rust index that compiles them into the
// crate, so the Rust front end reads the same texts. With --check, it writes nothing and fails if
// a file differs, as Verification runs it.
// Usage: bun scripts/front-modules.ts [--check]

import { existsSync, mkdirSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { join, relative } from "node:path";

import { BUNDLED_MODULES } from "../src/bundled-modules";
import { SANY_174_STANDARD_MODULES, SANY_STANDARD_MODULES } from "../src/sany/modules";

const CRATE_DIRECTORY = join(import.meta.dirname, "../native/crates/tla-front");
const MODULES_DIRECTORY = join(CRATE_DIRECTORY, "modules");
const INDEX_PATH = join(CRATE_DIRECTORY, "src/standard_modules.rs");

const SETS = [
  { directory: "master", constant: "MASTER", modules: SANY_STANDARD_MODULES },
  { directory: "1.7.4", constant: "TLC_174", modules: SANY_174_STANDARD_MODULES },
  { directory: "bundled", constant: "BUNDLED", modules: BUNDLED_MODULES },
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
  console.log(`${files.size - 1} standard modules are up to date`);
} else {
  rmSync(MODULES_DIRECTORY, { recursive: true, force: true });
  files.forEach((text, path) => {
    mkdirSync(join(path, ".."), { recursive: true });
    writeFileSync(path, text);
  });
  console.log(`wrote ${files.size - 1} standard modules`);
}
