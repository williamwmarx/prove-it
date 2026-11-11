import { afterAll, describe, expect, it } from "bun:test";
import { spawnSync } from "node:child_process";
import {
  copyFileSync,
  mkdirSync,
  mkdtempSync,
  realpathSync,
  rmSync,
  symlinkSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";

const CLI = join(import.meta.dirname, "../../src/cli.ts");

// M.class overrides CM with 5 (M.java), which violates Inv.
const CLASS = join(
  import.meta.dirname,
  "../../native/crates/prove-it-cli/tests/resolver-order/M.class",
);

const SPEC =
  "---- MODULE Spec ----\nEXTENDS Naturals, M\nVARIABLE x\nInit == x = CM\nNext == UNCHANGED x\nInv == x = 1\n====\n";
const MODULE = "---- MODULE M ----\nCM == 1\n====\n";
const CONFIG = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
const OVERRIDE =
  "Loading CM operator override from file:{root}/{path} with signature: <Java Method: public static tlc2.value.impl.Value M.CM()>.";
const VIOLATED = "Error: Invariant Inv is violated by the initial state:";
const MISSING_M = [
  "Fatal errors while parsing TLA+ spec in file Spec",
  "Cannot find source file for module M imported in module Spec.",
  "Cannot find source file for module M imported in module Spec.",
  "Error: Parsing or semantic analysis failed.",
];

interface ResolverCase {
  name: string;
  // Each file by its path from the root: a text, M.class, "->" and the path a link leads to, or
  // "/" for a directory.
  files: Record<string, string>;
  args: string[];
  // What TLC at d8fb231 printed for the same files and command line, with the root as {root}:
  // where it found the files and its errors, on stdout and then on stderr, and its exit code
  // last; or undefined where tla-ts declines.
  printed?: string[];
}

const CASES: ResolverCase[] = [
  {
    name: "class-in-working-directory",
    files: { "sub/Spec.tla": SPEC, "sub/Spec.cfg": CONFIG, "sub/M.tla": MODULE, "M.class": "" },
    args: ["tlc2.TLC", "sub/Spec"],
    printed: [
      "Parsing file {root}/sub/Spec.tla",
      "Parsing file {root}/sub/M.tla",
      OVERRIDE.replace("{path}", "M.class"),
      VIOLATED,
      "exit 12",
    ],
  },
  {
    name: "class-on-library-path",
    files: { "Spec.tla": SPEC, "Spec.cfg": CONFIG, "lib/M.tla": MODULE, "lib/M.class": "" },
    args: ["-DTLA-Library=lib", "tlc2.TLC", "Spec"],
    printed: [
      "Parsing file {root}/Spec.tla",
      "Parsing file {root}/lib/M.tla",
      OVERRIDE.replace("{path}", "lib/M.class"),
      VIOLATED,
      "exit 12",
    ],
  },
  {
    name: "class-through-dot",
    files: { "sp/Spec.tla": SPEC, "sp/Spec.cfg": CONFIG, "lib/M.tla": MODULE, "lib/M.class": "" },
    args: ["-DTLA-Library=./lib", "tlc2.TLC", "{root}/sp/Spec.tla"],
    printed: [
      "Parsing file {root}/sp/Spec.tla",
      "Parsing file {root}/lib/M.tla (file:{root}/./lib/M.tla)",
      OVERRIDE.replace("{path}", "lib/M.class"),
      VIOLATED,
      "exit 12",
    ],
  },
  {
    name: "spec-on-library-path",
    files: { "lib/Spec.tla": SPEC, "lib/Spec.cfg": CONFIG, ll: "->lib" },
    args: ["-DTLA-Library=ll", "tlc2.TLC", "Spec"],
    printed: [
      "Parsing file {root}/lib/Spec.tla (file:{root}/ll/Spec.tla)",
      ...MISSING_M,
      "exit 150",
    ],
  },
  {
    name: "spec-through-dot",
    files: { "lib/Spec.tla": SPEC, "lib/Spec.cfg": CONFIG, "lib/M.tla": MODULE },
    args: ["-DTLA-Library=lib/.", "tlc2.TLC", "Spec"],
    printed: [
      "Parsing file {root}/lib/Spec.tla (file:{root}/lib/./Spec.tla)",
      "Parsing file {root}/lib/M.tla (file:{root}/lib/./M.tla)",
      "exit 0",
    ],
  },
  {
    name: "last-library-path",
    files: { "Spec.tla": SPEC, "Spec.cfg": CONFIG, "a/M.tla": MODULE, "b/M.tla": MODULE },
    args: ["-DTLA-Library=a", "-DTLA-Library=b", "tlc2.TLC", "Spec"],
    printed: ["Parsing file {root}/Spec.tla", "Parsing file {root}/b/M.tla", "exit 0"],
  },
  // Java's String.split drops the empty paths at the end, so TLC looks for M beside the spec
  // alone, not in the working directory.
  {
    name: "empty-library-paths",
    files: { "sp/Spec.tla": SPEC, "sp/Spec.cfg": CONFIG, "M.tla": MODULE },
    args: ["-DTLA-Library=:", "tlc2.TLC", "{root}/sp/Spec.tla"],
    printed: ["Parsing file {root}/sp/Spec.tla", ...MISSING_M, "exit 150"],
  },
  // SimpleFilenameToStream looks for a relative spec named with a directory there alone.
  {
    name: "missing-spec-in-directory",
    files: { "sub/Nope.cfg": CONFIG, lib: "/" },
    args: ["-DTLA-Library=lib", "tlc2.TLC", "sub/Nope"],
    printed: [
      "Fatal errors while parsing TLA+ spec in file sub/Nope",
      "Cannot find source file for module sub/Nope",
      "Cannot find source file for module sub/Nope",
      "Error: Parsing or semantic analysis failed.",
      // on stderr
      "File does not exist: {root}/./sub/Nope.tla while looking in these directories: {root}, sub, classpath:/tla2sany/StandardModules, classpath:/",
      "exit 150",
    ],
  },
  // TLC stops at the first M.class it finds, and loads no override from a directory.
  {
    name: "class-directory",
    files: {
      "Spec.tla": SPEC,
      "Spec.cfg": CONFIG,
      "l1/M.tla": MODULE,
      "cd1/M.class": "/",
      "l2/M.class": "",
    },
    args: ["-DTLA-Library=l1:cd1:l2", "tlc2.TLC", "Spec"],
    printed: ["Parsing file {root}/Spec.tla", "Parsing file {root}/l1/M.tla", "exit 0"],
  },
  // The system follows the link before .., as Java does.
  {
    name: "link-then-parent",
    files: {
      "Spec.tla": SPEC,
      "Spec.cfg": CONFIG,
      "other/X/M.tla": MODULE,
      "other/deep": "/",
      dl: "->other/deep",
    },
    args: ["-DTLA-Library=dl/../X", "tlc2.TLC", "Spec"],
    printed: [
      "Parsing file {root}/Spec.tla",
      "Parsing file {root}/other/X/M.tla (file:{root}/dl/../X/M.tla)",
      "exit 0",
    ],
  },
  // A -DTLA-Library without a value sets the library path to the empty one.
  {
    name: "library-path-without-value",
    files: { "Spec.cfg": CONFIG, "L/Spec.tla": SPEC, "L/M.tla": MODULE },
    args: ["-DTLA-Library=L", "-DTLA-Library", "tlc2.TLC", "Spec"],
    printed: [
      "Fatal errors while parsing TLA+ spec in file Spec",
      "Cannot find source file for module Spec",
      "Cannot find source file for module Spec",
      "Error: Parsing or semantic analysis failed.",
      // on stderr
      "File does not exist: {root}/./Spec.tla while looking in these directories: {root}, , classpath:/tla2sany/StandardModules, classpath:/",
      "exit 150",
    ],
  },
  {
    name: "missing-spec-in-doubled-directory",
    files: { "Nope.cfg": CONFIG },
    args: ["tlc2.TLC", ".//Nope"],
    printed: [
      "Fatal errors while parsing TLA+ spec in file .//Nope",
      "Cannot find source file for module .//Nope",
      "Cannot find source file for module .//Nope",
      "Error: Parsing or semantic analysis failed.",
      // on stderr
      "File does not exist: {root}/././Nope.tla while looking in these directories: {root}, ., classpath:/tla2sany/StandardModules, classpath:/",
      "exit 150",
    ],
  },
  // TLC reads anything there but a directory, such as /dev/null.
  {
    name: "module-device",
    files: { "Spec.tla": SPEC, "Spec.cfg": CONFIG, "M.tla": "->/dev/null" },
    args: ["tlc2.TLC", "Spec"],
    printed: [
      "Parsing file {root}/Spec.tla",
      "Parsing file /dev/null (file:{root}/M.tla)",
      "Fatal errors while parsing TLA+ spec in file Spec",
      "Error: Parsing or semantic analysis failed.",
      "exit 150",
    ],
  },
  // A path the system can't follow, as a link to itself, isn't there.
  {
    name: "configuration-loop",
    files: { "Spec.tla": SPEC, "M.tla": MODULE, "Spec.cfg": "->Spec.cfg" },
    args: ["tlc2.TLC", "Spec"],
    printed: [
      "Error: TLC encountered the following error when trying to read the configuration file Spec.cfg:",
      "exit 151",
    ],
  },
  // TLC finds the configuration on the library path, then can't read the spec, which tla-ts
  // doesn't report as TLC does.
  {
    name: "spec-directory-with-library-configuration",
    files: { "Spec.tla": "/", "lib/Spec.cfg": CONFIG },
    args: ["-DTLA-Library=lib", "tlc2.TLC", "Spec"],
  },
  // MonolithSpecExtractor.getConfig: TLC reads a -config x as x.cfg.
  {
    name: "configuration-without-extension",
    files: { "Spec.tla": SPEC, "M.tla": MODULE, "x.cfg": CONFIG },
    args: ["tlc2.TLC", "-config", "x", "Spec"],
    printed: ["Parsing file {root}/Spec.tla", "Parsing file {root}/M.tla", "exit 0"],
  },
  {
    name: "configuration-directory-without-extension",
    files: { "Spec.tla": SPEC, "M.tla": MODULE, "d.cfg": "/" },
    args: ["tlc2.TLC", "-config", "d", "Spec"],
  },
  // TLC drops a -config's .cfg and reads X.tla's CONFIG section, which tla-ts doesn't, or names
  // the file it doesn't find.
  {
    name: "missing-module-configuration",
    files: { "Spec.tla": SPEC, "M.tla": MODULE },
    args: ["tlc2.TLC", "-config", "Nope.tla", "Spec"],
    printed: [
      "Error: TLC encountered the following error when trying to read the configuration file Nope.tla:",
      "exit 151",
    ],
  },
  {
    name: "configuration-named-extension",
    files: { "Spec.tla": SPEC, "M.tla": MODULE, ".cfg": CONFIG },
    args: ["tlc2.TLC", "-config", ".cfg", "Spec"],
    printed: ["Parsing file {root}/Spec.tla", "Parsing file {root}/M.tla", "exit 0"],
  },
  {
    name: "module-configuration",
    files: { "Spec.tla": SPEC, "M.tla": MODULE, "Spec.tla.cfg": CONFIG },
    args: ["tlc2.TLC", "-config", "Spec.tla.cfg", "Spec"],
  },
  // TLC reads the configuration before the spec.
  {
    name: "spec-directory-without-configuration",
    files: { "D.tla": "/" },
    args: ["tlc2.TLC", "D"],
    printed: [
      "Error: TLC encountered the following error when trying to read the configuration file D.cfg:",
      "exit 151",
    ],
  },
  // TLC prints `***Internal error: Unable to create FileInputStream` as it fails to read the
  // directory, which tla-ts doesn't.
  {
    name: "configuration-directory",
    files: { "Spec.tla": SPEC, "M.tla": MODULE, "C.cfg": "/" },
    args: ["tlc2.TLC", "-config", "C.cfg", "Spec"],
  },
  // TLC prints `***Internal error: Unable to create NamedInputStream in toIStream method` as it
  // fails to read the directory, which tla-ts doesn't.
  {
    name: "module-directory",
    files: { "Spec.tla": SPEC, "Spec.cfg": CONFIG, "M.tla": "/" },
    args: ["tlc2.TLC", "Spec"],
  },
  {
    name: "spec-directory",
    files: { "Spec.tla": "/", "Spec.cfg": CONFIG },
    args: ["tlc2.TLC", "Spec"],
  },
];

const PREFIXES = [
  "Parsing file ",
  "Loading ",
  "Fatal errors",
  "File does not exist",
  "Cannot find",
  "Error:",
];

const temporary = realpathSync(mkdtempSync(join(tmpdir(), "prove-it-resolver-order-")));

afterAll(() => rmSync(temporary, { recursive: true, force: true }));

const setUp = (root: string, files: Record<string, string>) =>
  Object.entries(files).forEach(([path, contents]) => {
    const target = join(root, path);
    mkdirSync(dirname(target), { recursive: true });
    if (contents === "/") return mkdirSync(target, { recursive: true });
    if (path.endsWith(".class")) return copyFileSync(CLASS, target);
    if (contents.startsWith("->")) return symlinkSync(contents.slice(2), target);
    writeFileSync(target, contents);
  });

describe.each(["native", "TypeScript"])("the %s check", (check) => {
  it.each(CASES)("finds the files of $name as TLC does", (resolverCase) => {
    const root = join(temporary, `${check}-${resolverCase.name}`);
    setUp(root, resolverCase.files);
    const args = resolverCase.args.flatMap((arg) =>
      arg === "tlc2.TLC" ? [arg, "-noGenerateSpecTE"] : [arg.replace("{root}", root)],
    );
    const result = spawnSync("bun", [CLI, ...args], {
      cwd: root,
      encoding: "utf8",
      env: { ...process.env, ...(check === "TypeScript" && { PROVE_IT_ENGINE: "0" }) },
    });
    const text = `${result.stdout}${result.stderr}`;
    if (resolverCase.printed === undefined) {
      expect(text).toMatch(/prove-it: not native yet: |TlaUnsupportedError: /);
      return;
    }
    const printed = text
      .split("\n")
      .filter((line) => PREFIXES.some((prefix) => line.startsWith(prefix)))
      .filter((line) => !line.includes("/tlc-"));
    expect([...printed, `exit ${result.status}`]).toEqual(
      resolverCase.printed.map((line) => line.replaceAll("{root}", root)),
    );
  });

  // TLC at d8fb231 says which version it is, then that it has no spec, on stdout alone, once it has
  // read every option, which the TypeScript check doesn't, so it declines.
  it.each([
    [
      [],
      "TLC2 Version _\nError: Error: Missing input TLA+ module.\nUsage: java tlc2.TLC [-help] [-option] inputfile\n",
    ],
    [
      ["-tool"],
      "@!@!@STARTMSG 2262:0 @!@!@\nTLC2 Version _\n@!@!@ENDMSG 2262 @!@!@\n@!@!@STARTMSG 1102:1 @!@!@\nError: Missing input TLA+ module.\nUsage: java tlc2.TLC [-help] [-option] inputfile\n@!@!@ENDMSG 1102 @!@!@\n",
    ],
  ])("reports a TLC command line %p without a spec as TLC does", (options, printed) => {
    const result = spawnSync("bun", [CLI, "tlc2.TLC", ...options], {
      cwd: temporary,
      encoding: "utf8",
      env: { ...process.env, ...(check === "TypeScript" && { PROVE_IT_ENGINE: "0" }) },
    });
    if (check === "TypeScript") {
      expect(result.stderr).toStartWith("TlaUnsupportedError: ");
      return;
    }
    expect(result.stdout.replace(/^TLC2 Version .*$/m, "TLC2 Version _")).toBe(printed);
    expect(result.stderr).toBe("");
    expect(result.status).toBe(1);
  });
});
