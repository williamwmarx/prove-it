import { describe, expect, it } from "bun:test";
import { spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, realpathSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const CLI = join(import.meta.dirname, "../../src/cli.ts");
const BUILT_CLI = join(import.meta.dirname, "../../dist/cli.js");
const WASM = process.env.PROVE_IT_ENGINE_WASM;

const useDirectory = (prefix: string, test: (directory: string) => void) => {
  const directory = realpathSync(mkdtempSync(join(tmpdir(), prefix)));
  try {
    test(directory);
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
};

// TLC reads a module's text not in UTF-8, as here bytes in a comment, and so does the CLI, with
// readFileSync's UTF-8 as it did, though the binary declines it.
describe("a module not in UTF-8", () => {
  it.each([
    [["-noGenerateSpecTE", "M"], "2 states generated, 1 distinct states found, 0 states left"],
    [["-noGenerateSpecTE", "-dump", "states", "M"], "1 distinct states found"],
    [["tla2sany.xml.XMLExporter", "-o", "M.tla"], "<filename>B</filename>"],
  ])("is read with %p", (args, printed) =>
    useDirectory("prove-it-not-utf8-", (directory) => {
      writeFileSync(
        join(directory, "M.tla"),
        "---- MODULE M ----\nEXTENDS B\nVARIABLE x\nInit == x = 0\nNext == x' = x\n====\n",
      );
      writeFileSync(join(directory, "M.cfg"), "INIT Init\nNEXT Next\n");
      writeFileSync(
        join(directory, "B.tla"),
        Buffer.concat([
          Buffer.from("---- MODULE B ----\n\\* "),
          Buffer.from([0xff, 0xfe]),
          Buffer.from("\n====\n"),
        ]),
      );
      const run = spawnSync("bun", [CLI, ...args], { cwd: directory, encoding: "utf8" });
      expect({ status: run.status, stderr: run.stderr }).toEqual({ status: 0, stderr: "" });
      expect(run.stdout).toContain(printed);
    }),
  );
});

// TLC finds the spec and its modules by the absolute paths it was given, which Rust's std doesn't
// take for absolute on wasm32-unknown-unknown.
describe("absolute paths", () => {
  const checkAbsolute = (runtime: string, cli: string, env: Record<string, string | undefined>) =>
    useDirectory("prove-it-absolute-", (directory) => {
      mkdirSync(join(directory, "spec"));
      mkdirSync(join(directory, "lib"));
      mkdirSync(join(directory, "work"));
      writeFileSync(
        join(directory, "spec", "Spec.tla"),
        "---- MODULE Spec ----\nEXTENDS L\nVARIABLE x\nInit == x = C\nNext == x' = x\n====\n",
      );
      writeFileSync(join(directory, "spec", "Spec.cfg"), "INIT Init\nNEXT Next\n");
      writeFileSync(join(directory, "lib", "L.tla"), "---- MODULE L ----\nC == 1\n====\n");
      const run = spawnSync(
        runtime,
        [
          cli,
          `-DTLA-Library=${join(directory, "lib")}`,
          "tlc2.TLC",
          "-noGenerateSpecTE",
          join(directory, "spec", "Spec"),
        ],
        { cwd: join(directory, "work"), encoding: "utf8", env: { ...process.env, ...env } },
      );
      // The status with what the run wrote to stderr, which PROVE_IT_ENGINE=debug writes to.
      expect({ status: run.status, stderr: run.stderr }).toMatchObject({ status: 0 });
      expect(run.stdout).toContain(
        `Parsing file ${join(directory, "spec", "Spec.tla")}\nParsing file ${join(directory, "lib", "L.tla")}\n`,
      );
      expect(run.stdout).toContain("1 distinct states found");
    });

  it.each(["debug", "0"])("are found with the addon, with PROVE_IT_ENGINE=%s", (setting) =>
    checkAbsolute("bun", CLI, { PROVE_IT_ENGINE: setting }),
  );

  it.if(WASM !== undefined).each(["debug", "0"])(
    "are found with the engine as WebAssembly, with PROVE_IT_ENGINE=%s",
    (setting) =>
      checkAbsolute("node", BUILT_CLI, {
        PROVE_IT_ENGINE: setting,
        PROVE_IT_ENGINE_ADDON: undefined,
        PROVE_IT_ENGINE_WASM: WASM,
      }),
  );
});

// SimpleFilenameToStream lists the working directory, then each -I directory, of which there are
// none here, so an empty one.
it("XMLExporter names where it looked for a root module it doesn't find", () =>
  useDirectory("prove-it-xml-missing-", (directory) => {
    const run = spawnSync("bun", [CLI, "tla2sany.xml.XMLExporter", "-o", "Nope"], {
      cwd: directory,
      encoding: "utf8",
    });
    expect(run.status).toBe(2);
    expect(run.stderr).toStartWith(
      `File does not exist: ${directory}/./Nope.tla while looking in these directories: ${directory}, , classpath:/tla2sany/StandardModules, classpath:/\n`,
    );
  }));

// TLC checks the config -config names, where the binary's parser declines another option on the
// command line and the TypeScript check takes it: here TLC reports Other.cfg's invariant violated.
it("finds the config -config names beside an option the binary declines", () =>
  useDirectory("prove-it-config-option-", (directory) => {
    writeFileSync(
      join(directory, "Spec.tla"),
      "---- MODULE Spec ----\nVARIABLE x\nInit == x = 0\nNext == x' = x\nInv == x = 1\n====\n",
    );
    writeFileSync(join(directory, "Spec.cfg"), "INIT Init\nNEXT Next\n");
    writeFileSync(join(directory, "Other.cfg"), "INIT Init\nNEXT Next\nINVARIANT Inv\n");
    const run = spawnSync(
      "bun",
      [CLI, "-noGenerateSpecTE", "-lncheck", "off", "-config", "Other.cfg", "Spec"],
      { cwd: directory, encoding: "utf8" },
    );
    expect(run.status).toBe(12);
    expect(run.stdout).toContain("Error: Invariant Inv is violated by the initial state:");
  }));

// A property of TLC's that SANY doesn't read leaves XMLExporter's XML as it is.
it("XMLExporter exports with a system property of TLC's that SANY doesn't read", () =>
  useDirectory("prove-it-xml-property-", (directory) => {
    writeFileSync(join(directory, "M.tla"), "---- MODULE M ----\nC == 1\n====\n");
    const run = spawnSync("bun", [CLI, "-Dtlc2.foo=1", "tla2sany.xml.XMLExporter", "-o", "M.tla"], {
      cwd: directory,
      encoding: "utf8",
    });
    expect({ status: run.status, stderr: run.stderr }).toEqual({ status: 0, stderr: "" });
    expect(run.stdout).toContain("<uniquename>C</uniquename>");
  }));

// TLC rejects -config without a file name where it reads it among the other options, which the
// TypeScript check doesn't order as TLC does, so it declines rather than check another config.
it("declines -config without a value beside an option the binary declines", () =>
  useDirectory("prove-it-config-missing-", (directory) => {
    writeFileSync(
      join(directory, "Spec.tla"),
      "---- MODULE Spec ----\nVARIABLE x\nInit == x = 0\nNext == x' = x\n====\n",
    );
    writeFileSync(join(directory, "Spec.cfg"), "INIT Init\nNEXT Next\nVIEW x\n");
    const run = spawnSync("bun", [CLI, "Spec", "-view", "-config"], {
      cwd: directory,
      encoding: "utf8",
    });
    expect(run.status).toBe(255);
    expect(run.stderr).toContain("TlaUnsupportedError: -config without a value");
    expect(run.stdout).not.toContain("Model checking completed");
  }));
