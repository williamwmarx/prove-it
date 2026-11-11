import { afterAll, afterEach, describe, expect, it } from "bun:test";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { parseModule } from "../../src";
import { getNativeSanyReport } from "../../src/cli/sany-text";
import { parseConfig } from "../../src/config";
import { createEnvironment } from "../../src/environment";
import { checkParsed } from "../../src/parallel";
import { createTlcOrder } from "../../src/tlc/order";

const directories: string[] = [];
const setting = process.env.PROVE_IT_ENGINE;

afterAll(() => directories.forEach((directory) => rmSync(directory, { recursive: true })));

afterEach(() => {
  if (setting === undefined) delete process.env.PROVE_IT_ENGINE;
  else process.env.PROVE_IT_ENGINE = setting;
});

// Writes each module to its own file, then reports on the first one, as TLC runs SANY.
const getReport = (modules: Record<string, string>) => {
  const directory = mkdtempSync(join(tmpdir(), "sany-readings-"));
  directories.push(directory);
  Object.entries(modules).forEach(([name, source]) =>
    writeFileSync(join(directory, `${name}.tla`), source),
  );
  const loadModule = (name: string) =>
    name in modules ? readFileSync(join(directory, `${name}.tla`), "utf8") : undefined;
  const root = Object.keys(modules)[0];
  const report = getNativeSanyReport(join(directory, `${root}.tla`), modules[root], "master", {
    fileName: root,
    loadModule,
    describeFile: () => "",
    rootExtendees: [],
  });
  if ("declined" in report) throw new Error(`tla-front declined: ${report.declined}`);
  return { report, loadModule };
};

const LEAF = "---- MODULE Leaf ----\nEXTENDS Naturals\nCONSTANT N\nDouble(n) == 2 * n\n====\n";

const COUNTER = `---- MODULE Counter ----
EXTENDS Leaf, TLC
VARIABLE x
---- MODULE Inner ----
VARIABLE y
Step == y' = y + 1
====
I == INSTANCE Inner WITH y <- x
Init == x = 0
Next == x < Double(N) /\\ I!Step
Inv == x < 5
====
`;

// SANY's parser reads []ASSUME as ASSUME once it takes out the box, which TLC's order can't.
const BOXED = `---- MODULE Boxed ----
VARIABLE x
THEOREM T == TRUE
<1>1 []ASSUME TRUE []PROVE TRUE
<1> QED
Init == x = 0
Next == x' = x
====
`;

describe("SANY's readings", () => {
  it("hold the module SANY's parser read from each text", () => {
    const sany = getReport({ Counter: COUNTER, Leaf: LEAF });
    expect(sany.report.isFailed).toBe(false);
    expect(sany.report.readings.get(COUNTER)?.module).toEqual(parseModule(COUNTER));
    expect(sany.report.readings.get(LEAF)?.module).toEqual(parseModule(LEAF));
  });

  it("give TLC's order the module SANY read", () => {
    const sany = getReport({ Counter: COUNTER, Leaf: LEAF });
    const order = createTlcOrder(COUNTER, sany.loadModule, sany.report.readings);
    expect(sany.report.readings.get(COUNTER)?.module).toBe(order.parseModule(COUNTER));
  });

  it("leave TLC's order to parse a text SANY read without its boxes", () => {
    const sany = getReport({ Boxed: BOXED });
    expect(sany.report.isFailed).toBe(false);
    const order = createTlcOrder(BOXED, sany.loadModule, sany.report.readings);
    expect(() => order.parseModule(BOXED)).toThrow('Unexpected "ASSUME" at line 4, column 8');
  });

  it("check a spec as its source does", async () => {
    const sany = getReport({ Counter: COUNTER, Leaf: LEAF });
    const getResult = async (isRead: boolean) => {
      const lines: string[] = [];
      const options = {
        source: COUNTER,
        config: "CONSTANT N = 3\nINIT Init\nNEXT Next\nINVARIANT Inv",
        loadModule: sany.loadModule,
        onPrint: (text: string) => lines.push(text),
        isSanyReported: true,
      };
      const result = isRead
        ? await checkParsed(options, sany.report.readings)
        : await checkParsed(options);
      return { result, lines };
    };
    const expected = await getResult(false);
    expect(expected.result.status).toBe("invariant-violation");
    expect(await getResult(true)).toEqual(expected);
    process.env.PROVE_IT_ENGINE = "0";
    expect(await getResult(true)).toEqual(expected);
  });
});

describe("the environment of a spec SANY accepted", () => {
  // SANY rejects the spec, so the environment's level check is all that would.
  const source = "---- MODULE M ----\nVARIABLE x\nF == [](x')\n====\n";
  const createSpecification = (isSanyAccepted: boolean) =>
    createEnvironment(parseConfig(""), {
      source,
      loadModule: undefined,
      print: () => {},
      files: { readFile: undefined, writeFile: undefined },
      isUnconfigured: true,
      isSanyAccepted,
    });

  it("leaves out SANY's level checks", () => {
    expect(() => createSpecification(false)).toThrow("[] followed by action not of form [A]_v");
    expect(() => createSpecification(true)).not.toThrow();
  });
});
