import { afterAll, describe, expect, it } from "bun:test";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { parseModule } from "../../src";
import { getSanyReport, type SanyReportOptions } from "../../src/sany/report";

const directories: string[] = [];

afterAll(() => directories.forEach((directory) => rmSync(directory, { recursive: true })));

// Writes each module to its own file, then reports on the first one, as TLC runs SANY.
const getReport = (modules: Record<string, string>, options?: SanyReportOptions) => {
  const directory = mkdtempSync(join(tmpdir(), "sany-readings-"));
  directories.push(directory);
  Object.entries(modules).forEach(([name, source]) =>
    writeFileSync(join(directory, `${name}.tla`), source),
  );
  const loadModule = (name: string) =>
    name in modules ? readFileSync(join(directory, `${name}.tla`), "utf8") : undefined;
  const root = Object.keys(modules)[0];
  const report = getSanyReport(join(directory, `${root}.tla`), loadModule, options);
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

describe("SANY's readings", () => {
  it("hold the module SANY's parser read from each text", () => {
    const sany = getReport({ Counter: COUNTER, Leaf: LEAF });
    expect(sany.report.isFailed).toBe(false);
    expect(sany.report.readings.get(COUNTER)?.module).toEqual(parseModule(COUNTER));
    expect(sany.report.readings.get(LEAF)?.module).toEqual(parseModule(LEAF));
  });

  // XMLExporter's SANY validates no PlusCal, so only the generator reads the modules.
  it("hold what the generator read", () => {
    const sany = getReport({ Counter: COUNTER, Leaf: LEAF }, { isXmlExport: true });
    expect(sany.report.readings.get(COUNTER)?.module).toEqual(parseModule(COUNTER));
    expect(sany.report.readings.get(LEAF)?.module).toEqual(parseModule(LEAF));
  });
});
