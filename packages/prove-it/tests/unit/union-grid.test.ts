import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { check, TlaUnsupportedError } from "../../src";
import { getReductionGrid, getUnionGrid, type GridCell } from "../union-grid";

interface Report {
  status: string;
  headline?: string;
}

interface Answer extends Report {
  prints: string[];
}

const readFixture = <T>(name: string): Record<string, T> =>
  JSON.parse(readFileSync(join(import.meta.dirname, "../fixtures/union-grid", name), "utf8"));

// Whether the answer holds, is false, or fails, which a difference of text never changes.
const getVerdict = (report: Report) =>
  report.status === "success"
    ? "holds"
    : report.headline?.startsWith("Assumption ")
      ? "false"
      : `fails: ${report.status}`;

// Checks each cell of a grid against TLC's answers, which scripts/record-union-grid.ts records in
// `recordedName`. `differencesName` holds the cells where the native check fails as TLC does but
// names another comparison, each with the native check's report: membership in a set of mixed
// values names the element's kind where TLC names the comparison that normalizing the set fails
// at, as main did (fallback.md, "Known wrong outputs").
const describeGrid = (
  name: string,
  cells: GridCell[],
  recordedName: string,
  differencesName: string,
) => {
  const recordedAnswers = readFixture<Answer>(recordedName);
  const differences = readFixture<Report>(differencesName);
  describe(name, () => {
    it("covers every cell of the grid with TLC's answer", () => {
      expect(cells.map((cell) => cell.id)).toEqual(Object.keys(recordedAnswers));
    });

    // The native check prints and answers as TLC does, or declines.
    it.each(cells.map((cell) => [cell.id, cell.source, cell.config]))(
      "answers %s as TLC does",
      async (id, source, config) => {
        const prints: string[] = [];
        const report = await check({
          source,
          config,
          onPrint: (text) => prints.push(...text.split("\n")),
        }).then(
          (result): Report | undefined => ({
            status: result.status,
            headline: result.violations[0]?.headline,
          }),
          (error: unknown) => {
            if (error instanceof TlaUnsupportedError) return undefined;
            throw error;
          },
        );
        if (report === undefined) return;
        const recorded = recordedAnswers[id];
        expect(getVerdict(report)).toBe(getVerdict(recorded));
        expect(prints).toEqual(recorded.prints);
        expect(report).toEqual(
          differences[id] ?? { status: recorded.status, headline: recorded.headline },
        );
      },
    );
  });
};

describeGrid("a membership in a union", getUnionGrid(), "tlc.json", "native-differences.json");
describeGrid(
  "a membership in a set operation TLC reduces",
  getReductionGrid(),
  "reductions.json",
  "reduction-differences.json",
);
