import { describe, expect, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { check, TlaUnsupportedError } from "../../src";
import { getUnionGrid } from "../union-grid";

interface Report {
  status: string;
  headline?: string;
}

interface Answer extends Report {
  prints: string[];
}

const readFixture = <T>(name: string): Record<string, T> =>
  JSON.parse(readFileSync(join(import.meta.dirname, "../fixtures/union-grid", name), "utf8"));

// TLC's answers, which scripts/record-union-grid.ts records.
const RECORDED = readFixture<Answer>("tlc.json");

// The cells where the native check fails as TLC does but names another comparison, each with the
// native check's report: membership in a set of mixed values names the element's kind where TLC
// names the comparison that normalizing the set fails at, as main did (fallback.md, "Known wrong
// outputs").
const DIFFERENCES = readFixture<Report>("native-differences.json");

// Whether the answer holds, is false, or fails, which a difference of text never changes.
const getVerdict = (report: Report) =>
  report.status === "success"
    ? "holds"
    : report.headline?.startsWith("Assumption ")
      ? "false"
      : `fails: ${report.status}`;

describe("a membership in a union", () => {
  it("covers every cell of the grid with TLC's answer", () => {
    expect(getUnionGrid().map((cell) => cell.id)).toEqual(Object.keys(RECORDED));
  });

  // The native check prints and answers as TLC does, or declines.
  it.each(getUnionGrid().map((cell) => [cell.id, cell.source, cell.config]))(
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
      const recorded = RECORDED[id];
      expect(getVerdict(report)).toBe(getVerdict(recorded));
      expect(prints).toEqual(recorded.prints);
      expect(report).toEqual(
        DIFFERENCES[id] ?? { status: recorded.status, headline: recorded.headline },
      );
    },
  );
});
