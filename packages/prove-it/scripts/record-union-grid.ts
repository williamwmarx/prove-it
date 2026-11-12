// Records TLC's answer to each cell of tests/union-grid.ts in tests/fixtures/union-grid/tlc.json:
// what the assumptions print, then the error TLC reports as it checks them, or success.
//
// Usage: TLA2TOOLS_JAR=path bun scripts/run.ts record-union-grid

import { execFile } from "node:child_process";
import { existsSync, mkdirSync, mkdtempSync, writeFileSync } from "node:fs";
import { availableParallelism, tmpdir } from "node:os";
import { join } from "node:path";
import { promisify } from "node:util";

import { getUnionGrid } from "../tests/union-grid";

export interface RecordedAnswer {
  status: string;
  headline?: string;
  prints: string[];
}

const jarPath = process.env.TLA2TOOLS_JAR;
if (!jarPath || !existsSync(jarPath)) {
  console.error("Set TLA2TOOLS_JAR to the path of tla2tools.jar");
  process.exit(1);
}

const run = promisify(execFile);

// TLC's output between "Starting..." and "Finished in": the lines the assumptions print, then an
// error's text, as the library's headline holds it, or success.
const getAnswer = (output: string): RecordedAnswer => {
  const lines = output.split("\n");
  const start = lines.findIndex((line) => line.startsWith("Starting..."));
  const end = lines.findIndex((line, index) => index > start && line.startsWith("Finished in"));
  const after = lines.slice(start + 1, end);
  const reported = after.findIndex(
    (line) => line.startsWith("Error: ") || line === "Computing initial states...",
  );
  const printed = reported === -1 ? after.length : reported;
  const prints = after.slice(0, printed);
  const report = after.slice(printed);
  if (report[0]?.startsWith("Error: ")) {
    return {
      status: "assumption-violation",
      headline: [report[0].slice("Error: ".length), ...report.slice(1)].join("\n"),
      prints,
    };
  }
  return report.includes("Model checking completed. No error has been found.")
    ? { status: "success", prints }
    : { status: "other", headline: report.join("\n"), prints };
};

const cells = getUnionGrid();
const answers: Record<string, RecordedAnswer> = {};
let next = 0;
const work = async () => {
  const directory = mkdtempSync(join(tmpdir(), "union-grid-"));
  while (next < cells.length) {
    const cell = cells[next++];
    writeFileSync(join(directory, "M.tla"), cell.source);
    writeFileSync(join(directory, "M.cfg"), cell.config);
    const result = await run(
      "java",
      ["-cp", jarPath, "tlc2.TLC", "-nowarning", "-workers", "1", "M"],
      { cwd: directory },
    ).catch((error: { stdout: string }) => error);
    answers[cell.id] = getAnswer(result.stdout);
    if (Object.keys(answers).length % 200 === 0) {
      console.log(`${Object.keys(answers).length} of ${cells.length}`);
    }
  }
};
await Promise.all(Array.from({ length: availableParallelism() }, work));

const fixtures = join(import.meta.dirname, "../tests/fixtures/union-grid");
mkdirSync(fixtures, { recursive: true });
const sorted = Object.fromEntries(cells.map((cell) => [cell.id, answers[cell.id]]));
writeFileSync(join(fixtures, "tlc.json"), `${JSON.stringify(sorted, null, 2)}\n`);
console.log(`Recorded ${cells.length} cells`);
