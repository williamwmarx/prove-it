import { afterAll, afterEach, describe, expect, it } from "bun:test";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { appendJournal, readJournal, repairJournal } from "../../scripts/journal";

const directory = mkdtempSync(join(tmpdir(), "prove-it-journal-"));
const path = join(directory, "journal.jsonl");

afterEach(() => rmSync(path, { force: true }));

afterAll(() => rmSync(directory, { recursive: true, force: true }));

describe("a journal", () => {
  it("reads what was appended, in order", () => {
    appendJournal(path, { id: "a" });
    appendJournal(path, { id: "b" });
    expect(readJournal(path)).toEqual([{ id: "a" }, { id: "b" }]);
  });

  it("reads nothing where there is no journal", () => {
    expect(readJournal(path)).toEqual([]);
  });

  // A stop part way through a write leaves a fragment, which may end as a whole entry would.
  it("skips an unfinished last line, and cuts it before going on", () => {
    writeFileSync(path, '{"id":"a"}\n{"id":"b","inputs":{}');
    expect(readJournal(path)).toEqual([{ id: "a" }]);
    repairJournal(path);
    appendJournal(path, { id: "c" });
    expect(readFileSync(path, "utf8")).toBe('{"id":"a"}\n{"id":"c"}\n');
    expect(readJournal(path)).toEqual([{ id: "a" }, { id: "c" }]);
  });
});
