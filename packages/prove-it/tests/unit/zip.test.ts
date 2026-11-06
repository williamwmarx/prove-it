import { afterAll, describe, expect, it } from "bun:test";
import { execFileSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { TlaError } from "../../src";
import { readZipEntry } from "../../src/tlc/zip";

// Info-ZIP's zip writes the archives, so the reader meets the layout another tool chose.
const directory = mkdtempSync(join(tmpdir(), "prove-it-zip-"));

afterAll(() => rmSync(directory, { recursive: true, force: true }));

const STORED_TEXT = "Manifest-Version: 1.0\nX-Git-Tag: v1.7.4\n";
const DEFLATED_TEXT = "TLA+ ".repeat(1000);

writeFileSync(join(directory, "stored.txt"), STORED_TEXT);
writeFileSync(join(directory, "deflated.txt"), DEFLATED_TEXT);

const zip = (args: string[], input?: string) =>
  execFileSync("zip", ["-q", "-X", ...args], { cwd: directory, input });

zip(["-0", "archive.zip", "stored.txt"]);
zip(["-9", "archive.zip", "deflated.txt"]);
zip(["-z", "archive.zip"], "A comment after the central directory\n");
writeFileSync(join(directory, "streamed.zip"), zip(["-9", "-", "deflated.txt"]));

const readText = async (archive: string, name: string) => {
  const data = await readZipEntry(readFileSync(join(directory, archive)), name);
  return data && new TextDecoder().decode(data);
};

describe("readZipEntry", () => {
  it("reads a stored entry", async () => {
    expect(await readText("archive.zip", "stored.txt")).toBe(STORED_TEXT);
  });

  it("inflates a deflated entry", async () => {
    expect(await readText("archive.zip", "deflated.txt")).toBe(DEFLATED_TEXT);
  });

  it("reads an entry whose sizes follow its data, as zip writes to a pipe", async () => {
    expect(await readText("streamed.zip", "deflated.txt")).toBe(DEFLATED_TEXT);
  });

  it("finds no entry that the archive doesn't have", async () => {
    expect(await readText("archive.zip", "missing.txt")).toBeUndefined();
  });

  it("rejects data that isn't a zip archive", async () => {
    await expect(readZipEntry(new TextEncoder().encode(STORED_TEXT), "stored.txt")).rejects.toThrow(
      TlaError,
    );
  });
});
