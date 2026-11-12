import { describe, expect, it } from "bun:test";
import { readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";

import { encodeForBackend } from "../../scripts/native-prover";
import { TlaProverError } from "../../src/errors";

// Modules from tlapm's tests and library, and the theory tlapm wrote for each of their obligations
// that it sent to Isabelle, as <module>-<obligation>.thy.
const FIXTURES = join(import.meta.dirname, "../fixtures/isabelle-encoder");

// tlapm's theories differ from tla-ts's only in comments, line breaks, and the theory's name,
// which tlapm takes from a temporary file.
const normalize = (text: string) =>
  text
    .replace(/\(\*[\s\S]*?\*\)/g, "")
    .replace(/\btlapm_[0-9a-f]+\b/g, "tlapm")
    .replace(/\s+/g, " ")
    .trim();

// The fixtures read only TLAPS, which the obligations know.
const encode = (name: string, id: number) =>
  encodeForBackend(
    `${name}.tla`,
    readFileSync(join(FIXTURES, `${name}.tla`), "utf8"),
    () => undefined,
    id,
    "isabelle",
  );

const theories = readdirSync(FIXTURES).flatMap((file) => {
  const match = /^(.+)-(\d+)\.thy$/.exec(file);
  return match ? [{ file, name: match[1], id: Number(match[2]) }] : [];
});

describe("Isabelle theories match tlapm", () => {
  it.each(theories)("encodes $file", (theory) => {
    expect(normalize(encode(theory.name, theory.id))).toBe(
      normalize(readFileSync(join(FIXTURES, theory.file), "utf8")),
    );
  });

  it("fails a goal with a set of several bounds, which tlapm leaves Isabelle part of a theory for", () => {
    expect(() => encode("Level_test", 1)).toThrow(TlaProverError);
  });
});
