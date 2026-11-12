import { describe, expect, it } from "bun:test";
import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";

import { encodeForBackend, getObligations } from "../../scripts/native-prover";
import { TlaProverError } from "../../src/errors";

const FIXTURES = join(import.meta.dirname, "../fixtures/zenon-encoder");

const SOURCE = readFileSync(join(FIXTURES, "Encoder.tla"), "utf8");

// tlapm's .znn files differ from tla-ts's only in comments and line breaks.
const normalize = (text: string) => text.replace(/^;.*$/gm, "").replace(/\s+/g, " ").trim();

const encode = (id: number) =>
  encodeForBackend("Encoder.tla", SOURCE, () => undefined, id, "zenon");

const obligations = getObligations("Encoder.tla", SOURCE, () => undefined).obligations;

describe("Zenon obligations match tlapm", () => {
  it.each(
    obligations.filter((obligation) => existsSync(join(FIXTURES, `Encoder-${obligation.id}.znn`))),
  )("encodes obligation $id", (obligation) => {
    expect(normalize(encode(obligation.id))).toBe(
      normalize(readFileSync(join(FIXTURES, `Encoder-${obligation.id}.znn`), "utf8")),
    );
  });

  it("rejects a function with several bounds, which tlapm leaves Zenon an empty file for", () => {
    expect(() => encode(obligations[23].id)).toThrow(TlaProverError);
  });
});
