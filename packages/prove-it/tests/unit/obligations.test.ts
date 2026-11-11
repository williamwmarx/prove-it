import { describe, expect, it } from "bun:test";

import { getObligations } from "../../src/obligations";

const getTexts = (body: string) =>
  getObligations(
    [{ file: "M.tla", source: `---- MODULE M ----\nEXTENDS Naturals\n${body}\n====\n` }],
    () => undefined,
  )[0].obligations.map((obligation) => obligation.text);

describe("proof obligations match tlapm", () => {
  it("prints an @ that no earlier step defines", () => {
    const texts = getTexts(
      [
        "VARIABLE x",
        "THEOREM x = 1",
        "<1>1. TRUE",
        "  OBVIOUS",
        "<1>2. @ = x",
        "  OBVIOUS",
        "<1>3. QED",
        "  OBVIOUS",
      ].join("\n"),
    );
    expect(texts).toEqual([
      "ASSUME NEW VARIABLE x\nPROVE  x = 1\n",
      "ASSUME NEW VARIABLE x\nPROVE  TRUE\n",
      "ASSUME NEW VARIABLE x\nPROVE  @ = x\n",
    ]);
  });

  it("fails an INSTANCE inside its own instantiation as tlapm's stack overflow", () => {
    const sources = [
      "---- MODULE M ----\n---- MODULE Inner ----\nTHEOREM LET I == INSTANCE Inner IN TRUE\n====\nTHEOREM TRUE\n====\n",
      "---- MODULE M ----\n---- MODULE P ----\nTHEOREM LET I == INSTANCE Q IN TRUE\n====\n---- MODULE Q ----\nTHEOREM LET J == INSTANCE P IN TRUE\n====\nTHEOREM TRUE\n====\n",
      "---- MODULE M ----\nTHEOREM LET I == INSTANCE M IN TRUE\n====\n",
    ];
    for (const source of sources) {
      expect(() => getObligations([{ file: "M.tla", source }], () => undefined)).toThrow(
        expect.objectContaining({ name: "TlaProofError", exception: "Stack overflow" }),
      );
    }
  });
});
