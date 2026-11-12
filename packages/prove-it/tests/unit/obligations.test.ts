import { describe, expect, it } from "bun:test";

import { getObligations } from "../../scripts/native-prover";

const getTexts = (body: string) =>
  getObligations(
    "M.tla",
    `---- MODULE M ----\nEXTENDS Naturals\n${body}\n====\n`,
    () => undefined,
  ).obligations.map((obligation) => obligation.text);

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
});
