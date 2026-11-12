import { describe, expect, it } from "bun:test";

import { getFingerprints } from "../../scripts/native-prover";

const getModuleFingerprints = (theorems: string[]) =>
  getFingerprints(
    "M.tla",
    ["---- MODULE M ----", "EXTENDS Naturals", ...theorems, "===="].join("\n"),
    () => undefined,
  ).map((entry) => {
    if (entry.fingerprint instanceof Error) throw entry.fingerprint;
    return entry.fingerprint;
  });

describe("fingerprints match tlapm's fp_sequent", () => {
  it("ignores the names of bound variables but not of declarations", () => {
    const fingerprints = getModuleFingerprints([
      "THEOREM \\A x \\in Nat : x + 0 = x",
      "  OBVIOUS",
      "THEOREM \\A y \\in Nat : y + 0 = y",
      "  OBVIOUS",
      "THEOREM ASSUME NEW a PROVE a = a",
      "  OBVIOUS",
      "THEOREM ASSUME NEW b PROVE b = b",
      "  OBVIOUS",
    ]);
    expect(fingerprints[0]).toBe(fingerprints[1]);
    expect(fingerprints[2]).not.toBe(fingerprints[3]);
  });
});
