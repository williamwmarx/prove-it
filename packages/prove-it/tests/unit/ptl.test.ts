import { describe, expect, it } from "bun:test";

import { encodeForBackend, getObligations } from "../../scripts/native-prover";
import { getNativeAddon } from "../../src/engine/native";
import { TlaProverError } from "../../src/errors";

const TIME_LIMIT_MS = 10_000;

// The LS4 input for the obligation whose last hypothesis cites PTL.
const getInput = (theorem: string[]) => {
  const source = [
    "---- MODULE M ----",
    "EXTENDS Naturals",
    'PTL == TRUE (*{ by (prover: "ls4") }*)',
    'ExpandENABLED == TRUE (*{ by (prover: "expandenabled") }*)',
    "VARIABLE x",
    "vars == <<x>>",
    "Init == x = 0",
    "Next == x' = x + 1",
    "Spec == Init /\\ [][Next]_vars /\\ WF_vars(Next)",
    "Inv == x \\in Nat",
    ...theorem,
    "====",
  ].join("\n");
  const obligations = getObligations("M.tla", source, () => undefined).obligations;
  const cited = obligations.find((obligation) => obligation.text.includes("PTL \nPROVE"));
  if (!cited) throw new Error("expected an obligation that cites PTL");
  return encodeForBackend("M.tla", source, () => undefined, cited.id, "ls4");
};

// tlapm proves exactly the obligations expected to be unsat. An input LS4 can't decide gives no
// verdict.
const getVerdict = (theorem: string[]) => {
  const addon = getNativeAddon();
  if (typeof addon === "string") throw new Error(addon);
  const decision = addon.decide("ls4", getInput(theorem), TIME_LIMIT_MS, undefined, undefined);
  return decision.kind === "decided" ? decision.verdict : decision.kind;
};

const INDUCTION = [
  "THEOREM Spec => []Inv",
  "<1>1. Init => Inv",
  "  BY DEF Init, Inv",
  "<1>2. Inv /\\ [Next]_vars => Inv'",
  "  BY DEF Inv, Next, vars",
  "<1>. QED  BY <1>1, <1>2, PTL DEF Spec",
];

describe("PTL backend matches tlapm with LS4", () => {
  it("prints the LS4 input tlapm sends, with its atom names", () => {
    expect(getInput(INDUCTION)).toBe(
      "not (((always (h8828a -> h2f89a)) & (always ((h2f89a & (hfc35e | h18388)) -> (next h2f89a))) & (always (cc | ~ cc)) -> (((h8828a & (always (hfc35e | h18388))) & ((sometime (always hc5714)) -> (always (sometime (hfc35e & (~ h18388)))))) -> (always h2f89a))))",
    );
  });

  it("proves an invariant by induction", () => {
    expect(getVerdict(INDUCTION)).toBe("unsat");
  });

  it("fails an induction without its base case", () => {
    const verdict = getVerdict([
      "THEOREM Spec => []Inv",
      "<1>2. Inv /\\ [Next]_vars => Inv'",
      "  BY DEF Inv, Next, vars",
      "<1>. QED  BY <1>2, PTL DEF Spec",
    ]);
    expect(verdict).toBe("sat");
  });

  it("proves a chain of leads-to steps", () => {
    const verdict = getVerdict([
      "THEOREM Spec => (x = 0 ~> x = 2)",
      "<1>1. Spec => (x = 0 ~> x = 1)",
      "  OMITTED",
      "<1>2. Spec => (x = 1 ~> x = 2)",
      "  OMITTED",
      "<1>. QED  BY <1>1, <1>2, PTL",
    ]);
    expect(verdict).toBe("unsat");
  });

  it("fails a chain of leads-to steps with a missing link", () => {
    const verdict = getVerdict([
      "THEOREM Spec => (x = 0 ~> x = 2)",
      "<1>1. Spec => (x = 0 ~> x = 1)",
      "  OMITTED",
      "<1>. QED  BY <1>1, PTL",
    ]);
    expect(verdict).toBe("sat");
  });

  it("proves progress from weak fairness when the action stays enabled", () => {
    const verdict = getVerdict([
      "THEOREM ASSUME []ENABLED <<Next>>_vars PROVE Spec => []<><<Next>>_vars",
      "  BY PTL DEF Spec",
    ]);
    expect(verdict).toBe("unsat");
  });

  it("fails progress from weak fairness when the action is only enabled infinitely often", () => {
    const verdict = getVerdict([
      "THEOREM ASSUME []<>ENABLED <<Next>>_vars PROVE Spec => []<><<Next>>_vars",
      "  BY PTL DEF Spec",
    ]);
    expect(verdict).toBe("sat");
  });

  it("proves progress from strong fairness when the action is enabled infinitely often", () => {
    const verdict = getVerdict([
      "THEOREM ASSUME []<>ENABLED <<Next>>_vars PROVE SF_vars(Next) => []<><<Next>>_vars",
      "  BY PTL",
    ]);
    expect(verdict).toBe("unsat");
  });

  it("treats formulas that print differently as different atoms", () => {
    expect(getVerdict(["THEOREM ASSUME x = 1 PROVE x = 1", "  BY PTL"])).toBe("unsat");
    expect(getVerdict(["THEOREM ASSUME x = 1 PROVE 1 = x", "  BY PTL"])).toBe("sat");
  });

  it("keeps a constant assumption for every state but a variable one only for the first", () => {
    expect(getVerdict(["THEOREM ASSUME NEW CONSTANT c, c = 1 PROVE [](c = 1)", "  BY PTL"])).toBe(
      "unsat",
    );
    expect(getVerdict(["THEOREM ASSUME x = 1 PROVE [](x = 1)", "  BY PTL"])).toBe("sat");
  });

  it("splits on cases that hold only now under an assumption about an operator a proof defines", () => {
    const verdict = getVerdict([
      "THEOREM TRUE",
      "<1>. DEFINE P(T) == T # {}",
      "<1>1. ASSUME NEW T, P(T) PROVE T = T",
      "  <2>1. CASE T = {}",
      "    OMITTED",
      "  <2>2. CASE ~(T = {})",
      "    OMITTED",
      "  <2>. QED  BY <2>1, <2>2, PTL",
      "<1>. QED  OBVIOUS",
    ]);
    expect(verdict).toBe("unsat");
  });

  it("fails to split on constant cases, which hold always", () => {
    const verdict = getVerdict([
      "THEOREM ASSUME NEW T PROVE T = T",
      "<1>1. CASE T = {}",
      "  OMITTED",
      "<1>2. CASE ~(T = {})",
      "  OMITTED",
      "<1>. QED  BY <1>1, <1>2, PTL",
    ]);
    expect(verdict).toBe("sat");
  });

  it("fails a step whose ENABLED needs a hidden definition, as tlapm's soundness check does", () => {
    expect(() =>
      getInput([
        "THEOREM ASSUME []ENABLED <<Next>>_vars PROVE Spec => []<><<Next>>_vars",
        "  BY ExpandENABLED, PTL DEF Spec",
      ]),
    ).toThrow(TlaProverError);
  });
});
