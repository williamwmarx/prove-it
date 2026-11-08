// Under symmetry TLC fingerprints the smallest image of each state. A VIEW that tells apart the
// images of one state makes the counts of a search depend on which image is the smallest, so these
// models check that the engine picks the same image as the interpreter.

import { afterEach, describe, expect, it, spyOn } from "bun:test";

import { check } from "../../src";

const setting = process.env.PROVE_IT_ENGINE;

afterEach(() => {
  if (setting === undefined) delete process.env.PROVE_IT_ENGINE;
  else process.env.PROVE_IT_ENGINE = setting;
});

// Checks a model with the engine and without, and that the engine searched every state.
const checkBoth = async (body: string, config: string) => {
  const source = `---- MODULE M ----\nEXTENDS Naturals, FiniteSets, TLC\n${body}\n====`;
  process.env.PROVE_IT_ENGINE = "debug";
  const lines: string[] = [];
  const spy = spyOn(console, "error").mockImplementation((message: unknown) => {
    if (typeof message === "string" && message.startsWith("[engine] ")) lines.push(message);
  });
  try {
    const result = await check({ source, config, onPrint: () => {} });
    process.env.PROVE_IT_ENGINE = "0";
    const reference = await check({ source, config, onPrint: () => {} });
    expect(result).toEqual(reference);
    return { result, lines };
  } finally {
    spy.mockRestore();
  }
};

const GROUPS =
  "CONSTANT P = {p1, p2, p3}\nCONSTANT V = {v1, v2}\nCONSTANT p1 = p1\nCONSTANT v1 = v1\nINIT Init\nNEXT Next";

describe("the engine under symmetry", () => {
  it.each([
    [
      "sets of records",
      [
        "CONSTANT P, V, p1, v1",
        "VARIABLES msgs, n",
        "Init == msgs = {} /\\ n = 0",
        "Next == \\/ \\E p \\in P, v \\in V, b \\in 0..1 : Cardinality(msgs) < 4",
        "              /\\ msgs' = msgs \\cup {[from |-> p, val |-> v, bal |-> b]} /\\ UNCHANGED n",
        "        \\/ n < 2 /\\ n' = n + 1 /\\ UNCHANGED msgs",
        "View == <<{IF m.from = p1 THEN [m EXCEPT !.bal = 0] ELSE m : m \\in msgs}, n>>",
        "Sym == Permutations(P) \\cup Permutations(V)",
      ],
    ],
    [
      "functions whose domains differ",
      [
        "CONSTANT P, V, p1, v1",
        "VARIABLES level, owner",
        "Init == level = [p \\in {} |-> 0] /\\ owner = [v \\in V |-> p1]",
        "Next == \\/ \\E p \\in P : level' = [q \\in DOMAIN level \\cup {p} |->",
        "              IF q = p /\\ p \\in DOMAIN level THEN (level[q] + 1) % 3",
        "              ELSE IF q = p THEN 0 ELSE level[q]] /\\ UNCHANGED owner",
        "        \\/ \\E v \\in V, p \\in P : owner' = [owner EXCEPT ![v] = p] /\\ UNCHANGED level",
        "View == <<[q \\in DOMAIN level |-> IF q = p1 THEN 0 ELSE level[q]], owner[v1]>>",
        "Sym == Permutations(P) \\cup Permutations(V)",
      ],
    ],
    [
      "tuples, and functions keyed by records",
      [
        "CONSTANT P, V, p1, v1",
        "VARIABLES last, bag",
        "Init == last = <<>> /\\ bag = [m \\in {} |-> 0]",
        "Next == \\E p \\in P, v \\in V : /\\ last' = <<p, v>>",
        "  /\\ \\/ Cardinality(DOMAIN bag) < 3 /\\ bag' = [m \\in DOMAIN bag \\cup {[to |-> p, val |-> v]} |->",
        "           IF m \\in DOMAIN bag THEN (bag[m] + 1) % 2 ELSE 0]",
        "     \\/ UNCHANGED bag",
        "View == <<last, [m \\in DOMAIN bag |-> IF m.to = p1 THEN 0 ELSE bag[m]]>>",
        "Sym == Permutations(P) \\cup Permutations(V)",
      ],
    ],
  ])("picks the image TLC fingerprints for %s", async (_, lines) => {
    const body = lines.join("\n");
    const config = `${GROUPS}\nVIEW View\nSYMMETRY Sym\nCHECK_DEADLOCK FALSE`;
    const symmetric = await checkBoth(body, config);
    expect(symmetric.result.status).toBe("success");
    expect(symmetric.lines).toContainEqual(expect.stringMatching(/^\[engine\] checked \d+ states/));
    // Symmetry merges states the VIEW alone tells apart.
    const viewed = await checkBoth(body, `${GROUPS}\nVIEW View\nCHECK_DEADLOCK FALSE`);
    expect(symmetric.result.distinctStates).toBeLessThan(viewed.result.distinctStates);
  });

  it("fails where an image mixes model values of different types, as TLC does", async () => {
    const { result } = await checkBoth(
      [
        "CONSTANT m, A_y, B_z",
        "VARIABLE s",
        "Init == s = {m, B_z}",
        "Next == UNCHANGED s",
        // The untyped m compares with either, but the image {A_y, B_z} of s can't be sorted.
        "Sym == Permutations({m, A_y})",
      ].join("\n"),
      "CONSTANT m = m\nCONSTANT A_y = A_y\nCONSTANT B_z = B_z\nINIT Init\nNEXT Next\nSYMMETRY Sym",
    );
    expect(result.status).toBe("error");
  });
});
