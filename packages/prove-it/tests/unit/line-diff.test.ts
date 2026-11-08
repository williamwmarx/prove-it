import { describe, expect, it } from "bun:test";

import { getLineDiff } from "../../scripts/line-diff";

describe("getLineDiff", () => {
  it("finds nothing between equal texts", () => {
    expect(getLineDiff(["a", "b"], ["a", "b"])).toEqual([]);
    expect(getLineDiff([], [])).toEqual([]);
  });

  it("names the lines one text drops and the other adds, in order", () => {
    expect(getLineDiff(["a", "b", "c", "d"], ["a", "x", "c", "d", "e"])).toEqual([
      "-b",
      "+x",
      "+e",
    ]);
    expect(getLineDiff(["x = 1", "y = 2"], ["y = 2", "x = 1"])).toEqual(["-x = 1", "+x = 1"]);
  });

  // Myers' own example: the longest common subsequence of the two is four lines long.
  it("gives a shortest edit script", () => {
    const diff = getLineDiff("a b c a b b a".split(" "), "c b a b a c".split(" "));
    expect(diff.length).toBe(7 + 6 - 2 * 4);
    expect(diff.filter((line) => line.startsWith("-")).length).toBe(3);
  });

  it("reports every line of very different texts", () => {
    const left = Array.from({ length: 3000 }, (_, index) => `left ${index}`);
    const right = Array.from({ length: 3000 }, (_, index) => `right ${index}`);
    const diff = getLineDiff(left, right);
    expect(diff.length).toBe(6000);
    expect(diff.filter((line) => line.startsWith("-")).length).toBe(3000);
  });
});
