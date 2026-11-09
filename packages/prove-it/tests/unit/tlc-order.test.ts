import { describe, expect, it } from "bun:test";
import { createTlcOrder } from "../../src/tlc/order";

describe("TLC's declaration order", () => {
  it("leaves out what a theorem's ASSUME declares", () => {
    const source = [
      "---- MODULE Main ----",
      "CONSTANT N",
      "VARIABLE x",
      "THEOREM Thm == ASSUME NEW VARIABLE y, CONSTANT c, NEW d PROVE y = y",
      "====",
    ].join("\n");
    const order = createTlcOrder(source, () => undefined);
    expect(order.getDeclarationOrder("variable")).toEqual(["x"]);
    expect(order.getDeclarationOrder("constant")).toEqual(["N"]);
  });
});
