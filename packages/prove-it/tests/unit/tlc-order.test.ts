import { describe, expect, it } from "bun:test";

import { createTlcOrder } from "../../src/tlc/order";

describe("TLC's declaration order", () => {
  it("leaves out what a theorem's ASSUME declares", () => {
    const source = [
      "---- MODULE Main ----",
      "CONSTANT N",
      "Field == [NEW |-> 1].NEW",
      "VARIABLE x",
      'Text == "NEW"',
      "VARIABLE w",
      "THEOREM Thm == ASSUME NEW VARIABLE y, CONSTANT c, NEW d PROVE y = y",
      "====",
    ].join("\n");
    const order = createTlcOrder(source, () => undefined);
    expect(order.getDeclarationOrder("variable")).toEqual(["w", "x"]);
    expect(order.getDeclarationOrder("constant")).toEqual(["N"]);
  });
});
