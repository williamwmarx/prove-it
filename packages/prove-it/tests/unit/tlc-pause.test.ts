import { expect, it } from "bun:test";

import { checkOnEngine } from "../native-check";

// TLC's breadth-first model checker prompts on TLCSet("pause", TRUE) and resumes, as the jar
// does here, finding no error.
it('answers TLCSet("pause", TRUE) as TLC does', async () => {
  const result = await checkOnEngine({
    source:
      '---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x\' = x + 1 /\\ TLCSet("pause", x = 1)\n====',
    config: "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE",
  });
  expect(result.status).toBe("success");
});
