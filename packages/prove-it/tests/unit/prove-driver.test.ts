import { describe, expect, it } from "bun:test";
import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";

import { prove } from "../../src";

// The Rust driver proves as the TypeScript one does: the same obligations, statuses and reasons.
const DIRECTORY = join(import.meta.dirname, "../fixtures/prove");

const loadModule = (name: string) => {
  const path = join(DIRECTORY, `${name}.tla`);
  return existsSync(path) ? readFileSync(path, "utf8") : undefined;
};

const proveWith = async (driver: string, name: string) => {
  const setting = process.env.PROVE_IT_PROVER_DRIVER;
  process.env.PROVE_IT_PROVER_DRIVER = driver;
  try {
    const streamed: unknown[] = [];
    const result = await prove({
      source: loadModule(name) ?? "",
      loadModule,
      onObligation: (obligation) => streamed.push(obligation),
    });
    return { result, streamed };
  } finally {
    if (setting === undefined) delete process.env.PROVE_IT_PROVER_DRIVER;
    else process.env.PROVE_IT_PROVER_DRIVER = setting;
  }
};

describe("the Rust driver", () => {
  it.each(["HourClock", "Simple"])("proves %s as the TypeScript driver does", async (name) => {
    const typescript = await proveWith("ts", name);
    const rust = await proveWith("rust", name);
    expect(rust.result).toEqual(typescript.result);
    expect(rust.streamed).toEqual(typescript.result.obligations);
  });
});
