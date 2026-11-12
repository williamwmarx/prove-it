import { describe, expect, it } from "bun:test";
import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";

import { check, parseConfig } from "../../src";

const FIXTURES = join(import.meta.dirname, "../fixtures");

// Models whose configurations assign values of each kind, substitute, scope to a module and
// define a constant operator by its values.
const MODELS = [
  ["commit", "Commit"],
  ["instances", "Scoping"],
  ["modules", "Scoped"],
  ["operator-constants", "ConstantOperatorConfiguration"],
  ["queue", "Queue"],
  ["randomization", "RandomModelValue"],
  ["strings", "StringOrder"],
  ["symmetry", "SymmetricMessages"],
  ["tlc-spec", "Rich"],
  ["view", "ViewSymmetry"],
] as const;

const checkModel = (
  directory: string,
  name: string,
  config: string | ReturnType<typeof parseConfig>,
) => {
  const prints: string[] = [];
  return check({
    source: readFileSync(join(FIXTURES, directory, `${name}.tla`), "utf8"),
    config,
    loadModule: (module) => {
      const path = join(FIXTURES, directory, `${module}.tla`);
      return existsSync(path) ? readFileSync(path, "utf8") : undefined;
    },
    onPrint: (text) => prints.push(text),
  }).then((result) => ({ result, prints }));
};

describe("check takes a ModelConfig as its configuration file", () => {
  it.each(MODELS)("checks %s/%s as with the file's text", async (directory, name) => {
    const text = readFileSync(join(FIXTURES, directory, `${name}.cfg`), "utf8");
    expect(await checkModel(directory, name, parseConfig(text))).toEqual(
      await checkModel(directory, name, text),
    );
  });
});

// The binary reads a Java launch's -D, as the library passes systemProperties: it checks a spec that
// doesn't read them natively, and declines TLCGet of one that is set, where the TypeScript check
// reads its value.
describe("check takes systemProperties as a Java launch's -D", () => {
  const getRun = (source: string) => {
    const prints: string[] = [];
    return check({
      source,
      config: "INIT Init\nNEXT Next",
      systemProperties: new Map([["color", "blue"]]),
      onPrint: (text) => prints.push(text),
    }).then((result) => ({ status: result.status, prints }));
  };

  it("reads a property TLCGet names", async () => {
    expect(
      await getRun(
        '---- MODULE P ----\nEXTENDS TLC\nVARIABLE x\nInit == PrintT(TLCGet("-Dcolor")) /\\ x = 0\nNext == UNCHANGED x\n====',
      ),
    ).toEqual({ status: "success", prints: ['"blue"'] });
  });

  it("checks a spec that reads none", async () => {
    expect(
      await getRun(
        "---- MODULE Q ----\nEXTENDS TLC\nVARIABLE x\nInit == PrintT(1) /\\ x = 0\nNext == UNCHANGED x\n====",
      ),
    ).toEqual({ status: "success", prints: ["1"] });
  });
});
