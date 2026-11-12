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
