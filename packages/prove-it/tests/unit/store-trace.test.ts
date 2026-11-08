import { afterAll, describe, expect, it } from "bun:test";
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { replayStoreTrace } from "../../scripts/store-replay";

const CLI = join(import.meta.dirname, "../../src/cli.ts");

const directory = mkdtempSync(join(tmpdir(), "prove-it-store-trace-"));

afterAll(() => rmSync(directory, { recursive: true, force: true }));

const traceFixture = (fixture: string, name: string) => {
  const path = join(directory, `${name}.jsonl`);
  const result = spawnSync("bun", [CLI, `${name}.tla`], {
    cwd: join(import.meta.dirname, "../fixtures", fixture),
    encoding: "utf8",
    env: { ...process.env, PROVE_IT_ENGINE: "debug", PROVE_IT_STORE_TRACE: path },
  });
  expect(result.stderr).toContain("[engine] checked ");
  return readFileSync(path, "utf8");
};

// Tests of the TypeScript engine's internals, which native/ts-only-tests.json lists with their Rust
// counterparts, don't apply when the native engine searches.
const isTypeScriptOnly = process.env.PROVE_IT_ENGINE_BACKEND === "rust";

describe("PROVE_IT_STORE_TRACE", () => {
  it.skipIf(isTypeScriptOnly).each([
    ["queue", "Queue"],
    ["commit", "Commit"],
    ["symmetry", "Symmetry"],
  ])("writes operations of %s that the store replays to the same ids", (fixture, name) => {
    const trace = traceFixture(fixture, name);
    const operations = trace.split("\n").filter((line) => line !== "");
    expect(JSON.parse(operations[0])[0]).toBe("resetStore");
    expect(operations.length).toBeGreaterThan(100);
    expect(replayStoreTrace(trace)).toBeUndefined();
  });

  it("keeps the search on one thread, since the workers' operations aren't traced", () => {
    // The workers run from the build, which bun run test makes first, and take levels only of a
    // search that runs long enough.
    const result = spawnSync(
      "bun",
      [join(import.meta.dirname, "../../dist/cli.js"), "Commit.tla"],
      {
        cwd: join(import.meta.dirname, "../../benchmarks/commit"),
        encoding: "utf8",
        env: {
          ...process.env,
          PROVE_IT_ENGINE: "debug",
          PROVE_IT_WORKERS: "4",
          PROVE_IT_STORE_TRACE: "/dev/null",
        },
      },
    );
    expect(result.stderr).toContain("checked 282251 states on 1 thread ");
  }, 60_000);

  it.skipIf(isTypeScriptOnly)("is caught out by an operation whose result changed", () => {
    const lines = traceFixture("queue", "Queue").split("\n");
    const index = lines.findIndex(
      (line) => line.startsWith('["tupleOf"') || line.startsWith('["appendTuple"'),
    );
    const record = JSON.parse(lines[index]);
    record[2] += 1;
    lines[index] = JSON.stringify(record);
    expect(replayStoreTrace(lines.join("\n"))).toEqual({
      line: index + 1,
      operation: record[0],
      expected: record[2],
      actual: record[2] - 1,
    });
  });

  it("records the strings something else ranks, so comparing them replays", () => {
    const path = join(directory, "ranks.jsonl");
    writeFileSync(path, "");
    const result = spawnSync(
      "bun",
      [
        "-e",
        [
          'const values = await import("./src/values.ts");',
          'const store = await import("./src/engine/store.ts");',
          "values.setStringOrder([]); store.resetStore();",
          'values.rankString("z"); values.rankString("a");',
          'store.compare(store.str("z"), store.str("a"));',
        ].join(" "),
      ],
      {
        cwd: join(import.meta.dirname, "../.."),
        encoding: "utf8",
        env: { ...process.env, PROVE_IT_STORE_TRACE: path },
      },
    );
    expect(result.status).toBe(0);
    const trace = readFileSync(path, "utf8");
    expect(trace).toContain('["rankStrings",[["z","a"]],null]');
    expect(replayStoreTrace(trace)).toBeUndefined();
  });

  it("records why an operation stopped", () => {
    const path = join(directory, "overflow.jsonl");
    writeFileSync(path, "");
    const result = spawnSync(
      "bun",
      [
        "-e",
        'const store = await import("./src/engine/store.ts"); store.resetStore(); try { store.int(2 ** 31); } catch {}',
      ],
      {
        cwd: join(import.meta.dirname, "../.."),
        encoding: "utf8",
        env: { ...process.env, PROVE_IT_STORE_TRACE: path },
      },
    );
    expect(result.status).toBe(0);
    const trace = readFileSync(path, "utf8");
    expect(trace.split("\n").at(-2)).toBe('["int",[2147483648],{"bail":"integer overflow"}]');
    expect(replayStoreTrace(trace)).toBeUndefined();
  });
});
