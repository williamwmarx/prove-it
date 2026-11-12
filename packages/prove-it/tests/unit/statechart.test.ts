import { afterAll, describe, expect, it } from "bun:test";
import { execFile } from "node:child_process";
import { rmSync } from "node:fs";
import { join } from "node:path";

import {
  getStatechartSpecs,
  prepareStatechart,
  readExpected,
  readStatechartCalls,
} from "../../scripts/statechart-calls";

const CLI = join(import.meta.dirname, "../../dist/cli.js");

const runCli = (args: string[], cwd: string) =>
  new Promise<{ output: string; status: number }>((resolve) => {
    execFile("node", [CLI, ...args], { cwd, maxBuffer: 1 << 30 }, (error, stdout, stderr) =>
      resolve({ output: stdout + stderr, status: error ? Number(error.code) : 0 }),
    );
  });

const TRACE_DECLINED = "rebuilding a trace: TLCGet";

// The calls other than those with -dump dot that the native check declines, by spec and index.
const DECLINED: Record<string, string> = {
  "CounterAction 2": TRACE_DECLINED,
  "CounterDeadlock 2": TRACE_DECLINED,
  "CounterGuard 2":
    "the engine stopped: applied a function outside its domain: rebuilding a trace: applied a function outside its domain",
  "CounterOrder 2": TRACE_DECLINED,
  "CounterTie 2": TRACE_DECLINED,
  "CounterView 2": TRACE_DECLINED,
  "FirstRule 2": TRACE_DECLINED,
  "FirstRule 3": TRACE_DECLINED,
  "FirstRule 4": TRACE_DECLINED,
  "SpacedNames 2": TRACE_DECLINED,
  "TypeGuard 2": `the engine stopped: applied a function outside its domain: ${TRACE_DECLINED}`,
  "UserNoDeadlock 2": TRACE_DECLINED,
};

// The corpus of pstack's statechart skill (https://github.com/michael-denyer/pstack-claude, under the
// MIT license in tests/fixtures/statechart/LICENSE),
// with each call the skill makes to TLC and SANY and what Java's TLC nightly prints for it.
describe("the CLI answers pstack's statechart skill like TLC", () => {
  describe.each(getStatechartSpecs())("for %s", (spec) => {
    const { root, work, getArgs, normalize } = prepareStatechart(spec, "/lib/tla2tools.jar");
    afterAll(() => rmSync(root, { recursive: true, force: true }));
    it.each([...readStatechartCalls(spec).entries()])("call %i", async (index, call) => {
      const args = getArgs(call);
      const result = await runCli(args, work);
      const declined = args.includes("-dump") ? "-dump dot" : DECLINED[`${spec} ${index}`];
      if (declined !== undefined) {
        expect(/^prove-it: not native yet: (.*)$/m.exec(result.output)?.[1]).toBe(declined);
        expect(result.status).toBe(1);
        return;
      }
      expect(normalize(result.output)).toBe<string | undefined>(
        readExpected(spec, call, index, "out"),
      );
      expect(result.status).toBe(call.status);
    });
  });
});
