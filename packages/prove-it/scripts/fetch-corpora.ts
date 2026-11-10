import { execFileSync } from "node:child_process";
import { existsSync, mkdirSync } from "node:fs";
import { join } from "node:path";

import { CORPORA_DIRECTORY, getAllCorpora, getOption } from "./corpora";

// Usage: bun scripts/fetch-corpora.ts [--only examples,tlc,...]
const only = getOption("--only")?.split(",");
const known = new Set(getAllCorpora().map((corpus) => corpus.name));
const unknown = (only ?? []).filter((name) => !known.has(name));
if (
  process.argv.includes("--only") &&
  (only === undefined || only.length === 0 || unknown.length > 0)
) {
  throw new Error(
    `--only takes corpus names from: ${[...known].join(", ")}${unknown.length > 0 ? `; not ${unknown.join(", ")}` : ""}`,
  );
}

const git = (directory: string, args: string[]) =>
  execFileSync("git", args, { cwd: directory, stdio: "inherit" });

mkdirSync(CORPORA_DIRECTORY, { recursive: true });

getAllCorpora()
  .filter((corpus) => only === undefined || only.includes(corpus.name))
  .forEach((corpus) => {
    const directory = join(CORPORA_DIRECTORY, corpus.name);
    if (!existsSync(directory)) {
      mkdirSync(directory);
      git(directory, ["init", "--quiet"]);
      git(directory, ["remote", "add", "origin", corpus.repository]);
      git(directory, [
        "sparse-checkout",
        "set",
        "--no-cone",
        ...corpus.paths.map((path) => `/${path}/`),
      ]);
    }
    git(directory, [
      "fetch",
      "--quiet",
      "--depth",
      "1",
      "--filter=blob:none",
      "origin",
      corpus.commit,
    ]);
    git(directory, ["checkout", "--quiet", "--force", corpus.commit]);
    console.log(`${corpus.name} at ${corpus.commit.slice(0, 12)}`);
  });
