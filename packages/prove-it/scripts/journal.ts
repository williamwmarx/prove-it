// A journal of JSON entries, one to a line, that a long script appends to as it finishes each piece
// of work, so that a run stopped part way can go on from it. A stop can leave the last line
// unfinished: readers take only the lines a newline ends, and the run that goes on cuts the
// unfinished line before appending, so that no entry is written onto its fragment.

import { appendFileSync, existsSync, readFileSync, writeFileSync } from "node:fs";

export const readJournal = <Entry>(path: string): Entry[] =>
  existsSync(path)
    ? readFileSync(path, "utf8")
        .split("\n")
        .slice(0, -1)
        .map((line): Entry => JSON.parse(line))
    : [];

// Cuts the line a stop left unfinished. Call it once, before anything appends.
export const repairJournal = (path: string) => {
  if (!existsSync(path)) return;
  const text = readFileSync(path, "utf8");
  const end = text.lastIndexOf("\n") + 1;
  if (end < text.length) writeFileSync(path, text.slice(0, end));
};

export const appendJournal = (path: string, entry: unknown) =>
  appendFileSync(path, `${JSON.stringify(entry)}\n`);
