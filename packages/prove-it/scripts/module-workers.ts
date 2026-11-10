// Runs a script's work on each item, such as a recorded module, in worker processes, --jobs of them
// at once, each taking one item at a time, largest first. The script forks itself with --worker,
// and a worker does the work on each item the parent sends it, by index.

import { fork } from "node:child_process";

import { getOption } from "./corpora";

// The results by module index. A module whose worker exits mid-module has none. In a worker, it
// never resolves. A worker wraps each result, as a process can't send undefined.
export const runModuleWorkers = async <Item extends { id: string }, Result>(
  records: Item[],
  getSize: (record: Item) => number,
  work: (record: Item) => Promise<Result>,
  defaultJobs: number,
): Promise<Map<number, Result>> => {
  if (process.argv.includes("--worker")) {
    process.on("message", (index: number) => {
      void work(records[index]).then((result) => process.send?.({ result }));
    });
    // The script's top-level await on this promise never settles in a worker, and Node warns and
    // exits with code 13 when the event loop empties under one. So the worker exits once the parent
    // lets it go.
    process.once("disconnect", () => process.exit(0));
    return new Promise(() => {});
  }
  const jobs = Number(getOption("--jobs") ?? defaultJobs);
  const queue = records
    .map((record, index) => ({ index, size: getSize(record) }))
    .toSorted((left, right) => right.size - left.size)
    .map((entry) => entry.index);
  const byModule = new Map<number, Result>();
  // A worker that exits mid-module, as when a backend overflows the stack, gives way to a new one.
  await Promise.all(
    Array.from({ length: Math.min(jobs, queue.length) }, async () => {
      while (queue.length > 0) {
        const worker = fork(process.argv[1], [...process.argv.slice(2), "--worker"]);
        const next = () => {
          const index = queue.shift();
          if (index === undefined) return worker.disconnect();
          worker.send(index);
          worker.once("message", (message: { result: Result }) => {
            byModule.set(index, message.result);
            console.error(`${byModule.size}/${records.length} ${records[index].id}`);
            next();
          });
        };
        next();
        await new Promise((resolve) => worker.on("exit", resolve));
      }
    }),
  );
  return byModule;
};
