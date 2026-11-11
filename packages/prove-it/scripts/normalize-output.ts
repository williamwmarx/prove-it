// Rewrites what differs between two runs of TLC, or of Prove It, on the same model, so their
// outputs compare: the times, dates and durations, the version, the machine, the process, and
// where the files were. It never touches a count, a state or a message.

// The lines in which TLC reports its version and runtime, and the files SANY parses.
export const STARTUP_LINE =
  /^(TLC2 Version |Running breadth-first search |Running Random Simulation |Parsing file |Semantic processing of module |Linting of module )/;

// The lines in which TLC reports when it started, finished or reached a point, the only ones with
// a time or date of the run. A spec's states and what it prints keep theirs.
const TIMED_LINE =
  /^(Starting\.\.\. |Finished |Progress\(|Checking (\d+ branches of )?temporal properties )/;

// TLC prints a duration as 12ms with -tool, and otherwise as 05s, 02min 05s, 01h 02min or 1d 01h.
const replaceTimes = (output: string) =>
  output
    .split("\n")
    .map((line) =>
      TIMED_LINE.test(line)
        ? line
            .replace(/\d{4}-\d\d-\d\d \d\d:\d\d:\d\d/g, "_")
            .replace(/ in (?:\d+ms|\d+s|\d+min \d+s|\d+h \d+min|\d+d \d+h) at /g, " in _ at ")
        : line,
    )
    .join("\n");

// TLC's output without its startup lines, with the times and dates it printed as _.
export const getSteadyLines = (output: string) =>
  replaceTimes(output)
    .split("\n")
    .filter((line) => !STARTUP_LINE.test(line));

// The whole output, with what depends on the run rewritten:
// - the version of TLC, or of Prove It;
// - the machine and process in `Running breadth-first search ...` and `Running Random Simulation
//   ...`: the cores, the memory, the pid, the operating system, the runtime and the kinds of
//   fingerprint set and queue;
// - the directory of each file SANY parses, and where TLC found it: the temporary directory a
//   standard module is copied to, /tmp on Linux and under /var/folders on macOS; the jar a standard
//   module comes from, the path on the library path that led to a library module, or the module a
//   copy in the metadata directory was made from;
// - the directory of the class file an operator override was loaded from, or failed to match;
// - in a stack trace, where Prove It's built files are, the hash in a chunk's name, and the line
//   and column in it, which change with every build;
// - the Progress lines, with -tool their message 2200 whole, whose presence depends on how long the
//   run takes, since they come once a minute. The counts in them are those of the lines that end
//   the run.
export const normalizeOutput = (output: string) =>
  replaceTimes(output)
    .split("\n")
    .filter(
      (line) =>
        !line.startsWith("Progress(") &&
        !line.startsWith("@!@!@STARTMSG 2200:") &&
        line !== "@!@!@ENDMSG 2200 @!@!@",
    )
    .map((line) =>
      line
        .replace(/^TLC2 Version .*$/, "TLC2 Version _")
        .replace(
          /^(Running (?:breadth-first search|Random Simulation) .* on )\d+ cores? with \d+MB heap and \d+MB offheap memory \[pid: \d+\] \(.*\)\.$/,
          "$1_ cores with _MB heap and _MB offheap memory [pid: _] (_).",
        )
        .replace(/^(Parsing file \S+) \(\S+\)$/, "$1")
        .replace(/^(Parsing file )\S*\/tlc-\d+\//, "$1/tmp/tlc-_/")
        .replace(/^(Parsing file )(?!\/tmp\/tlc-_\/)\S*\/(\S+)$/, "$1$2")
        .replace(
          /^((?:Loading|Failed to match) \S+ operator override from file:)\S*\/(\S+\.class )/,
          "$1$2",
        )
        .replace(
          /(?:file:\/\/)?[^\s(]*\/dist\/([\w.]+?)(-[a-z0-9]{8})?\.js(?::\d+)*/g,
          (_, name: string, hash: string | undefined) => `dist/${name}${hash ? "-_" : ""}.js:_`,
        ),
    )
    .join("\n");

// A run's exit code, stdout and stderr as one normalised text, which two runs of a model share when
// they print the same. Prove It's notes on what its engine did, on stderr, aren't output.
export const getTranscript = (exitCode: string, stdout: string, stderr: string) => {
  const errorOutput = stderr.replace(/^\[engine\] .*\n/gm, "");
  return [
    `exit ${exitCode}`,
    normalizeOutput(stdout),
    ...(errorOutput === "" ? [] : ["--- stderr", normalizeOutput(errorOutput)]),
  ].join("\n");
};
