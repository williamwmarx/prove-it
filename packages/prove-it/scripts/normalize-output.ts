// Rewrites what differs between two runs of TLC, or of Prove It, on the same model, so their
// outputs compare: the times, dates and durations, the version, the machine, the process, and
// where the files were. It never touches a count, a state or a message.

// The lines in which TLC reports its version and runtime, and the files SANY parses.
export const STARTUP_LINE =
  /^(TLC2 Version |Running breadth-first search |Parsing file |Semantic processing of module |Linting of module )/;

// TLC prints a duration as 12ms with -tool, and otherwise as 05s, 02min 05s, 01h 02min or 1d 01h.
const replaceTimes = (output: string) =>
  output
    .replace(/\d{4}-\d\d-\d\d \d\d:\d\d:\d\d/g, "_")
    .replace(/ in (?:\d+ms|\d+s|\d+min \d+s|\d+h \d+min|\d+d \d+h) at /g, " in _ at ");

// TLC's output without its startup lines, with the times and dates it printed as _.
export const getSteadyLines = (output: string) =>
  replaceTimes(output)
    .split("\n")
    .filter((line) => !STARTUP_LINE.test(line));

// The whole output, with what depends on the run rewritten:
// - the version of TLC, or of Prove It;
// - the machine and process in `Running breadth-first search ...`: the cores, the memory, the pid,
//   the operating system, the runtime and the kinds of fingerprint set and queue;
// - the directory of each file SANY parses, and where TLC found it: the jar a standard module
//   comes from, or the path on the library path that led to a library module;
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
          /^(Running breadth-first search .* on )\d+ cores? with \d+MB heap and \d+MB offheap memory \[pid: \d+\] \(.*\)\.$/,
          "$1_ cores with _MB heap and _MB offheap memory [pid: _] (_).",
        )
        .replace(/^(Parsing file \S+) \((?:jar:)?file:\S+\)$/, "$1")
        .replace(/^(Parsing file \/tmp\/tlc-)\d+\//, "$1_/")
        .replace(/^(Parsing file )(?!\/tmp\/tlc-_\/)\S*\/(\S+)$/, "$1$2"),
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
