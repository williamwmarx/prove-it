import { existsSync, readFileSync } from "node:fs";
import { basename, resolve } from "node:path";

import { getNativeAddon, type NativeSanyXml } from "../engine/native";
import { EngineUnavailableError } from "../errors";
import { EXIT_STATUS } from "../exit-codes";
import { SANY_STANDARD_MODULES } from "../sany/modules";
import { NOT_NATIVE_EXIT_CODE } from "./sany-text";
import { createModuleLoader, printMissingFile } from "./shared";

// The usage that XMLExporter.printUsage prints with UsageGenerator.
const XML_EXPORT_USAGE = (() => {
  const bold = (text: string) => `\x1b[1m${text}\x1b[0m`;
  const options = [
    ["-I", "Include; use given directory path to resolve module dependencies."],
    ["-help", "Print this usage information."],
    ["-o", "Offline mode; skip XML schema validation step."],
    [
      "-r",
      "Restrict mode; include only declarations and definitions of the specified module, excluding extended or instantiated modules.",
    ],
    ["-t", "Terse; format XML output without tabs or newlines."],
    [
      "-u",
      "Uncomment; process boxed comments and single-line comments (\\*) in pre-comments to extract their content.",
    ],
  ];
  const tips = [
    "Only one root TLA+ file can be parsed per run.",
    "Multiple directory search paths can be given by providing multiple -I arguments.",
    "XML schema validation does not require network access.",
  ];
  return [
    "",
    bold("NAME"),
    "",
    "\ttla2sany.xml.XMLExporter - Emit SANY's parse tree as XML - Version 2.2 created 08 July 2020",
    "",
    "",
    bold("SYNOPSIS"),
    "",
    `\t${bold("tla2sany.xml.XMLExporter")} [${bold("-Iortu")}] [${bold("-help")}] FILE`,
    "",
    bold("DESCRIPTION"),
    "",
    "\tGiven a TLA+ file, parse that file with SANY then translate the module's semantic parse tree to XML, including all the modules depended on. The XML is printed to stdout and its output format is given by an XML Schema file (.xsd) found at https://proofs.tlapl.us/doc/web/sany.xsd.",
    "",
    bold("OPTIONS"),
    "",
    ...options.map(([flag, description]) => `\t${bold(flag)}\n\t\t${description}`),
    "",
    bold("TIPS"),
    "",
    ...tips.flatMap((tip) => [`\t${tip}`, ""]),
    "",
  ].join("\n");
})();

// XMLExporterExitCode.
const XML_EXPORT_EXIT_CODE = { argsParsingFailure: 1, specParsingFailure: 2 } as const;

// What the CLI exits with where tla-front doesn't export the spec, as the native binary does.

const printXmlExportUsageError = (message: string) => {
  process.stderr.write(`ERROR: ${message}\n${XML_EXPORT_USAGE}`);
  return XML_EXPORT_EXIT_CODE.argsParsingFailure;
};

interface XmlExportArgs {
  flags: Set<string>;
  includes: string[];
  error: "missing-include" | "several-files" | undefined;
}

// XMLExporter reads the flags before the last argument, which names the module, and skips an
// argument it does not know, which then counts as another module.
const parseXmlExportArgs = (args: string[]): XmlExportArgs => {
  const flagNames = new Set(["-o", "-t", "-r", "-u"]);
  const parsed: XmlExportArgs = { flags: new Set(), includes: [], error: undefined };
  const lastFlag = { index: -1 };
  for (let index = 0; index < args.length - 1; index++) {
    if (flagNames.has(args[index])) {
      parsed.flags.add(args[index]);
      lastFlag.index = index;
      continue;
    }
    if (args[index] !== "-I") continue;
    index++;
    if (index > args.length - 2) return { ...parsed, error: "missing-include" };
    parsed.includes.push(args[index]);
    lastFlag.index = index;
  }
  return lastFlag.index === args.length - 2 ? parsed : { ...parsed, error: "several-files" };
};

// What XMLExporter prints for a root module that no file holds: SimpleFilenameToStream names the
// file and where it looked, then SANY's fatal error.
const printMissingRoot = (name: string, fileName: string, includes: string[]) => {
  printMissingFile(process.cwd(), `./${fileName}`, includes);
  const fatal = `Unknown location\n\nCannot find source file for module ${basename(fileName, ".tla")}`;
  process.stderr.write(
    `\nFatal errors while parsing TLA+ spec in file ${name}\n\n${fatal}\n*** Errors: 1\n\n${fatal}\n\n\n\nERROR: Failed to parse module.\n`,
  );
  return XML_EXPORT_EXIT_CODE.specParsingFailure;
};

// What SANY's XMLExporter prints, as tla-front writes it, through the native engine, which reads
// nothing itself: it names the modules it needs, and is asked again with them.
const exportNativeXml = (
  root: string,
  source: string,
  fileName: string,
  flags: string,
  loadModule: (name: string) => string | undefined,
) => {
  const addon = getNativeAddon();
  if (typeof addon === "string") throw new EngineUnavailableError(addon, false);
  const known = new Map<string, string | undefined>();
  const write = (): Exclude<NativeSanyXml, { kind: "needed" }> => {
    const result = addon.sanyXml(root, source, fileName, flags, [...known]);
    if (result.kind !== "needed") return result;
    result.keys.forEach((key) => known.set(key, loadModule(key.slice("module:".length))));
    return write();
  };
  return write();
};

export const exportXml = (args: string[]) => {
  if (args.length === 0) return printXmlExportUsageError("at least one .tla file must be given");
  const parsed = parseXmlExportArgs(args);
  if (parsed.error === "missing-include") {
    return printXmlExportUsageError(
      "the -I flag must be followed by a directory and at least one .tla file",
    );
  }
  if (parsed.error === "several-files") {
    return printXmlExportUsageError("Only one TLA file to check allowed!");
  }
  const name = args[args.length - 1];
  if (name === "-help") {
    process.stdout.write(XML_EXPORT_USAGE);
    return EXIT_STATUS.success;
  }
  const fileName = name.endsWith(".tla") ? name : `${name}.tla`;
  const rootName = basename(fileName, ".tla");
  // SANY looks for each module in the working directory, then in the -I directories, which
  // XMLExporter passes in place of TLA-Library, then among its standard modules.
  const directories = [".", ...parsed.includes];
  const path = directories.map((directory) => resolve(directory, fileName)).find(existsSync);
  const source =
    path === undefined ? SANY_STANDARD_MODULES.get(rootName) : readFileSync(path, "utf8");
  if (source === undefined) return printMissingRoot(name, fileName, parsed.includes);
  const exported = exportNativeXml(
    rootName,
    source,
    name,
    [...parsed.flags].map((flag) => flag.slice(1)).join(""),
    createModuleLoader(directories),
  );
  if (exported.kind === "declined") {
    console.error(`prove-it: not native yet: ${exported.reason}`);
    return NOT_NATIVE_EXIT_CODE;
  }
  process.stderr.write(exported.stderr);
  process.stdout.write(exported.stdout);
  return exported.exitCode;
};
