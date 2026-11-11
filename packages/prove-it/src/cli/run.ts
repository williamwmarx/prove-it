import { delimiter } from "node:path";

import { EngineUnavailableError } from "../errors";
import { EXIT_STATUS } from "../exit-codes";
import { getTlcVersion } from "../tlc/version";
import { NOT_NATIVE_EXIT_CODE } from "./sany-text";
import { getToolsJar, type JavaProperties, reportErrors, UnreadableFileError } from "./shared";
import { checkNatively, checkSpecs } from "./tlc";

// Tools that run TLC with Java, such as pstack's statechart skill, can run tla-ts in place of java,
// as in `tla-ts -DTLA-Library=lib -cp tla2tools.jar tlc2.TLC Spec`. Other JVM options are ignored.
const JAVA_MAIN_CLASSES = ["tlc2.TLC", "tla2sany.xml.XMLExporter"];

const TLA_LIBRARY_PROPERTY = "-DTLA-Library=";

const TEMPORARY_DIRECTORY_PROPERTY = "-Djava.io.tmpdir=";

const TLC_VERSION_PROPERTY = "-Dtla-ts.tlc=";

const getJavaLaunch = (args: string[]) => {
  const java: JavaProperties = { libraries: [], properties: new Map() };
  for (let index = 0; index < args.length; index++) {
    const arg = args[index];
    if (arg.startsWith("-D")) {
      const separator = arg.indexOf("=");
      java.properties.set(
        arg.slice(2, separator === -1 ? undefined : separator),
        separator === -1 ? "" : arg.slice(separator + 1),
      );
    }
    if (arg === "-cp" || arg === "-classpath" || arg === "--class-path") {
      index++;
      java.classPath = args[index];
    } else if (arg === "-jar") {
      java.classPath = args[index + 1];
      return { mainClass: "tlc2.TLC", args: args.slice(index + 2), java };
    } else if (arg.startsWith(TLA_LIBRARY_PROPERTY)) {
      // Java keeps a system property's last value, and String.split drops the empty entries it
      // ends with, unless the property is empty.
      const libraries = arg.slice(TLA_LIBRARY_PROPERTY.length).split(delimiter);
      while (libraries.length > 1 && libraries[libraries.length - 1] === "") libraries.pop();
      java.libraries =
        libraries.length === 1 && libraries[0] === "" && arg.length > TLA_LIBRARY_PROPERTY.length
          ? []
          : libraries;
    } else if (arg.startsWith(TEMPORARY_DIRECTORY_PROPERTY)) {
      java.temporaryDirectory = arg.slice(TEMPORARY_DIRECTORY_PROPERTY.length);
    } else if (arg.startsWith(TLC_VERSION_PROPERTY)) {
      java.tlcVersion = arg.slice(TLC_VERSION_PROPERTY.length) === "1.7.4" ? "1.7.4" : "master";
    } else if (!arg.startsWith("-D") && !arg.startsWith("-X")) {
      const isLaunch = index > 0 || JAVA_MAIN_CLASSES.includes(arg);
      return isLaunch ? { mainClass: arg, args: args.slice(index + 1), java } : undefined;
    }
  }
  return undefined;
};

const run = async (args: string[]) => {
  if (args[0] === "tlapm") {
    const tlapm = await import("./tlapm");
    return reportErrors(() => tlapm.runTlapm(args.slice(1)));
  }
  const launch = getJavaLaunch(args);
  if (launch === undefined) {
    const java = { libraries: [], properties: new Map() };
    return (await checkNatively(args, args, java)) ?? checkSpecs(args, java);
  }
  launch.java.tlcVersion ??= await getTlcVersion(getToolsJar(launch.java));
  if (launch.mainClass === "tlc2.TLC") {
    return (
      (await checkNatively(args, launch.args, launch.java)) ??
      checkSpecs(launch.args, launch.java, launch.mainClass === "tlc2.TLC")
    );
  }
  if (launch.mainClass === "tla2sany.xml.XMLExporter") {
    // TLC 1.7.4's XMLExporter is retired, and only master's is native.
    if (launch.java.tlcVersion === "1.7.4") {
      console.error("prove-it: not native yet: TLC 1.7.4");
      return 1;
    }
    const exporter = await import("./xml-exporter");
    return reportErrors(() => exporter.exportXml(launch.args));
  }
  console.error(
    `Error: tla-ts runs the Java classes ${JAVA_MAIN_CLASSES.join(" and ")}, not ${launch.mainClass}.`,
  );
  return 1;
};

// Without a native engine, the CLI exits as TLC does on an internal error.
export const runCli = async () => {
  process.exitCode = await run(process.argv.slice(2)).catch((error: unknown) => {
    if (error instanceof UnreadableFileError) {
      console.error(`prove-it: not native yet: ${error.message}`);
      return NOT_NATIVE_EXIT_CODE;
    }
    if (!(error instanceof EngineUnavailableError)) throw error;
    console.error(error.message);
    return EXIT_STATUS.error;
  });
};
