// The optional npm packages that carry the native engine, one per platform, each holding only
// prove-it-engine.node and the native prove-it binary (native/DESIGN.md 13), bin/prove-it: no
// JavaScript and no install scripts. Each has the os, cpu and libc fields that make a package
// manager install only the one for its platform, and the main package's version.
// src/engine/native.ts finds the installed one. The package declares no bin, so it never shadows
// the main package's.
// The engine as WebAssembly, for hosts without process.dlopen such as a browser, and for Node or Bun
// where no platform package loads, ships in the main package instead: build --target
// wasm32-unknown-unknown writes it to dist/prove-it-engine.wasm, after bun run build, beside the
// modules that name it.
// Usage: bun scripts/platform-packages.ts build [--target <Rust target>]
//        bun scripts/platform-packages.ts pack <destination>
//        bun scripts/platform-packages.ts install-test
// build compiles the addon and the binary with cargo, for the host or a Rust target whose standard library and
// linker are installed, and writes its package to native/npm/<platform>. pack packs every package
// built there into the destination. install-test packs the main package, built first, and the
// package built for this system, installs both with npm into an empty project, and checks that the
// installed CLI searches a model natively under Node and under Bun.

import { spawnSync } from "node:child_process";
import {
  chmodSync,
  copyFileSync,
  existsSync,
  mkdirSync,
  mkdtempSync,
  readdirSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { basename, join, resolve } from "node:path";

import { ADDON_FILE, WASM_FILE } from "../src/engine/native";

interface Platform {
  name: string;
  target: string;
  os: string;
  cpu: string;
  libc?: string;
  library: string;
  description: string;
}

const PACKAGE_DIRECTORY = join(import.meta.dirname, "..");
const NATIVE_DIRECTORY = join(PACKAGE_DIRECTORY, "native");
export const NPM_DIRECTORY = join(NATIVE_DIRECTORY, "npm");

const LINUX_LIBRARY = "libprove_it_napi.so";
export const PLATFORMS: Platform[] = [
  {
    name: "linux-x64-gnu",
    target: "x86_64-unknown-linux-gnu",
    os: "linux",
    cpu: "x64",
    libc: "glibc",
    library: LINUX_LIBRARY,
    description: "Linux x64 with glibc",
  },
  {
    name: "linux-arm64-gnu",
    target: "aarch64-unknown-linux-gnu",
    os: "linux",
    cpu: "arm64",
    libc: "glibc",
    library: LINUX_LIBRARY,
    description: "Linux arm64 with glibc",
  },
  {
    name: "linux-x64-musl",
    target: "x86_64-unknown-linux-musl",
    os: "linux",
    cpu: "x64",
    libc: "musl",
    library: LINUX_LIBRARY,
    description: "Linux x64 with musl",
  },
  {
    name: "linux-arm64-musl",
    target: "aarch64-unknown-linux-musl",
    os: "linux",
    cpu: "arm64",
    libc: "musl",
    library: LINUX_LIBRARY,
    description: "Linux arm64 with musl",
  },
  {
    name: "darwin-arm64",
    target: "aarch64-apple-darwin",
    os: "darwin",
    cpu: "arm64",
    library: "libprove_it_napi.dylib",
    description: "macOS arm64",
  },
  {
    name: "darwin-x64",
    target: "x86_64-apple-darwin",
    os: "darwin",
    cpu: "x64",
    library: "libprove_it_napi.dylib",
    description: "macOS x64",
  },
  {
    name: "win32-x64-msvc",
    target: "x86_64-pc-windows-msvc",
    os: "win32",
    cpu: "x64",
    library: "prove_it_napi.dll",
    description: "Windows x64",
  },
];

// The addon `build` built for this system, if it did, which the tests and the conformance scripts
// check with unless PROVE_IT_ENGINE_ADDON or PROVE_IT_ENGINE_WASM names an engine.
export const getBuiltAddon = () =>
  PLATFORMS.filter((platform) => platform.os === process.platform && platform.cpu === process.arch)
    .map((platform) => join(NPM_DIRECTORY, platform.name, ADDON_FILE))
    .find(existsSync);

// Sets PROVE_IT_ENGINE_ADDON to the addon built for this system, where no engine is named.
export const useBuiltAddon = () => {
  const addon = getBuiltAddon();
  if (
    addon !== undefined &&
    process.env.PROVE_IT_ENGINE_ADDON === undefined &&
    process.env.PROVE_IT_ENGINE_WASM === undefined
  ) {
    process.env.PROVE_IT_ENGINE_ADDON = addon;
  }
};

// npm is npm.cmd on Windows, which only a shell runs, and the shell splits an argument at its
// spaces, as in a temporary directory under C:\Users\Jane Doe, unless it is quoted. No argument
// here holds a quote.
const isShell = process.platform === "win32";

const run = (command: string, args: string[], cwd: string) => {
  const result = spawnSync(
    command,
    isShell ? args.map((argument) => (/\s/.test(argument) ? `"${argument}"` : argument)) : args,
    { cwd, stdio: ["ignore", "pipe", "inherit"], encoding: "utf8", shell: isShell },
  );
  if (result.status !== 0) {
    console.error(`${command} ${args.join(" ")} failed`);
    process.exit(result.status ?? 1);
  }
  return result.stdout;
};

const WASM_TARGET = "wasm32-unknown-unknown";

const buildWasm = () => {
  run(
    "cargo",
    ["build", "--release", "--locked", "--package", "prove-it-wasm", "--target", WASM_TARGET],
    NATIVE_DIRECTORY,
  );
  const directory = join(PACKAGE_DIRECTORY, "dist");
  mkdirSync(directory, { recursive: true });
  copyFileSync(
    join(NATIVE_DIRECTORY, "target", WASM_TARGET, "release", "prove_it_wasm.wasm"),
    join(directory, WASM_FILE),
  );
  console.log(`Built ${join(directory, WASM_FILE)}`);
};

const build = (requested: string | undefined) => {
  if (requested === WASM_TARGET) return buildWasm();
  const target = requested ?? /^host: (.+)$/m.exec(run("rustc", ["-vV"], NATIVE_DIRECTORY))?.[1];
  const platform = PLATFORMS.find((innerPlatform) => innerPlatform.target === target);
  if (platform === undefined) {
    console.error(`No platform package for the Rust target ${target}`);
    process.exit(1);
  }
  run(
    "cargo",
    [
      "build",
      "--release",
      "--locked",
      "--package",
      "prove-it-napi",
      "--package",
      "prove-it-cli",
      ...(requested ? ["--target", requested] : []),
    ],
    NATIVE_DIRECTORY,
  );
  const main = JSON.parse(readFileSync(join(PACKAGE_DIRECTORY, "package.json"), "utf8"));
  const directory = join(NPM_DIRECTORY, platform.name);
  rmSync(directory, { recursive: true, force: true });
  mkdirSync(directory, { recursive: true });
  const release = join(NATIVE_DIRECTORY, "target", ...(requested ? [requested] : []), "release");
  copyFileSync(join(release, platform.library), join(directory, ADDON_FILE));
  const binary = `bin/prove-it${platform.os === "win32" ? ".exe" : ""}`;
  mkdirSync(join(directory, "bin"));
  copyFileSync(join(release, basename(binary)), join(directory, binary));
  chmodSync(join(directory, binary), 0o755);
  copyFileSync(join(PACKAGE_DIRECTORY, "../../LICENSE"), join(directory, "LICENSE"));
  const manifest = {
    name: `${main.name}-${platform.name}`,
    version: main.version,
    description: `The native engine and prove-it binary of ${main.name} for ${platform.description}`,
    license: "MIT",
    repository: main.repository,
    os: [platform.os],
    cpu: [platform.cpu],
    ...(platform.libc && { libc: [platform.libc] }),
    files: [ADDON_FILE, binary],
    publishConfig: main.publishConfig,
  };
  writeFileSync(join(directory, "package.json"), `${JSON.stringify(manifest, null, 2)}\n`);
  console.log(`Built ${manifest.name}@${manifest.version} in ${directory}`);
};

const pack = (argument: string | undefined) => {
  if (argument === undefined) {
    console.error("Usage: bun scripts/platform-packages.ts pack <destination>");
    process.exit(1);
  }
  // npm runs in each package's directory, so a relative destination is resolved here first.
  const destination = resolve(argument);
  mkdirSync(destination, { recursive: true });
  const built = existsSync(NPM_DIRECTORY) ? readdirSync(NPM_DIRECTORY).sort() : [];
  if (built.length === 0) {
    console.error("No platform package is built: run bun scripts/platform-packages.ts build first");
    process.exit(1);
  }
  built.forEach((name) => {
    const tarball = run(
      "npm",
      ["pack", "--silent", "--ignore-scripts", "--pack-destination", destination],
      join(NPM_DIRECTORY, name),
    ).trim();
    console.log(join(destination, tarball));
  });
  const missing = PLATFORMS.filter((platform) => !built.includes(platform.name));
  if (missing.length > 0) {
    console.error(
      `Not built, so their users can check only with the interpreter (PROVE_IT_ENGINE=0): ${missing.map((platform) => platform.name).join(", ")}`,
    );
  }
};

const installTest = () => {
  const built = PLATFORMS.filter(
    (platform) =>
      platform.os === process.platform &&
      platform.cpu === process.arch &&
      existsSync(join(NPM_DIRECTORY, platform.name)),
  );
  if (built.length !== 1) {
    console.error(
      `Build exactly one platform package for ${process.platform}-${process.arch} first; built: ${built.map((platform) => platform.name).join(", ") || "none"}`,
    );
    process.exit(1);
  }
  const project = mkdtempSync(join(tmpdir(), "prove-it-install-"));
  // The main package's prepack copies files with cp, which Windows lacks; they aren't needed here.
  const npmPack = (directory: string) =>
    join(
      project,
      run("npm", ["pack", "--silent", "--ignore-scripts", "--pack-destination", project], directory)
        .trim()
        .split("\n")
        .at(-1) ?? "",
    );
  const tarballs = [npmPack(PACKAGE_DIRECTORY), npmPack(join(NPM_DIRECTORY, built[0].name))];
  writeFileSync(join(project, "package.json"), '{ "private": true }\n');
  run("npm", ["install", "--no-audit", "--no-fund", "--ignore-scripts", ...tarballs], project);
  const cli = join(project, "node_modules/@atemp/prove-it/dist/cli.js");
  const failures = ["node", "bun"].flatMap((runtime) => {
    const result = spawnSync(runtime, [cli, "Commit.tla"], {
      cwd: join(PACKAGE_DIRECTORY, "tests/fixtures/commit"),
      env: { ...process.env, PROVE_IT_ENGINE: "debug", PROVE_IT_ENGINE_ADDON: undefined },
      encoding: "utf8",
    });
    const isNative = result.status === 0 && result.stderr.includes("[engine] native: complete");
    console.log(`${runtime}: ${isNative ? "native: complete" : "not native"}`);
    return isNative
      ? []
      : [`${runtime} exited ${result.status}:\n${result.stdout}\n${result.stderr}`];
  });
  // The native CLI checks few models yet and stops on the others, but it starts and prints TLC's
  // banner first.
  const binary = join(
    project,
    `node_modules/@atemp/prove-it-${built[0].name}/bin/prove-it${process.platform === "win32" ? ".exe" : ""}`,
  );
  const native = spawnSync(binary, ["Commit.tla"], {
    cwd: join(PACKAGE_DIRECTORY, "tests/fixtures/commit"),
    encoding: "utf8",
  });
  const isStarted = native.stdout.startsWith("TLC2 Version ");
  console.log(`bin/prove-it: ${isStarted ? "started" : "didn't start"}`);
  if (!isStarted)
    failures.push(`bin/prove-it exited ${native.status}:\n${native.stdout}\n${native.stderr}`);
  rmSync(project, { recursive: true, force: true });
  if (failures.length > 0) {
    console.error(`The installed ${built[0].name} package failed:\n${failures.join("\n")}`);
    process.exit(1);
  }
};

const COMMANDS: Record<string, () => void> = {
  build: () => {
    const targetIndex = process.argv.indexOf("--target");
    build(targetIndex === -1 ? undefined : process.argv[targetIndex + 1]);
  },
  pack: () => pack(process.argv[3]),
  "install-test": installTest,
};

if (import.meta.main) {
  const command = COMMANDS[process.argv[2] ?? ""];
  if (command === undefined) {
    console.error(
      "Usage: bun scripts/platform-packages.ts build [--target <Rust target>] | pack <destination> | install-test",
    );
    process.exit(1);
  }
  command();
}
