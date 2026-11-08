// The optional npm packages that carry the native engine, one per platform, each holding only
// prove-it-engine.node: no JavaScript and no install scripts. Each has the os, cpu and libc fields
// that make a package manager install only the one for its platform, and the main package's
// version. src/engine/native.ts finds the installed one.
// Usage: bun scripts/platform-packages.ts build [--target <Rust target>]
//        bun scripts/platform-packages.ts pack <destination>
// build compiles the addon with cargo, for the host or a Rust target whose standard library and
// linker are installed, and writes its package to native/npm/<platform>. pack packs every package
// built there into the destination.

import { spawnSync } from "node:child_process";
import {
  copyFileSync,
  existsSync,
  mkdirSync,
  readdirSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { join } from "node:path";

import { ADDON_FILE } from "../src/engine/native";

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

const run = (command: string, args: string[], cwd: string) => {
  const result = spawnSync(command, args, {
    cwd,
    stdio: ["ignore", "pipe", "inherit"],
    encoding: "utf8",
  });
  if (result.status !== 0) {
    console.error(`${command} ${args.join(" ")} failed`);
    process.exit(result.status ?? 1);
  }
  return result.stdout;
};

const build = (requested: string | undefined) => {
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
      ...(requested ? ["--target", requested] : []),
    ],
    NATIVE_DIRECTORY,
  );
  const main = JSON.parse(readFileSync(join(PACKAGE_DIRECTORY, "package.json"), "utf8"));
  const directory = join(NPM_DIRECTORY, platform.name);
  rmSync(directory, { recursive: true, force: true });
  mkdirSync(directory, { recursive: true });
  copyFileSync(
    join(
      NATIVE_DIRECTORY,
      "target",
      ...(requested ? [requested] : []),
      "release",
      platform.library,
    ),
    join(directory, ADDON_FILE),
  );
  copyFileSync(join(PACKAGE_DIRECTORY, "../../LICENSE"), join(directory, "LICENSE"));
  const manifest = {
    name: `${main.name}-${platform.name}`,
    version: main.version,
    description: `The native engine of ${main.name} for ${platform.description}`,
    license: "MIT",
    repository: main.repository,
    os: [platform.os],
    cpu: [platform.cpu],
    ...(platform.libc && { libc: [platform.libc] }),
    files: [ADDON_FILE],
    publishConfig: main.publishConfig,
  };
  writeFileSync(join(directory, "package.json"), `${JSON.stringify(manifest, null, 2)}\n`);
  console.log(`Built ${manifest.name}@${manifest.version} in ${directory}`);
};

const pack = (destination: string | undefined) => {
  if (destination === undefined) {
    console.error("Usage: bun scripts/platform-packages.ts pack <destination>");
    process.exit(1);
  }
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
      `Not built, so their users get the TypeScript engine: ${missing.map((platform) => platform.name).join(", ")}`,
    );
  }
};

const COMMANDS: Record<string, () => void> = {
  build: () => {
    const targetIndex = process.argv.indexOf("--target");
    build(targetIndex === -1 ? undefined : process.argv[targetIndex + 1]);
  },
  pack: () => pack(process.argv[3]),
};

if (import.meta.main) {
  const command = COMMANDS[process.argv[2] ?? ""];
  if (command === undefined) {
    console.error(
      "Usage: bun scripts/platform-packages.ts build [--target <Rust target>] | pack <destination>",
    );
    process.exit(1);
  }
  command();
}
