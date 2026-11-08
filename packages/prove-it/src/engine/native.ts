// The native engine: the N-API addon that native/crates/prove-it-napi builds. The npm package finds
// it in the optional package for its platform, and the executables embed it. It declines every
// model for now, so the TypeScript engine checks them all.

import { getEngineAddon } from "./settings";

interface NativeAddon {
  abiVersion: () => number;
  check: (ir: Uint8Array) => NativeOutcome;
}

export interface NativeOutcome {
  status: "unavailable" | "declined";
  reason: string;
}

// The contract between this loader and the addon, ABI_VERSION in its lib.rs.
const ABI_VERSION = 1;

export const ADDON_FILE = "prove-it-engine.node";

// The executables build-binary.ts compiles define PROVE_IT_BINARY, and embed the addon beside the
// CLI when their build had one.
declare const PROVE_IT_BINARY: boolean | undefined;
const isBinary = typeof PROVE_IT_BINARY === "boolean" && PROVE_IT_BINARY;

// The platform packages scripts/platform-packages.ts packs. Linux has one for glibc and one for
// musl, and a package manager installs only the one for the libc it runs on.
const getPackages = () =>
  (process.platform === "linux"
    ? ["-gnu", "-musl"]
    : process.platform === "win32"
      ? ["-msvc"]
      : [""]
  ).map((suffix) => `@atemp/prove-it-${process.platform}-${process.arch}${suffix}`);

const resolveAddon = (name: string) => {
  try {
    return new URL(import.meta.resolve(`${name}/${ADDON_FILE}`));
  } catch {
    return undefined;
  }
};

// The addon PROVE_IT_ENGINE_ADDON names, the one an executable embeds, or the one in the platform
// package installed. process.getBuiltinModule would take Bun a millisecond or two to load node:url,
// so a file URL becomes a path by hand; on Windows its path starts with a slash before the drive.
const getAddonPath = () => {
  const override = getEngineAddon();
  if (override !== undefined) return override;
  const url = isBinary
    ? new URL(`./${ADDON_FILE}`, import.meta.url)
    : getPackages().reduce<URL | undefined>(
        (found, name) => found ?? resolveAddon(name),
        undefined,
      );
  if (url === undefined) return undefined;
  const path = decodeURIComponent(url.pathname);
  return process.platform === "win32" ? path.slice(1) : path;
};

const loadAddon = (): NativeAddon | string => {
  const addonPath = getAddonPath();
  if (addonPath === undefined) return `no ${getPackages().join(" or ")}`;
  const module = { exports: {} };
  try {
    process.dlopen(module, addonPath);
  } catch (error) {
    return `can't load ${addonPath}: ${error instanceof Error ? error.message : String(error)}`;
  }
  const addon = module.exports as NativeAddon;
  const version = addon.abiVersion();
  return version === ABI_VERSION
    ? addon
    : `${addonPath} has ABI version ${version}, not ${ABI_VERSION}`;
};

const loaded: { addon?: NativeAddon | string } = {};

// Loads the addon on first use. The TypeScript engine checks what it declines, and everything when
// it can't be loaded.
export const checkNatively = (): NativeOutcome => {
  loaded.addon ??=
    typeof globalThis.process?.dlopen === "function" ? loadAddon() : "no process.dlopen";
  return typeof loaded.addon === "string"
    ? { status: "unavailable", reason: loaded.addon }
    : loaded.addon.check(new Uint8Array(0));
};
