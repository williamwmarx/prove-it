import { afterAll, expect, it } from "bun:test";
import { spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, realpathSync, rmSync, symlinkSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const CLI = join(import.meta.dirname, "../../src/cli.ts");

const root = realpathSync(mkdtempSync(join(tmpdir(), "prove-it-library-links-")));

afterAll(() => rmSync(root, { recursive: true, force: true }));

const writeModule = (path: string, name: string, value: number) =>
  writeFileSync(path, `---- MODULE ${name} ----\n${name}Val == ${value}\n====\n`);

it.each(["Spec", "Spec.tla"])(
  "names a module reached through a link by its real path and the path through the link, as TLC does, for %s",
  (spec) => {
    const directory = join(root, spec);
    mkdirSync(join(directory, "real lib"), { recursive: true });
    mkdirSync(join(directory, "other lib"));
    mkdirSync(join(directory, "links"));
    mkdirSync(join(directory, "spec"));
    writeModule(join(directory, "real lib", "Lib.tla"), "Lib", 1);
    writeModule(join(directory, "real lib", "Other.tla"), "Other", 2);
    writeModule(join(directory, "real lib", "Linked.tla"), "Linked", 3);
    writeModule(join(directory, "other lib", "Far.tla"), "Far", 4);
    writeModule(join(directory, "spec", "Near.tla"), "Near", 5);
    writeFileSync(
      join(directory, "spec", "Spec.tla"),
      "---- MODULE Spec ----\nEXTENDS Naturals, Lib, Other, Far, Near, Linked\nVARIABLE x\nInit == x = LibVal + OtherVal + FarVal + NearVal + LinkedVal\nNext == UNCHANGED x\n====\n",
    );
    writeFileSync(join(directory, "spec", "Spec.cfg"), "INIT Init\nNEXT Next\n");
    symlinkSync(join(directory, "real lib", "Lib.tla"), join(directory, "links", "Lib.tla"));
    symlinkSync(join(directory, "real lib", "Linked.tla"), join(directory, "spec", "Linked.tla"));
    symlinkSync(join(directory, "real lib"), join(directory, "dir link"));
    symlinkSync(join(directory, "other lib"), join(directory, "L﻿"));
    const result = spawnSync(
      "bun",
      [
        CLI,
        `-DTLA-Library=${directory}/links:${directory}/dir link:${directory}/L﻿`,
        "tlc2.TLC",
        spec,
      ],
      { cwd: join(directory, "spec"), encoding: "utf8" },
    );
    // TLC at 2026.11.11, run with LC_ALL=C.UTF-8 on the same files, prints these lines with
    // <directory> in place of the directory.
    const parsed = result.stdout
      .split("\n")
      .filter((line) => line.startsWith(`Parsing file ${directory}`));
    expect(parsed).toEqual([
      `Parsing file ${directory}/spec/Spec.tla`,
      `Parsing file ${directory}/real lib/Lib.tla (file:${directory}/links/Lib.tla)`,
      `Parsing file ${directory}/real lib/Other.tla (file:${directory}/dir%20link/Other.tla)`,
      `Parsing file ${directory}/other lib/Far.tla (file:${directory}/L﻿/Far.tla)`,
      `Parsing file ${directory}/spec/Near.tla`,
      `Parsing file ${directory}/real lib/Linked.tla (file:${directory}/spec/Linked.tla)`,
    ]);
    expect(result.stdout).toContain("Model checking completed. No error has been found.");
  },
);

it.each([
  ["", ""],
  [".", " (file:<directory>/./M.tla)"],
])(
  "finds a module in the library directory %p, the working directory, as TLC does",
  (library, suffix) => {
    const directory = join(root, `library-${library === "" ? "empty" : "dot"}`);
    mkdirSync(join(directory, "spec"), { recursive: true });
    writeModule(join(directory, "M.tla"), "M", 1);
    writeFileSync(
      join(directory, "spec", "Spec.tla"),
      "---- MODULE Spec ----\nEXTENDS Naturals, M\nVARIABLE x\nInit == x = MVal\nNext == UNCHANGED x\n====\n",
    );
    writeFileSync(join(directory, "spec", "Spec.cfg"), "INIT Init\nNEXT Next\n");
    const result = spawnSync(
      "bun",
      [CLI, `-DTLA-Library=${library}`, "tlc2.TLC", join(directory, "spec", "Spec.tla")],
      { cwd: directory, encoding: "utf8" },
    );
    // TLC at 2026.11.11 prints these lines on the same files.
    const parsed = result.stdout
      .split("\n")
      .filter((line) => line.startsWith(`Parsing file ${directory}`));
    expect(parsed).toEqual([
      `Parsing file ${directory}/spec/Spec.tla`,
      `Parsing file ${directory}/M.tla${suffix.replace("<directory>", directory)}`,
    ]);
    expect(result.stdout).toContain("Model checking completed. No error has been found.");
  },
);

it("finds the modules of a spec it found on the library path in the working directory first, as TLC does", () => {
  const directory = join(root, "library-spec");
  mkdirSync(join(directory, "lib"), { recursive: true });
  writeModule(join(directory, "M.tla"), "M", 1);
  writeFileSync(
    join(directory, "lib", "Spec.tla"),
    "---- MODULE Spec ----\nEXTENDS Naturals, M\nVARIABLE x\nInit == x = MVal\nNext == UNCHANGED x\n====\n",
  );
  writeFileSync(join(directory, "lib", "Spec.cfg"), "INIT Init\nNEXT Next\n");
  const result = spawnSync("bun", [CLI, "-DTLA-Library=lib:.", "tlc2.TLC", "Spec"], {
    cwd: directory,
    encoding: "utf8",
  });
  // TLC at 2026.11.11 prints these lines on the same files.
  const parsed = result.stdout
    .split("\n")
    .filter((line) => line.startsWith(`Parsing file ${directory}`));
  expect(parsed).toEqual([
    `Parsing file ${directory}/lib/Spec.tla`,
    `Parsing file ${directory}/M.tla`,
  ]);
  expect(result.stdout).toContain("Model checking completed. No error has been found.");
});
