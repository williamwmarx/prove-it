import { describe, it } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import { expectDeclined } from "../native-check";

const DIRECTORY = join(import.meta.dirname, "../fixtures/tlc-set");

const TLC_GET = "an assumption that fails to evaluate: evaluating the assumption again: TLCGet";

describe("TLCGet revision and configuration", () => {
  it.each(["TLCSet", "TLCSetPost"])("declines TLC's TLCSet test with %s.cfg", async (name) => {
    await expectDeclined(
      {
        source: readFileSync(join(DIRECTORY, "TLCSet.tla"), "utf8"),
        config: `${readFileSync(join(DIRECTORY, `${name}.cfg`), "utf8")}\nCHECK_DEADLOCK FALSE\n`,
      },
      TLC_GET,
    );
  });

  it('declines TLCGet("revision")', async () => {
    const fields = ["calver", "count", "date", "tag", "timestamp"];
    await expectDeclined(
      {
        source: `---- MODULE M ----\nEXTENDS TLC\nASSUME DOMAIN TLCGet("revision") = {${fields.map((field) => `"${field}"`).join(", ")}}\n${fields.map((field) => `ASSUME PrintT(TLCGet("revision").${field})`).join("\n")}\nASSUME PrintT(TLCGet("config").install)\n====`,
        config: "",
      },
      TLC_GET,
    );
  });
});
