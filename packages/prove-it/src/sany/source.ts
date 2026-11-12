import type { Module } from "../ast";
import { TlaSyntaxError } from "../errors";
import { readAtAsIdentifier, type Token, tokenize } from "../lexer";
import { parseSanyModule } from "../parser";
import type { TlcVersion } from "../tlc/version";
import { getTabStop } from "./lexer";
import { getSanyParseError } from "./parse-error";

// The offset of a line's column in the source, as SANY counts a tab to the next tab stop.
const getOffset = (source: string, lineOffsets: number[], line: number, column: number) => {
  let width = 0;
  let offset = lineOffsets[line];
  while (offset < source.length) {
    width = source[offset] === "\t" ? getTabStop(width) : width + 1;
    if (width >= column) return offset;
    offset++;
  }
  return offset;
};

// SANY lexes []ASSUME and []PROVE as single tokens.
const isBoxToken = (tokens: Token[], index: number) => {
  const box = tokens[index];
  const next = tokens[index + 1];
  return (
    box?.kind === "Operator" &&
    box.text === "[]" &&
    next?.kind === "Keyword" &&
    (next.text === "ASSUME" || next.text === "PROVE") &&
    next.line === box.line &&
    next.column === box.endColumn + 1
  );
};

// HACK: the tla-ts parser has no []ASSUME or []PROVE, so it parses the source with each such []
// blanked out, which keeps every other token where it was. SANY's parser takes them only in an
// ASSUME/PROVE, which unboxing hides. Such a [] comes right before its keyword, so a source that
// never spells one has nothing to blank out.
const getUnboxedSource = (source: string, version?: TlcVersion) => {
  if (!/(?:\[\]|□)(?:ASSUME|PROVE)/.test(source)) return source;
  const tokens = tokenize(source)
    .filter((token) => token.kind !== "End")
    .map(readAtAsIdentifier);
  const lineOffsets = [0, 0];
  for (let index = 0; index < source.length; index++) {
    if (source[index] === "\n") lineOffsets.push(index + 1);
  }
  const unboxed = tokens.reduce((text, token, index) => {
    if (!isBoxToken(tokens, index)) return text;
    const offset = getOffset(source, lineOffsets, token.line, token.column);
    return `${text.slice(0, offset)}  ${text.slice(offset + 2)}`;
  }, source);
  if (unboxed !== source && getSanyParseError(source, version) !== undefined) {
    throw new TlaSyntaxError("SANY rejects a []ASSUME or []PROVE outside an ASSUME/PROVE");
  }
  return unboxed;
};

// What SANY's parser reads from a module's text: the text's tokens and its module, or the syntax
// error that stops the parser. TLC's order and environment read each text once.
export interface SanyReading {
  tokens: Token[];
  module: Module | TlaSyntaxError;
  // Whether the parser read the text without the boxes of []ASSUME and []PROVE, so the module is
  // not the one of the text's tokens.
  isUnboxed: boolean;
}

// A run reads its texts as SANY in one version of TLC does.
export const readSanyText = (
  readings: Map<string, SanyReading>,
  text: string,
  version?: TlcVersion,
) => {
  const known = readings.get(text);
  if (known) return known;
  // HACK: the parser reports a syntax error by throwing it, and every reader of the text gets it.
  const read = (): SanyReading => {
    try {
      const tokens = tokenize(text);
      const unboxed = getUnboxedSource(text, version);
      const isUnboxed = unboxed !== text;
      return {
        tokens,
        module: parseSanyModule(unboxed, isUnboxed ? undefined : tokens, version),
        isUnboxed,
      };
    } catch (error) {
      if (!(error instanceof TlaSyntaxError)) throw error;
      return { tokens: [], module: error, isUnboxed: false };
    }
  };
  const reading = read();
  readings.set(text, reading);
  return reading;
};
