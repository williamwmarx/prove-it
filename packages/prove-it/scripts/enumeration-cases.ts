// The cases of the enumeration oracle (native/DESIGN.md 6.8): sets TLC keeps lazy, written in
// native/oracle/ValueOracle.java's tokens. TLC (enumerate q and s) and the native engine (replay
// enumerate) answer the elements in the order a quantifier binds them and the order x' \in S
// assigns them, as their TLC fingerprints.

// The strings the cases use, which every side interns first, in this order.
export const CASE_STRINGS = ["a", "b", "c"];

export const encodeText = (text: string) =>
  Array.from(text, (character) => character.charCodeAt(0).toString(16).padStart(4, "0")).join("");

// The requests ValueOracle.java and replay enumerate answer for the cases, after the strings.
export const toRequests = (cases: string[]) => [
  `strings ${CASE_STRINGS.map((text) => `s${encodeText(text)}`).join(" ")}`,
  ...cases.flatMap((tokens, index) => [
    `value ${tokens}`,
    `enumerate q ${index}`,
    `enumerate s ${index}`,
  ]),
];

// The answers to the enumerate requests of toRequests, two a case.
export const toCaseAnswers = (lines: string[]) =>
  lines.slice(1).filter((_, index) => index % 3 !== 0);
