// testdata/statement: the statements statement.ts reads from each fixture theory, and the
// outcomes of the cases below, rendered as the Rust test renders them.
import { TlaIsabelleError } from "../../src/errors";
import { parseProp } from "../../src/prover/isabelle/isar/inner-syntax";
import { readStatement } from "../../src/prover/isabelle/isar/statement";
import { parseTheory } from "../../src/prover/isabelle/isar/theory";
import { checkProps } from "../../src/prover/isabelle/isar/type-check";
import { mkTFree, mkType, type Term } from "../../src/prover/isabelle/pure/term";
import { loadLogic } from "../../src/prover/isabelle/tla/logic";
import { escape, getFixtureNames, joinLines, readFixture, showTerm } from "./terms";

const show = (term: Term) => showTerm(term, ". ");

const outcome = (run: () => string[]) => {
  try {
    return run();
  } catch (error) {
    if (error instanceof TlaIsabelleError) return [`${error.exception}: ${error.message}`];
    throw error;
  }
};

const render = (text: string) =>
  outcome(() => {
    const theory = parseTheory(text);
    const statement = readStatement(loadLogic(), theory);
    const assumes = theory.elements.filter((element) => element.kind === "assumes");
    return [
      ...theory.elements.map((element) =>
        element.kind === "fixes" ? `fixes ${element.names.join(" ")}` : `assumes ${element.name}`,
      ),
      ...statement.assumptions.map(
        (term, index) => `assumption ${assumes[index].name}: ${show(term)}`,
      ),
      `conclusion: ${show(statement.conclusion)}`,
    ];
  });

const lemma = (body: string, consts = "") =>
  `theory T imports Constant Zenon begin\n${consts}lemma L: ${body} (is "PROP ?G") proof - show "PROP ?G" by auto qed end`;

const THEORIES = [
  lemma(`shows "P(%x. x(x))"`),
  lemma(`shows "P(%x. Q(x, x(y)))"`),
  lemma(`shows "P(%x y. x) & Q(%z. z) & R(z)"`),
  lemma(`assumes h: "P(%x. x)" shows "P(%x::c. x)"`),
  lemma(`assumes h: "P(%x. x)" shows "P(%x. x) & Q(%x. x)"`),
  lemma(`assumes h: "x" shows "x(y)"`),
  lemma(`fixes x assumes h: "x = y" shows "y \\<in> x"`),
  lemma(`fixes TRUE assumes h: "TRUE" shows "TRUE"`),
  lemma(`assumes h: "TRUE" fixes TRUE shows "TRUE = FALSE"`),
  lemma(`shows "f(x) = g"`, `consts "f" :: "[c] => c" "g" :: c\n`),
  lemma(`fixes f shows "f(x) = g"`, `consts "f" :: "[c] => c" "g" :: c\n`),
  lemma(`shows "f"`, `consts "f" :: "[c] => c"\n`),
  lemma(`shows "f"`, `consts "f" :: "[c, => c"\n`),
  lemma(`shows "(%x. x) = (%y. y)"`),
  lemma(`shows "(%x y z. y) = (%x. %y. x)"`),
  lemma(`shows "P(%x. x)"`),
  lemma(`shows "a ~= b"`),
  lemma(`shows "a \\<notin> S"`),
  lemma(`shows "x \\<in> BOOLEAN"`),
  lemma(`shows "(\\<lambda>x::c. x) = (\\<lambda>x::prop. x)"`),
  lemma(`shows "(x::prop)"`),
  lemma(`shows "x = "`),
  lemma(`shows "x" assumes h: "y"`),
];

const CHECKS = ["f", "g(f)", "g(x)", "g(g)", "x(g(x), y)", "x(x)", "P(%x. x)", "y = y"];
const getScope = () => ({
  consts: new Map([
    ["PredicateLogic.Trueprop", loadLogic().consts.get("PredicateLogic.Trueprop")!],
    [
      "T.g",
      {
        type: mkType("fun", [mkTFree("'a"), mkTFree("'a")]),
        typargs: [],
        abbreviation: undefined,
      },
    ],
  ]),
  constNames: new Map([
    ["f", "T.f"],
    ["g", "T.g"],
  ]),
});

export const getStatementExpectations = () => {
  const scope = getScope();
  return {
    ...Object.fromEntries(
      getFixtureNames().map((name) => [
        `statement/${name}.txt`,
        joinLines(render(readFixture(name))),
      ]),
    ),
    "statement/cases.txt": joinLines([
      ...THEORIES.flatMap((text) => [`theory\t${escape(text)}`, ...render(text)]),
      ...CHECKS.flatMap((text) => [
        `check\t${escape(text)}`,
        ...outcome(() => checkProps(scope, [{ ast: parseProp(text), fixed: new Set() }]).map(show)),
      ]),
    ]),
  };
};
