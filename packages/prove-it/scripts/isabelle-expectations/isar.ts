// testdata/isar: what the TypeScript's outer and inner syntax parsers read from each fixture
// theory and from the cases below.
import { TlaIsabelleError } from "../../src/errors";
import { type Ast, parseProp, parseType } from "../../src/prover/isabelle/isar/inner-syntax";
import { parseTheory } from "../../src/prover/isabelle/isar/theory";
import type { Typ } from "../../src/prover/isabelle/pure/term";
import { escape, getFixtureNames, joinLines, readFixture } from "./terms";

const showTyp = (type: Typ): string =>
  type.kind !== "Type"
    ? `?${type.kind}`
    : type.name === "fun"
      ? `(${showTyp(type.args[0])} => ${showTyp(type.args[1])})`
      : type.args.length === 0
        ? type.name
        : `${type.name}(${type.args.map(showTyp).join(", ")})`;

const showAst = (node: Ast): string => {
  switch (node.kind) {
    case "name":
      return node.name;
    case "const":
      return `'${node.name}`;
    case "app":
      return `(${showAst(node.fun)} ${showAst(node.arg)})`;
    case "abs":
      return `(%${node.name}${node.type === undefined ? "" : `::${showTyp(node.type)}`}. ${showAst(node.body)})`;
    case "constrain":
      return `(${showAst(node.term)} :: ${showTyp(node.type)})`;
  }
};

const attempt = (run: () => string) => {
  try {
    return run();
  } catch (error) {
    if (!(error instanceof TlaIsabelleError)) throw error;
    return `${error.exception}: ${error.message}`;
  }
};

const dumpTheory = (text: string) => {
  const theory = parseTheory(text);
  const lines = [`theory ${theory.name}`];
  for (const constant of theory.consts)
    lines.push(
      `const ${escape(constant.name)} :: ${escape(constant.type)} = ${attempt(() => showTyp(parseType(constant.type)))}`,
    );
  for (const element of theory.elements)
    if (element.kind === "fixes") lines.push(`fixes ${element.names.join(" ")}`);
    else {
      lines.push(`assumes ${element.name}: ${escape(element.prop)}`);
      lines.push(`  = ${attempt(() => showAst(parseProp(element.prop)))}`);
    }
  lines.push(`shows ${escape(theory.shows)}`);
  lines.push(`  = ${attempt(() => showAst(parseProp(theory.shows)))}`);
  lines.push(`using assms ${theory.isUsingAssms}`);
  lines.push(
    `method ${theory.method.map((token) => `${token.kind}:${escape(token.text)}`).join(" ")}`,
  );
  return joinLines(lines);
};

const HEADER = "theory T imports Constant Zenon begin\n";
const BODY = 'lemma L: shows "x" (is "PROP ?G") proof - show "PROP ?G" by auto qed end';
const THEORIES = [
  HEADER + BODY,
  HEADER +
    'consts "f" :: "[c,c] => c" "g" :: c\n' +
    'lemma L: fixes a b c assumes h: "a" assumes k: "b \\" \\\\ \\<in>" shows "x" (is "PROP ?G") proof - show "PROP ?G" using assms by (auto simp: x) (simp add: y) qed end',
  HEADER + "(* a (* nested *) comment *)" + BODY,
  HEADER + "(* unterminated (* comment *)" + BODY,
  HEADER + 'lemma L: shows "unterminated',
  HEADER + 'lemma L: shows "x\\"',
  "theory",
  "theory T",
  "theory begin",
  'theory T imports begin lemma L: shows "x" (is "PROP ?G") proof - show "PROP ?G" by auto qed end',
  HEADER + 'lemma lemma: shows "x"',
  HEADER + 'lemma L shows "x"',
  HEADER + 'lemma L: fixes shows "x"',
  HEADER + 'lemma L: assumes "a" shows "x"',
  HEADER + 'lemma L: assumes h "a" shows "x"',
  HEADER + BODY + " end",
  HEADER + BODY.replace(" qed end", " qed"),
  HEADER + BODY.replace(" qed end", ""),
  HEADER + BODY.replace("proof -", "proof"),
  HEADER + BODY.replace("by auto", "using foo by auto"),
  HEADER + BODY.replace("by auto", "by"),
  HEADER + 'consts "f" : c ' + BODY,
  HEADER + 'consts "f" :: ' + BODY,
  HEADER + "consts " + BODY,
  HEADER + BODY.replace("by auto", "by auto\u00a0é\u2028x\u0085\ufeff+ λ 'a.b_c'"),
  HEADER + BODY.replace("by auto", "by (simp)[2]"),
  HEADER + BODY.replace('shows "x"', "shows x"),
  HEADER + BODY.replace('(is "PROP ?G")', "(is PROP)"),
  HEADER.replace("Constant", '"Constant"') + BODY,
  "\u00a0" + HEADER + BODY + "\n\ufeff",
  "\u0085" + HEADER + BODY,
];

const PROPS = [
  "a \\<in> S",
  "a \\<Longrightarrow> b \\<Longrightarrow> c",
  "(a \\<Longrightarrow> b) \\<Longrightarrow> c",
  "\\<And>x y. P(x, y) \\<Longrightarrow> Q",
  "\\<And>x :: c. P(x)",
  "\\<And>x :: c => c. x = y",
  "a = (\\<And>x. b)",
  "(a \\<Longrightarrow> b) = c",
  "a \\<and> b \\<or> c \\<Rightarrow> d \\<Leftrightarrow> e => f & g | h",
  "~a = b",
  "\\<not> ~ a",
  "a = b = c",
  "a \\<noteq> b \\<and> a \\<notin> S \\<and> S \\<subseteq> T",
  "S \\<union> T \\ U \\<inter> V @@ (a :> b) \\<times> X \\<times> Y",
  "f[x][y] = g(a)(b, c)",
  "f(a)[b](c)",
  "f[x](y)",
  "x :: c",
  "(x :: c) = y",
  "x = y :: c",
  "x = (y :: c => c)",
  "{}",
  "{} = {a}",
  "{a, b, c}",
  "{a, b, c}[x]",
  "{}[x]",
  "<<>> = <<a>> & <<a, b>> = \\<langle>c, d\\<rangle>",
  "\\<langle>\\<rangle>",
  "[x \\<in> S \\<mapsto> x]",
  "[x \\<in> S \\<mapsto> x][y]",
  "[S \\<rightarrow> T]",
  "[f EXCEPT ![a] = b, ![c] = d]",
  "[f EXCEPT ![a] = b]",
  "[a : b, c : d]",
  "[a : b, c : d][e]",
  "[a]",
  "[x \\<in> S : x]",
  "\\<forall>x, y : P(x, y)",
  "\\<exists>x \\<in> S : P(x)",
  "\\<forall>x, y \\<in> S : x = y",
  "\\<forall>x : \\<exists>y : x = y",
  "a = (\\<forall>x : x)",
  "a = \\<forall>x : x",
  "%x y. f(x, y)",
  "\\<lambda>x::c. x",
  "(%x. x) = y",
  "a = %x. x",
  "f(%x. x)",
  "SUBSET S = UNION T & DOMAIN f = {}",
  "SUBSET SUBSET S",
  "a = SUBSET S",
  "~ a = ~ b",
  "a & ~ b",
  "''abc'' = ''''",
  "''a b'' = x",
  "''\\<in>''",
  "''é''",
  "''abc",
  "0 = succ[0]",
  "PROP P",
  "a b",
  "f()",
  "f(a,)",
  "(a",
  "a)",
  "",
  "  ",
  "a =",
  "= a",
  "a é b",
  "a # bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
  "a = b (* c *)",
  "x.y = a.b.c' & a._b & a.1",
  "x'_y1 = z",
  "\\<in>",
  "\\<foo> a",
  "\\<1>",
  "\\<",
  "\\a",
  "EXCEPT",
  "a !",
  "\\<forall>x y : P",
  "\\<forall>x \\<in> S, y : P",
  "\\<forall> : P",
  "%. x",
  "\\<And>. x",
  "\\<And>x. y \\<Longrightarrow> z",
  "a \\<Longrightarrow> \\<And>x. y",
  "trailing input after this very long proposition ) more",
  "x :: c :: c",
  "x :: d",
  "x :: (c => c",
  "a\u00a0=\ufeffb",
  "a\u0085= b",
  "a\u2028=\u3000b",
  "\\<lambda>x. \\<And>y. z",
  "f[\\<And>y. z]",
  "a :: [c, c] => c",
  "a :: [c]",
  "a :: [c, prop] \\<Rightarrow> (c => prop)",
];

const TYPES = [
  "c",
  "prop",
  "[c,c] => c",
  "c => c => c",
  "(c => c) => c",
  "(c)",
  "[c]",
  "[c] => c",
  "[]",
  "d",
  "c c",
  "",
  "c \\<Rightarrow> prop",
  "[c, [c] => c] => c",
  "=> c",
  "'a",
];

export const getIsarExpectations = () => ({
  ...Object.fromEntries(
    getFixtureNames().map((name) => [
      `isar/${name}.dump`,
      attempt(() => dumpTheory(readFixture(name))),
    ]),
  ),
  "isar/cases.txt": joinLines([
    ...THEORIES.map(
      (text) =>
        `theory\t${escape(text)}\n${attempt(() => dumpTheory(text).trimEnd().replace(/\n/g, "\n  "))}`,
    ),
    ...PROPS.map((text) => `prop\t${escape(text)}\n${attempt(() => showAst(parseProp(text)))}`),
    ...TYPES.map((text) => `type\t${escape(text)}\n${attempt(() => showTyp(parseType(text)))}`),
  ]),
});
