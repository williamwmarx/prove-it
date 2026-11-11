// testdata/blast/term.txt: what provers/blast/term.ts does to the classical rules of
// Isabelle/TLA+.
import {
  addTermVars,
  blastAconv,
  blastSubstBound,
  type BlastTerm,
  destConstApp,
  FALSE_NAME,
  fromTerm,
  hasLooseBound0,
  incrBlastBoundvars,
  instantiateTemplate,
  insTerm,
  isGoal,
  mkBlastAbs,
  mkBlastApp,
  mkBlastBound,
  mkBlastConst,
  mkBlastFree,
  mkBlastSkolem,
  mkBlastVar,
  mkGoal,
  norm,
  sameVars,
  stripBlastImpConcl,
  stripBlastImpPrems,
  toTemplate,
  toTerm,
  varOccur,
  type VarRef,
  varsInVars,
  wkNorm,
} from "../../src/prover/isabelle/provers/blast/term";
import type { Term } from "../../src/prover/isabelle/pure/term";
import { loadLogic } from "../../src/prover/isabelle/tla/logic";
import { joinLines, showTerm } from "./terms";

const TRUEPROP = "PredicateLogic.Trueprop";

const show = (term: Term) => showTerm(term, ". ");

export const getBlastTermExpectations = () => {
  const logic = loadLogic();
  const lines: string[] = [];
  const rules = [
    ...logic.claset.safeIs,
    ...logic.claset.safeEs,
    ...logic.claset.unsafeIs,
    ...logic.claset.unsafeEs,
  ];
  for (const [number, rule] of rules.entries()) {
    // Every third rule keeps the expectations small.
    if (number % 3 !== 0) continue;
    // Variables are labelled in the order the rule's lines first show them.
    const labels: VarRef[] = [];
    const label = (ref: VarRef) => {
      if (!labels.includes(ref)) labels.push(ref);
      return `?${labels.indexOf(ref)}`;
    };
    const print = (term: BlastTerm): string => {
      switch (term.kind) {
        case "Const":
          return term.typargs.length === 0
            ? term.name
            : `${term.name}{${term.typargs.map(print).join(",")}}`;
        case "Skolem":
          return `S:${term.name}[${term.args.map(label).join(",")}]`;
        case "Free":
          return `F:${term.name}`;
        case "Var":
          return term.ref.value === undefined
            ? label(term.ref)
            : `${label(term.ref)}=${print(term.ref.value)}`;
        case "Bound":
          return `B${term.index}`;
        case "Abs":
          return `(%${term.name}. ${print(term.body)})`;
        case "App":
          return `(${print(term.fun)} ${print(term.arg)})`;
      }
    };
    const flag = (value: boolean) => (value ? "1" : "0");
    const out = (key: string, value: string) => lines.push(`${number} ${key}: ${value}`);

    const term = fromTerm(logic.consts, rule.rule.prop);
    out("from", print(term));
    const vars = addTermVars(term, []);
    out("vars", vars.map(label).join(" "));
    const prems = stripBlastImpPrems(TRUEPROP, term);
    const concl = stripBlastImpConcl(TRUEPROP, term);
    out("prems", String(prems.length));
    out("concl", print(concl));
    out("toTerm", `${show(toTerm(3, term))} ${show(toTerm(2, concl))}`);
    out("goal", `${flag(isGoal(mkGoal(concl)))}${flag(isGoal(concl))}`);

    const refs: VarRef[] = [];
    const template = toTemplate(refs, [], term);
    const fresh = refs.map(() => mkBlastVar({ value: undefined }));
    const instance = instantiateTemplate(fresh, [], template);
    out(
      "aconv",
      `${flag(blastAconv(term, instance))}${flag(blastAconv(instance, instance))}${flag(term === instance)}`,
    );
    if (concl.kind === "Var") {
      concl.ref.value = mkBlastConst(FALSE_NAME);
      out("norm", print(norm(term)));
    }
    out(
      "occurs",
      vars.map((ref) => flag(varOccur(ref, term))).join("") +
        " " +
        fresh
          .map((variable) =>
            variable.kind === "Var" ? flag(varOccur(variable.ref, instance)) : "-",
          )
          .join(""),
    );

    // Instantiates each fresh variable with a Skolem term over the later ones.
    const freshRefs = fresh.flatMap((variable) => (variable.kind === "Var" ? [variable.ref] : []));
    for (const [index, ref] of freshRefs.entries())
      if (index % 2 === 0) ref.value = mkBlastSkolem(`S${index}`, freshRefs.slice(index + 1));
    const normal = norm(instance);
    out("instantiated", print(normal));
    const remaining = varsInVars(freshRefs);
    out(
      "remaining",
      `${remaining.map(label).join(" ")} ${flag(sameVars(remaining, freshRefs))}${flag(sameVars(freshRefs, freshRefs))} ${addTermVars(instance, []).map(label).join(" ")}`,
    );
    out("renorm", flag(norm(normal) === normal));

    for (const prem of stripBlastImpPrems(TRUEPROP, normal)) {
      let current = prem;
      let body = destConstApp(current, "Pure.all");
      while (body?.kind === "Abs") {
        current = blastSubstBound(mkBlastSkolem("K", remaining), body.body);
        body = destConstApp(current, "Pure.all");
      }
      if (current !== prem) out("skolemized", print(norm(current)));
    }

    const abstractions: BlastTerm[] = [];
    const collect = (current: BlastTerm) => {
      if (current.kind === "Abs") abstractions.push(current);
      if (current.kind === "Abs") collect(current.body);
      if (current.kind === "App") {
        collect(current.fun);
        collect(current.arg);
      }
    };
    collect(term);
    for (const abs of abstractions.slice(0, 1)) {
      const redex = mkBlastApp(abs, mkBlastFree("a"));
      out("beta", `${print(wkNorm(redex))} ${flag(blastAconv(wkNorm(redex), norm(redex)))}`);
      const eta = mkBlastAbs("e", mkBlastApp(incrBlastBoundvars(1, abs), mkBlastBound(0)));
      out(
        "eta",
        `${print(wkNorm(eta))} ${flag(hasLooseBound0(abs.kind === "Abs" ? abs.body : abs))}`,
      );
      const nested = mkBlastApp(
        mkBlastApp(mkBlastAbs("u", abs), mkBlastBound(2)),
        mkBlastFree("b"),
      );
      out("nested", print(norm(nested)));
    }
    const chased = mkBlastAbs(
      "e",
      mkBlastApp(mkBlastVar({ value: incrBlastBoundvars(1, concl) }), mkBlastBound(0)),
    );
    out("eta2", `${print(wkNorm(chased))} ${print(norm(chased))}`);
    out(
      "ins",
      `${insTerm(concl, prems).length} ${prems.length === 0 ? "-" : insTerm(prems[0], prems).length}`,
    );
  }
  return { "blast/term.txt": joinLines(lines) };
};
