//! Ported from Isabelle2025's Pure/Isar/method.ML (method syntax, combinators, SIMPLE_METHOD,
//! finish), the assume_rule_tac and norm_hhf_tac of Pure/goal.ML, and the methods the theories
//! tlapm writes use: auto, force and clarsimp (Provers/clasimp.ML), blast (Provers/blast.ML),
//! iprover (Tools/intuitionistic.ML) and intro. Copyright (c) 1986-2025 University of Cambridge,
//! Technische Universitaet Muenchen, and contributors, see LICENSE.
//!
//! (`isar/method.ts`.) A method applied to its facts may raise (an undefined fact, a rule a
//! modifier rejects) before it is given a goal, so it returns a `Res<Tactic>`. The tactics that
//! build a simpset (norm_hhf_tac) are built once per proof rather than at each goal: building
//! one takes no step.

use std::rc::Rc;

use crate::error::{Error, Res, error_exn};
use crate::provers::clasimp::{BlastDepthTac, ClasimpContext, auto_tac, clarsimp_tac, force_tac};
use crate::provers::classical::{
    ClassicalContext, add_unsafe_dest, add_unsafe_intro, fast_tac, with_claset,
};
use crate::pure::drule::{asm_rl, is_norm_hhf, multi_resolves, norm_hhf_eq, reflexive_thm, term_i};
use crate::pure::logic::{is_equals, strip_assums_concl, strip_imp_prems};
use crate::pure::name::variant_list;
use crate::pure::object_logic::atomize_prems_tac;
use crate::pure::raw_simplifier::{SimpContext, Simpset, add_simps, empty_simpset};
use crate::pure::rewriter::{RewriteMode, generic_rewrite_goal_tac};
use crate::pure::seq::{Seq, filter_seq, maps_seq, single_seq};
use crate::pure::simplifier::{asm_full_simp_tac, norm_hhf};
use crate::pure::tactic::{assume_tac, eresolve_tac, flexflex_tac, match_tac, resolve_tac};
use crate::pure::tactical::{
    GoalTactic, Tactic, all_goals, all_tac, append_goal, changed_prop, no_tac, or_else,
    repeat_all_new, subgoal, then_all_new, then_goal, then_tac,
};
use crate::pure::term::{
    Name, Term, add_free_names, maxidx_of_term, mk_var, strip_all_body, strip_all_vars,
    subst_bounds,
};
use crate::pure::thm::{Thm, nprems, trivial};
use crate::tools::intuitionistic::{IntuitionisticContext, prover_tac};

use super::proof::insert_tac;
use super::theory::{OuterToken, OuterTokenKind};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ModifierKind {
    Intro,
    Dest,
    /// `simp:` and `simp add:` of the clasimp methods, `add:` of simp.
    Simp,
}

/// The modifiers a method's Method.sections takes: Classical.cla_modifiers, Clasimp's
/// clasimp_modifiers, Simplifier.simp_modifiers'.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Sections {
    Classical,
    Clasimp,
    Simp,
}

/// The methods Isabelle/Pure and the provers of Isabelle/TLA+'s session define that the port has
/// no tactic for: a theory that names one declines, where any other name is Isabelle's error.
const KNOWN_METHODS: &[&str] = &[
    "-",
    "assumption",
    "atomize",
    "best",
    "bestsimp",
    "cases",
    "clarify",
    "coinduct",
    "contradiction",
    "cut_tac",
    "deepen",
    "drule",
    "drule_tac",
    "elim",
    "erule",
    "erule_tac",
    "fact",
    "fail",
    "fastforce",
    "fold",
    "frule",
    "frule_tac",
    "goal_cases",
    "hypsubst",
    "hypsubst_thin",
    "induct",
    "induction",
    "insert",
    "inst_step",
    "intro_classes",
    "intro_locales",
    "rename_tac",
    "rotate_tac",
    "rule_tac",
    "safe",
    "safe_step",
    "simp_all",
    "simplesubst",
    "sleep",
    "slow",
    "slow_step",
    "slowsimp",
    "split",
    "standard",
    "step",
    "subgoal_tac",
    "subst",
    "succeed",
    "tactic",
    "raw_tactic",
    "thin_tac",
    "this",
    "unfold",
    "unfold_locales",
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Modifier {
    pub kind: ModifierKind,
    pub facts: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MethodText {
    Auto { modifiers: Vec<Modifier> },
    Blast { modifiers: Vec<Modifier> },
    Force { modifiers: Vec<Modifier> },
    Clarsimp { modifiers: Vec<Modifier> },
    Fast { modifiers: Vec<Modifier> },
    Simp { modifiers: Vec<Modifier> },
    Iprover,
    Intro { facts: Vec<String> },
    Rule { facts: Vec<String> },
    Then { methods: Vec<MethodText> },
    Try { method: Box<MethodText> },
}

/// The methods of by: the initial one, and the terminal one that qed runs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofText {
    pub initial: MethodText,
    pub terminal: Option<MethodText>,
}

/// What a proof method reads from the Isabelle proof context.
pub struct ProofContext {
    pub simpset: Simpset,
    pub classical: ClassicalContext,
    pub intuitionistic: IntuitionisticContext,
    pub atomize_rules: Vec<Thm>,
    pub blast_depth_tac: BlastDepthTac,
    pub blast_tac: Rc<dyn Fn(&ClassicalContext) -> Res<GoalTactic>>,
    pub get_fact: Rc<dyn Fn(&str) -> Res<Vec<Thm>>>,
}

fn syntax_error(token: Option<&OuterToken>) -> crate::error::Error {
    error_exn(format!(
        "Outer syntax error at: {}",
        token.map_or("end of input", |token| token.text.as_str())
    ))
}

/// Method.parse for the proof methods of by.
struct MethodParser<'tokens> {
    tokens: &'tokens [OuterToken],
    position: usize,
}

impl MethodParser<'_> {
    fn peek(&self) -> Option<&OuterToken> {
        self.tokens.get(self.position)
    }

    fn is_symbol(&self, symbol: &str, offset: usize) -> bool {
        self.tokens
            .get(self.position + offset)
            .is_some_and(|token| token.kind == OuterTokenKind::Symbol && token.text == symbol)
    }

    fn expect_symbol(&mut self, symbol: &str) -> Res<()> {
        if !self.is_symbol(symbol, 0) {
            return Err(syntax_error(self.peek()));
        }
        self.position += 1;
        Ok(())
    }

    fn is_word(&self) -> bool {
        self.peek()
            .is_some_and(|token| token.kind == OuterTokenKind::Word)
    }

    fn word(&mut self) -> Res<String> {
        match self.peek() {
            Some(token) if token.kind == OuterTokenKind::Word => {
                let text = token.text.clone();
                self.position += 1;
                Ok(text)
            }
            token => Err(syntax_error(token)),
        }
    }

    fn token_at(&self, at: usize) -> Option<&OuterToken> {
        self.tokens.get(at)
    }

    fn symbol_at(&self, at: usize, symbol: &str) -> bool {
        self.token_at(at)
            .is_some_and(|token| token.kind == OuterTokenKind::Symbol && token.text == symbol)
    }

    /// Method.sections: the length in tokens of the section header at `at` among those the
    /// method's sections parse (one or two words, `!` for a safe rule after them, then `:`), or 0
    /// where none starts there, so a fact named like a header's word is still a fact.
    fn header_length(&self, at: usize, sections: Sections) -> usize {
        let is_word = |offset: usize, word: &str| {
            self.token_at(at + offset)
                .is_some_and(|token| token.kind == OuterTokenKind::Word && token.text == word)
        };
        for header in section_headers(sections) {
            let words: Vec<&str> = header.split(' ').filter(|word| *word != "!").collect();
            if !words
                .iter()
                .enumerate()
                .all(|(offset, word)| is_word(offset, word))
            {
                continue;
            }
            let bang = usize::from(header.ends_with('!'));
            if bang == usize::from(self.symbol_at(at + words.len(), "!"))
                && self.symbol_at(at + words.len() + bang, ":")
            {
                return words.len() + bang + 1;
            }
        }
        0
    }

    /// Attrib.thms: fact names up to the next section of `sections`, if any. An attribute in
    /// brackets after a name, which the port doesn't apply, declines.
    fn facts(&mut self, sections: Option<Sections>) -> Res<Vec<String>> {
        let mut names = Vec::new();
        while self.is_word()
            && sections.is_none_or(|sections| self.header_length(self.position, sections) == 0)
        {
            names.push(self.word()?);
            if self.is_symbol("[", 0) {
                return Err(Error::Unsupported("Isabelle's fact attributes".into()));
            }
        }
        Ok(names)
    }

    fn modifiers(&mut self, sections: Sections) -> Res<Vec<Modifier>> {
        let mut result = Vec::new();
        loop {
            let length = self.header_length(self.position, sections);
            if length == 0 {
                return Ok(result);
            }
            let header = self.tokens[self.position..self.position + length - 1]
                .iter()
                .map(|token| token.text.as_str())
                .collect::<Vec<_>>()
                .join(" ");
            self.position += length;
            result.push(Modifier {
                kind: section_kind(sections, &header)?,
                facts: self.facts(Some(sections))?,
            });
        }
    }

    fn method(&mut self, name: &str, has_args: bool) -> Res<MethodText> {
        let modifiers = |parser: &mut Self, sections| {
            if has_args {
                parser.modifiers(sections)
            } else {
                Ok(Vec::new())
            }
        };
        let facts = |parser: &mut Self| {
            if has_args {
                parser.facts(None)
            } else {
                Ok(Vec::new())
            }
        };
        Ok(match name {
            "auto" => MethodText::Auto {
                modifiers: modifiers(self, Sections::Clasimp)?,
            },
            "blast" => MethodText::Blast {
                modifiers: modifiers(self, Sections::Classical)?,
            },
            "fast" => MethodText::Fast {
                modifiers: modifiers(self, Sections::Classical)?,
            },
            "force" => MethodText::Force {
                modifiers: modifiers(self, Sections::Clasimp)?,
            },
            "clarsimp" => MethodText::Clarsimp {
                modifiers: modifiers(self, Sections::Clasimp)?,
            },
            // Simplifier.simp_method: an option such as `(no_asm)` comes before the sections.
            "simp" => {
                if has_args && self.is_symbol("(", 0) {
                    return Err(Error::Unsupported(
                        "Isabelle's simp method with options".into(),
                    ));
                }
                MethodText::Simp {
                    modifiers: modifiers(self, Sections::Simp)?,
                }
            }
            "iprover" => MethodText::Iprover,
            "intro" => MethodText::Intro {
                facts: facts(self)?,
            },
            "rule" => MethodText::Rule {
                facts: facts(self)?,
            },
            _ if KNOWN_METHODS.contains(&name) => {
                return Err(Error::Unsupported(format!("Isabelle's {name} method")));
            }
            _ => return Err(error_exn(format!("Undefined method: {name}"))),
        })
    }

    fn suffixed(&mut self, text: MethodText) -> MethodText {
        if !self.is_symbol("?", 0) {
            return text;
        }
        self.position += 1;
        self.suffixed(MethodText::Try {
            method: Box::new(text),
        })
    }

    fn element(&mut self) -> Res<MethodText> {
        let text = if self.is_symbol("(", 0) {
            self.parenthesized()?
        } else {
            let name = self.word()?;
            self.method(&name, true)?
        };
        Ok(self.suffixed(text))
    }

    fn parenthesized(&mut self) -> Res<MethodText> {
        self.expect_symbol("(")?;
        let mut elements = vec![self.element()?];
        while self.is_symbol(",", 0) {
            self.position += 1;
            elements.push(self.element()?);
        }
        self.expect_symbol(")")?;
        Ok(if elements.len() == 1 {
            elements.remove(0)
        } else {
            MethodText::Then { methods: elements }
        })
    }

    fn atom(&mut self) -> Res<MethodText> {
        let text = if self.is_symbol("(", 0) {
            self.parenthesized()?
        } else {
            let name = self.word()?;
            self.method(&name, false)?
        };
        Ok(self.suffixed(text))
    }
}

/// The section headers a method's Method.sections parse, each as its words with ` !` for a safe
/// rule: Classical.cla_modifiers; Clasimp's clasimp_modifiers (the simp, split, cla and iff
/// modifiers); Simplifier.simp_modifiers' with the cong modifiers.
fn section_headers(sections: Sections) -> &'static [&'static str] {
    const CLA: &[&str] = &[
        "intro", "intro !", "elim", "elim !", "dest", "dest !", "del",
    ];
    const CLASIMP: &[&str] = &[
        "simp",
        "simp add",
        "simp del",
        "simp flip",
        "simp only",
        "cong",
        "cong add",
        "cong del",
        "split",
        "split add",
        "split del",
        "intro",
        "intro !",
        "elim",
        "elim !",
        "dest",
        "dest !",
        "del",
        "iff",
        "iff add",
        "iff !",
        "iff add !",
        "iff del",
    ];
    const SIMP: &[&str] = &["add", "del", "flip", "only", "cong", "cong add", "cong del"];
    match sections {
        Sections::Classical => CLA,
        Sections::Clasimp => CLASIMP,
        Sections::Simp => SIMP,
    }
}

/// The modifier a section's header declares: one the port applies as Isabelle does, or one
/// Isabelle takes and the port doesn't, which declines.
fn section_kind(sections: Sections, header: &str) -> Res<ModifierKind> {
    match (sections, header) {
        (Sections::Classical | Sections::Clasimp, "intro") => Ok(ModifierKind::Intro),
        (Sections::Classical | Sections::Clasimp, "dest") => Ok(ModifierKind::Dest),
        (Sections::Clasimp, "simp" | "simp add") | (Sections::Simp, "add") => {
            Ok(ModifierKind::Simp)
        }
        _ => Err(Error::Unsupported(format!(
            "Isabelle's method modifier {header}:"
        ))),
    }
}

pub fn parse_proof_text(tokens: &[OuterToken]) -> Res<ProofText> {
    let mut parser = MethodParser {
        tokens,
        position: 0,
    };
    let initial = parser.atom()?;
    let terminal = if parser.position < tokens.len() {
        Some(parser.atom()?)
    } else {
        None
    };
    if parser.position != tokens.len() {
        return Err(syntax_error(parser.peek()));
    }
    Ok(ProofText { initial, terminal })
}

fn get_facts(context: &ProofContext, names: &[String]) -> Res<Vec<Thm>> {
    let mut facts = Vec::new();
    for name in names {
        facts.extend((context.get_fact)(name)?);
    }
    Ok(facts)
}

/// Method.sections: the claset the modifiers declare.
fn with_modifiers(context: &ProofContext, modifiers: &[Modifier]) -> Res<ClassicalContext> {
    let mut classical = context.classical.clone();
    for modifier in modifiers {
        for fact in get_facts(context, &modifier.facts)? {
            let claset = match modifier.kind {
                ModifierKind::Intro => add_unsafe_intro(&classical, &fact)?,
                ModifierKind::Dest => add_unsafe_dest(&classical, &fact)?,
                ModifierKind::Simp => continue,
            };
            classical = with_claset(&classical, claset);
        }
    }
    Ok(classical)
}

/// Simplifier.simp_add for each fact of the `simp` modifiers, in order.
fn with_simps(context: &ProofContext, modifiers: &[Modifier]) -> Res<SimpContext> {
    let mut simp = SimpContext {
        simpset: context.simpset.clone(),
        bounds: 0,
    };
    for modifier in modifiers {
        if modifier.kind == ModifierKind::Simp {
            simp.simpset = add_simps(&simp, &get_facts(context, &modifier.facts)?)?;
        }
    }
    Ok(simp)
}

fn get_clasimp(context: &ProofContext, modifiers: &[Modifier]) -> Res<ClasimpContext> {
    Ok(ClasimpContext {
        classical: with_modifiers(context, modifiers)?,
        simp: with_simps(context, modifiers)?,
        blast_depth_tac: context.blast_depth_tac.clone(),
    })
}

/// Method.rule_tac: the rules, with their first premises resolved against the facts, resolve
/// against the goal, whose new goals are then normalized.
fn rule_tac(rules: Vec<Thm>, facts: Vec<Thm>) -> Res<GoalTactic> {
    let rules: Rc<[Thm]> = rules.into();
    let facts: Rc<[Thm]> = facts.into();
    Ok(then_all_new(
        Rc::new(move |index| {
            let rules = rules.clone();
            let facts = facts.clone();
            Rc::new(move |state: Thm| {
                if facts.is_empty() {
                    return resolve_tac(&rules)(index)(state);
                }
                Ok(maps_seq(
                    move |rule: Thm| resolve_tac(std::slice::from_ref(&rule))(index)(state.clone()),
                    multi_resolves(&facts, &rules),
                ))
            })
        }),
        norm_hhf_tac()?,
    ))
}

fn insert_all_tac(facts: &[Thm]) -> Tactic {
    let facts: Rc<[Thm]> = facts.into();
    all_goals(Rc::new(move |index| {
        let facts = facts.clone();
        Rc::new(move |state| insert_tac(&facts, index)?(state))
    }))
}

/// SIMPLE_METHOD'
fn simple_method_head(facts: &[Thm], tactic: GoalTactic) -> Res<Tactic> {
    Ok(then_tac(insert_tac(facts, 1)?, tactic(1)))
}

type Method = Rc<dyn Fn(&[Thm]) -> Res<Tactic>>;

fn evaluate(context: &Rc<ProofContext>, text: &MethodText) -> Method {
    let context = context.clone();
    match text.clone() {
        MethodText::Auto { modifiers } => Rc::new(move |facts| {
            let insert = insert_all_tac(facts);
            Ok(then_tac(
                insert,
                changed_prop(auto_tac(&get_clasimp(&context, &modifiers)?)?),
            ))
        }),
        // The TypeScript reads the modifiers once SIMPLE_METHOD' gives the tactic its goal, after
        // building insert_tac.
        MethodText::Clarsimp { modifiers } => Rc::new(move |facts| {
            let insert = insert_tac(facts, 1)?;
            let clasimp = get_clasimp(&context, &modifiers)?;
            Ok(then_tac(insert, changed_prop(clarsimp_tac(&clasimp)(1))))
        }),
        // Simplifier.simp_method with its default options: SIMPLE_METHOD' of CHANGED_PROP over
        // asm_full_simp_tac, in the simpset its `add:` sections extend.
        MethodText::Simp { modifiers } => Rc::new(move |facts| {
            let simp = with_simps(&context, &modifiers)?;
            simple_method_head(
                facts,
                Rc::new(move |index| changed_prop(asm_full_simp_tac(&simp)(index))),
            )
        }),
        MethodText::Force { modifiers } => Rc::new(move |facts| {
            let tactic = force_tac(&get_clasimp(&context, &modifiers)?, &context.atomize_rules)?;
            simple_method_head(facts, tactic)
        }),
        // Classical.cla_method' fast_tac.
        MethodText::Fast { modifiers } => Rc::new(move |facts| {
            let tactic = fast_tac(
                &with_modifiers(&context, &modifiers)?,
                &context.atomize_rules,
            )?;
            simple_method_head(facts, tactic)
        }),
        // Classical's rule method: METHOD (HEADGOAL o rule_tac ctxt rules), which without rules
        // is some_rule_tac over the context's rules, which the port doesn't search.
        MethodText::Rule { facts: names } => Rc::new(move |facts| {
            let rules = get_facts(&context, &names)?;
            if rules.is_empty() {
                return Err(Error::Unsupported(
                    "Isabelle's rule method without rules".into(),
                ));
            }
            Ok(rule_tac(rules, facts.to_vec())?(1))
        }),
        MethodText::Blast { modifiers } => Rc::new(move |facts| {
            let tactic = (context.blast_tac)(&with_modifiers(&context, &modifiers)?)?;
            simple_method_head(facts, tactic)
        }),
        MethodText::Iprover => Rc::new(move |facts| {
            let tactic = then_goal(
                atomize_prems_tac(&context.atomize_rules)?,
                prover_tac(&context.intuitionistic),
            );
            simple_method_head(facts, tactic)
        }),
        MethodText::Intro { facts: names } => Rc::new(move |facts| {
            let rules = get_facts(&context, &names)?;
            simple_method_head(
                facts,
                Rc::new(move |index| changed_prop(repeat_all_new(match_tac(&rules))(index))),
            )
        }),
        MethodText::Then { methods } => {
            let methods: Rc<[Method]> = methods
                .iter()
                .map(|method| evaluate(&context, method))
                .collect();
            Rc::new(move |facts| {
                let methods = methods.clone();
                let facts: Rc<[Thm]> = facts.into();
                Ok(Rc::new(move |state| {
                    let mut results = single_seq(state);
                    for method in methods.iter() {
                        let tactic = method(&facts)?;
                        results = maps_seq(move |result| tactic(result), results);
                    }
                    Ok(results)
                }))
            })
        }
        MethodText::Try { method } => {
            let method = evaluate(&context, &method);
            Rc::new(move |facts| Ok(or_else(method(facts)?, all_tac())))
        }
    }
}

/// Goal.norm_hhf_tac
fn norm_hhf_tac() -> Res<GoalTactic> {
    let empty = SimpContext {
        simpset: empty_simpset(),
        bounds: 0,
    };
    let context = SimpContext {
        simpset: add_simps(&empty, &[norm_hhf_eq()])?,
        ..empty
    };
    Ok(then_goal(
        resolve_tac(&[asm_rl()]),
        subgoal(move |goal, index| {
            Ok(if is_norm_hhf(false, goal) {
                all_tac()
            } else {
                generic_rewrite_goal_tac(
                    RewriteMode {
                        simprem: true,
                        useprem: false,
                        mutsimp: false,
                    },
                    Rc::new(|_, _| Ok(None)),
                    &context,
                    index,
                )
            })
        }),
    ))
}

/// Goal.assume_rule_tac: solves a goal with one of its non-atomic premises.
fn assume_rule_tac() -> Res<GoalTactic> {
    Ok(then_goal(
        norm_hhf_tac()?,
        subgoal(|goal, index| {
            // Variable.focus_cterm and Variable.export: the parameters become schematic
            // variables.
            let params = strip_all_vars(goal);
            let names = variant_list(
                &add_free_names(goal, Vec::new()),
                &params
                    .iter()
                    .map(|param| param.0.clone())
                    .collect::<Vec<Name>>(),
            );
            let maxidx = maxidx_of_term(goal, -1) + 1;
            let vars: Vec<Term> = params
                .iter()
                .enumerate()
                .map(|(offset, param)| mk_var(names[offset].clone(), maxidx, param.1.clone()))
                .rev()
                .collect();
            let body = subst_bounds(&vars, strip_all_body(goal));
            let rules: Vec<Term> = strip_imp_prems(&body)
                .into_iter()
                .filter(|prem| {
                    prem.dest_app().is_some_and(|(fun, _)| {
                        fun.dest_app()
                            .is_some_and(|(head, _)| head.is_const_named("Pure.imp"))
                            || fun.is_const_named("Pure.all")
                    })
                })
                .collect();
            let mut tactic: GoalTactic = Rc::new(|_| no_tac());
            for rule in rules.iter().rev() {
                tactic = append_goal(
                    then_all_new(eresolve_tac(&[norm_hhf(&trivial(rule)?)?]), assume_tac()),
                    tactic,
                );
            }
            Ok(tactic(index))
        }),
    ))
}

/// Method.assm_tac
fn assm_tac() -> Res<GoalTactic> {
    let cond_rtac = |is_rule: fn(&Term) -> bool, rule: Thm| {
        subgoal(move |goal, index| {
            Ok(if is_rule(strip_assums_concl(goal)) {
                resolve_tac(std::slice::from_ref(&rule))(index)
            } else {
                no_tac()
            })
        })
    };
    Ok(append_goal(
        assume_tac(),
        append_goal(
            assume_rule_tac()?,
            append_goal(
                cond_rtac(is_equals, reflexive_thm()),
                cond_rtac(
                    |concl| {
                        concl
                            .dest_app()
                            .is_some_and(|(fun, _)| fun.is_const_named("Pure.term"))
                    },
                    term_i(),
                ),
            ),
        ),
    ))
}

/// Method.all_assm_tac
fn all_assm_tac(assm: GoalTactic, index: i32) -> Tactic {
    Rc::new(move |state: Thm| {
        if index > nprems(&state) as i32 {
            return Ok(single_seq(state));
        }
        or_else(
            then_tac(assm(index), all_assm_tac(assm.clone(), index)),
            all_assm_tac(assm.clone(), index + 1),
        )(state)
    })
}

/// Proof.local_terminal_proof: by initial terminal runs the initial method with the facts, then
/// the terminal one without them and Method.finish, and succeeds on the first result that leaves
/// no goal.
pub fn terminal_proof(
    context: &Rc<ProofContext>,
    text: &ProofText,
    facts: &[Thm],
    state: Thm,
) -> Res<Seq<Thm>> {
    let initial = evaluate(context, &text.initial);
    let terminal = text
        .terminal
        .as_ref()
        .map(|terminal| evaluate(context, terminal));
    let assm = assm_tac()?;
    let finish: Tactic = Rc::new(move |result| {
        let flexflex = flexflex_tac();
        Ok(maps_seq(
            move |state| flexflex(state),
            all_assm_tac(assm.clone(), 1)(result)?,
        ))
    });
    let results = initial(facts)?(state)?;
    Ok(filter_seq(
        |result| Ok(nprems(result) == 0),
        maps_seq(
            move |result| {
                let finish = finish.clone();
                let terminated = match &terminal {
                    None => single_seq(result),
                    Some(terminal) => terminal(&[])?(result)?,
                };
                Ok(maps_seq(move |state| finish(state), terminated))
            },
            results,
        ),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::Exception;
    use crate::isar::theory::tokenize;

    fn parse(text: &str) -> Res<MethodText> {
        Ok(parse_proof_text(&tokenize(text)?)?.initial)
    }

    fn modifier(kind: ModifierKind, facts: &[&str]) -> Modifier {
        Modifier {
            kind,
            facts: facts.iter().map(|fact| (*fact).to_owned()).collect(),
        }
    }

    // Method.sections of each method: a fact named like a header's word stays a fact, and a
    // header another method's sections take is no section of this one.
    #[test]
    fn parses_the_sections_each_method_takes() {
        assert_eq!(
            parse("(auto intro: conjI dest: conjunct1)").unwrap(),
            MethodText::Auto {
                modifiers: vec![
                    modifier(ModifierKind::Intro, &["conjI"]),
                    modifier(ModifierKind::Dest, &["conjunct1"]),
                ]
            }
        );
        assert_eq!(
            parse("(auto simp add: add dest intro: dest)").unwrap(),
            MethodText::Auto {
                modifiers: vec![
                    modifier(ModifierKind::Simp, &["add", "dest"]),
                    modifier(ModifierKind::Intro, &["dest"]),
                ]
            }
        );
        assert_eq!(
            parse("(simp add: simp cong)").unwrap(),
            MethodText::Simp {
                modifiers: vec![modifier(ModifierKind::Simp, &["simp", "cong"])]
            }
        );
        assert_eq!(
            parse("(rule chooseI dest)").unwrap(),
            MethodText::Rule {
                facts: vec!["chooseI".into(), "dest".into()]
            }
        );
        assert_eq!(
            parse("(fast intro: conjI)").unwrap(),
            MethodText::Fast {
                modifiers: vec![modifier(ModifierKind::Intro, &["conjI"])]
            }
        );
        assert_eq!(
            parse("(simp)").unwrap(),
            MethodText::Simp {
                modifiers: Vec::new()
            }
        );
    }

    #[test]
    fn declines_what_isabelle_takes_and_the_port_does_not() {
        for text in [
            "(auto elim: conjE)",
            "(auto intro!: conjI)",
            "(auto simp del: x)",
            "(simp only: x)",
            "(blast dest!: x)",
            "(simp (no_asm))",
            "(rule x [OF y])",
            "clarify",
        ] {
            assert!(
                matches!(parse(text), Err(Error::Unsupported(_))),
                "{text}: {:?}",
                parse(text)
            );
        }
    }

    // A section another method takes, or a word that is no section, is Isabelle's syntax error.
    #[test]
    fn rejects_what_isabelle_rejects() {
        for text in [
            "(simp intro: x)",
            "(blast simp: x)",
            "(auto foo: x)",
            "no_such_method",
        ] {
            assert!(
                matches!(parse(text), Err(Error::Isabelle(Exception::Error, _))),
                "{text}: {:?}",
                parse(text)
            );
        }
    }
}
