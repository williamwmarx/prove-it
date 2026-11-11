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

use crate::error::{Res, error_exn};
use crate::provers::clasimp::{BlastDepthTac, ClasimpContext, auto_tac, clarsimp_tac, force_tac};
use crate::provers::classical::{ClassicalContext, add_unsafe_dest, add_unsafe_intro, with_claset};
use crate::pure::drule::{asm_rl, is_norm_hhf, norm_hhf_eq, reflexive_thm, term_i};
use crate::pure::logic::{is_equals, strip_assums_concl, strip_imp_prems};
use crate::pure::name::variant_list;
use crate::pure::object_logic::atomize_prems_tac;
use crate::pure::raw_simplifier::{SimpContext, Simpset, add_simps, empty_simpset};
use crate::pure::rewriter::{RewriteMode, generic_rewrite_goal_tac};
use crate::pure::seq::{Seq, filter_seq, maps_seq, single_seq};
use crate::pure::simplifier::norm_hhf;
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
}

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
    Iprover,
    Intro { facts: Vec<String> },
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

    fn is_section_start(&self) -> bool {
        self.is_word() && self.is_symbol(":", 1)
    }

    fn facts(&mut self) -> Res<Vec<String>> {
        let mut names = Vec::new();
        while self.is_word() && !self.is_section_start() {
            names.push(self.word()?);
        }
        Ok(names)
    }

    fn modifiers(&mut self) -> Res<Vec<Modifier>> {
        let mut result = Vec::new();
        while self.is_section_start() {
            let kind = self.word()?;
            self.position += 1;
            let kind = match kind.as_str() {
                "intro" => ModifierKind::Intro,
                "dest" => ModifierKind::Dest,
                _ => return Err(error_exn(format!("Unsupported method modifier: {kind}"))),
            };
            result.push(Modifier {
                kind,
                facts: self.facts()?,
            });
        }
        Ok(result)
    }

    fn method(&mut self, name: &str, has_args: bool) -> Res<MethodText> {
        let modifiers = |parser: &mut Self| {
            if has_args {
                parser.modifiers()
            } else {
                Ok(Vec::new())
            }
        };
        Ok(match name {
            "auto" => MethodText::Auto {
                modifiers: modifiers(self)?,
            },
            "blast" => MethodText::Blast {
                modifiers: modifiers(self)?,
            },
            "force" => MethodText::Force {
                modifiers: modifiers(self)?,
            },
            "clarsimp" => MethodText::Clarsimp {
                modifiers: modifiers(self)?,
            },
            "iprover" => MethodText::Iprover,
            "intro" => MethodText::Intro {
                facts: if has_args { self.facts()? } else { Vec::new() },
            },
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
            };
            classical = with_claset(&classical, claset);
        }
    }
    Ok(classical)
}

fn get_clasimp(context: &ProofContext, classical: ClassicalContext) -> ClasimpContext {
    ClasimpContext {
        classical,
        simp: SimpContext {
            simpset: context.simpset.clone(),
            bounds: 0,
        },
        blast_depth_tac: context.blast_depth_tac.clone(),
    }
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
                changed_prop(auto_tac(&get_clasimp(
                    &context,
                    with_modifiers(&context, &modifiers)?,
                ))?),
            ))
        }),
        // The TypeScript reads the modifiers once SIMPLE_METHOD' gives the tactic its goal, after
        // building insert_tac.
        MethodText::Clarsimp { modifiers } => Rc::new(move |facts| {
            let insert = insert_tac(facts, 1)?;
            let clasimp = get_clasimp(&context, with_modifiers(&context, &modifiers)?);
            Ok(then_tac(insert, changed_prop(clarsimp_tac(&clasimp)(1))))
        }),
        MethodText::Force { modifiers } => Rc::new(move |facts| {
            let tactic = force_tac(
                &get_clasimp(&context, with_modifiers(&context, &modifiers)?),
                &context.atomize_rules,
            )?;
            simple_method_head(facts, tactic)
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
