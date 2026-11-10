//! Comparing formulas by their own alpha-equivalence: each formula prints to a key in which a bound
//! variable is the number of binders between it and its own.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use super::terms::{
    Binding, Checked, Env, Operators, Term, TermKey, TermKind, UncheckedError, term, variable,
};

/// `name.length` in JavaScript, which counts UTF-16 code units.
fn named(tag: &str, name: &str) -> String {
    format!("{tag}{}:{name}", name.encode_utf16().count())
}

fn without(operators: Option<&Rc<Operators>>, name: &str) -> Option<Rc<Operators>> {
    match operators {
        Some(present) if present.contains_key(name) => {
            let mut inner = (**present).clone();
            inner.remove(name);
            Some(Rc::new(inner))
        }
        _ => operators.cloned(),
    }
}

/// The caches of one check: `createKeys`.
#[derive(Default)]
pub struct Keys {
    free_names: HashMap<TermKey, Rc<Vec<Rc<str>>>>,
    top_keys: HashMap<TermKey, Rc<str>>,
    fresh_count: u64,
}

impl Keys {
    // The variables and applied symbols that a formula doesn't bind, which are the names an
    // environment can change.
    fn get_free_names(&mut self, formula: &Term) -> Rc<Vec<Rc<str>>> {
        if let Some(cached) = self.free_names.get(&TermKey(formula.clone())) {
            return cached.clone();
        }
        let mut names = Vec::new();
        let mut seen = HashSet::new();
        let mut add = |name: &Rc<str>| {
            if seen.insert(name.clone()) {
                names.push(name.clone());
            }
        };
        let kind = formula.kind();
        let bound = match kind {
            TermKind::Subst => Some(formula.symbol().clone()),
            TermKind::All | TermKind::Ex | TermKind::Tau | TermKind::Lam => {
                Some(formula.arg(0).symbol().clone())
            }
            _ => None,
        };
        if kind == TermKind::Var || kind == TermKind::App {
            add(formula.symbol());
        }
        if kind != TermKind::Meta {
            for (index, inner) in formula.args().iter().enumerate() {
                for name in self.get_free_names(inner).iter() {
                    if bound.as_ref() != Some(name) || (kind == TermKind::Subst && index == 1) {
                        add(name);
                    }
                }
            }
        }
        let names = Rc::new(names);
        self.free_names
            .insert(TermKey(formula.clone()), names.clone());
        names
    }

    // `operators` replaces applied symbols, for definitions whose parameters are operators.
    pub fn get_key(
        &mut self,
        formula: &Term,
        env: &Rc<Env>,
        depth: i64,
        operators: Option<&Rc<Operators>>,
    ) -> Checked<Rc<str>> {
        for name in self.get_free_names(formula).iter() {
            if env.contains_key(name) || operators.is_some_and(|present| present.contains_key(name))
            {
                return Ok(self.get_env_key(formula, env, depth, operators)?.into());
            }
        }
        self.get_top_key(formula)
    }

    fn get_env_key(
        &mut self,
        formula: &Term,
        env: &Rc<Env>,
        depth: i64,
        operators: Option<&Rc<Operators>>,
    ) -> Checked<String> {
        match formula.kind() {
            TermKind::Var => match env.get(formula.symbol()) {
                None => Ok(named("v", formula.symbol())),
                Some(Binding::Depth(binding)) => Ok(format!("#{}", depth - binding)),
                Some(Binding::Term {
                    formula: bound,
                    env: bound_env,
                    operators: bound_operators,
                }) => Ok(self
                    .get_key(bound, bound_env, depth, bound_operators.as_ref())?
                    .to_string()),
            },
            TermKind::Meta => Ok(format!("m({})", self.get_top_key(&formula.arg(0))?)),
            TermKind::True => Ok("T".into()),
            TermKind::False => Ok("F".into()),
            TermKind::Subst => {
                let mut inner = (**env).clone();
                inner.insert(
                    formula.symbol().clone(),
                    Binding::Term {
                        formula: formula.arg(1),
                        env: env.clone(),
                        operators: operators.cloned(),
                    },
                );
                Ok(self
                    .get_key(
                        &formula.arg(0),
                        &Rc::new(inner),
                        depth,
                        without(operators, formula.symbol()).as_ref(),
                    )?
                    .to_string())
            }
            TermKind::App => {
                let args = formula
                    .args()
                    .iter()
                    .map(|inner| self.get_key(inner, env, depth, operators))
                    .collect::<Checked<Vec<_>>>()?;
                let symbol = formula.symbol();
                if &**symbol == "$notequiv" && args.len() == 2 {
                    return Ok(format!("~(equiv({},{}))", args[0], args[1]));
                }
                let Some(operator) = operators.and_then(|present| present.get(symbol)) else {
                    return Ok(format!("{}({})", named("a", symbol), args.join(",")));
                };
                let operator = operator.clone();
                match operator.kind() {
                    TermKind::Lam if args.len() == 1 => {
                        let inner = Env::from([(
                            operator.arg(0).symbol().clone(),
                            Binding::Term {
                                formula: formula.arg(0),
                                env: env.clone(),
                                operators: operators.cloned(),
                            },
                        )]);
                        Ok(self
                            .get_key(&operator.arg(1), &Rc::new(inner), depth, None)?
                            .to_string())
                    }
                    TermKind::Var => Ok(format!(
                        "{}({})",
                        named("a", operator.symbol()),
                        args.join(",")
                    )),
                    TermKind::App => {
                        let empty = Rc::new(Env::new());
                        let mut all = operator
                            .args()
                            .iter()
                            .map(|inner| self.get_key(inner, &empty, depth, None))
                            .collect::<Checked<Vec<_>>>()?;
                        all.extend(args);
                        Ok(format!(
                            "{}({})",
                            named("a", operator.symbol()),
                            all.join(",")
                        ))
                    }
                    _ => Err(UncheckedError),
                }
            }
            TermKind::Not => Ok(format!(
                "~({})",
                self.get_key(&formula.arg(0), env, depth, operators)?
            )),
            kind @ (TermKind::And | TermKind::Or | TermKind::Imply | TermKind::Equiv) => {
                let left = self.get_key(&formula.arg(0), env, depth, operators)?;
                let right = self.get_key(&formula.arg(1), env, depth, operators)?;
                Ok(format!("{}({left},{right})", kind.name()))
            }
            kind @ (TermKind::All | TermKind::Ex | TermKind::Tau | TermKind::Lam) => {
                let bound = formula.arg(0).symbol().clone();
                let mut inner = (**env).clone();
                inner.insert(bound.clone(), Binding::Depth(depth));
                let body = self.get_key(
                    &formula.arg(1),
                    &Rc::new(inner),
                    depth + 1,
                    without(operators, &bound).as_ref(),
                )?;
                Ok(format!(
                    "{}{}{{{body}}}",
                    kind.name(),
                    named("", formula.symbol())
                ))
            }
        }
    }

    pub fn get_top_key(&mut self, formula: &Term) -> Checked<Rc<str>> {
        if let Some(cached) = self.top_keys.get(&TermKey(formula.clone())) {
            return Ok(cached.clone());
        }
        // Keys count binders from the variable, so a formula's key doesn't depend on where it sits.
        let key: Rc<str> = self
            .get_env_key(formula, &Rc::new(Env::new()), 0, None)?
            .into();
        self.top_keys.insert(TermKey(formula.clone()), key.clone());
        Ok(key)
    }

    pub fn is_same(&mut self, left: &Term, right: &Term) -> Checked<bool> {
        Ok(self.get_top_key(left)? == self.get_top_key(right)?)
    }

    pub fn bind(
        &mut self,
        kind: TermKind,
        type_name: &str,
        build: impl FnOnce(&Term) -> Term,
    ) -> Term {
        let bound = variable(&format!("\u{0}{}", self.fresh_count));
        self.fresh_count += 1;
        let body = build(&bound);
        term(kind, type_name, vec![bound, body])
    }
}
