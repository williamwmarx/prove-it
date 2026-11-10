// Ported from Z3 (src/nlsat/nlsat_solver.cpp, src/nlsat/nlsat_scoped_literal_vector.h,
// src/util/id_gen.h), MIT license, see z3-license.txt. The atoms of nlsat, hash-consed, with
// reference counts. An atom whose count drops to zero is deleted and its Boolean variable reused,
// last freed first, so literals are numbered as in Z3. Boolean variable 0 is true and has no atom.
//
// The table holds neither the polynomial manager nor the cache nor the solver's hooks: the
// methods that use them take them.
use std::collections::HashMap;
use std::rc::Rc;

use super::Int;
use super::polynomial::{NULL_VAR, Polynomial, PolynomialCache, PolynomialManager, Var};
use super::types::{Atom, AtomRef, IneqAtom, IneqKind, RootAtom, RootKind};

pub const TRUE_BOOL_VAR: u32 = 0;
pub const TRUE_LITERAL: u32 = 0;
pub const FALSE_LITERAL: u32 = 1;

pub fn flip_kind(kind: IneqKind) -> IneqKind {
    match kind {
        IneqKind::Eq => IneqKind::Eq,
        IneqKind::Lt => IneqKind::Gt,
        IneqKind::Gt => IneqKind::Lt,
    }
}

// What the solver keeps per Boolean variable, reset when a variable is made or deleted.
pub trait BoolVarHooks {
    fn on_mk(&mut self, bool_var: u32);
    fn on_delete(&mut self, bool_var: u32);
}

pub struct AtomTable {
    pub atoms: Vec<Option<AtomRef>>,
    ref_counts: Vec<i32>,
    next_bool_var: u32,
    free_bool_vars: Vec<u32>,
    ineq_atoms: HashMap<String, AtomRef>,
    // Keyed by the variable at creation: like Z3's root atom table, renaming the variables leaves the
    // key alone.
    root_atoms: HashMap<String, AtomRef>,
    root_keys: HashMap<u32, String>,
}

impl AtomTable {
    pub fn new(hooks: Option<&mut dyn BoolVarHooks>) -> AtomTable {
        let mut table = AtomTable {
            atoms: Vec::new(),
            ref_counts: Vec::new(),
            next_bool_var: 0,
            free_bool_vars: Vec::new(),
            ineq_atoms: HashMap::new(),
            root_atoms: HashMap::new(),
            root_keys: HashMap::new(),
        };
        table.mk_bool_var(hooks);
        table
    }

    // mk_bool_var_core with id_gen: the last freed variable first.
    pub fn mk_bool_var(&mut self, hooks: Option<&mut dyn BoolVarHooks>) -> u32 {
        let bool_var = self.free_bool_vars.pop().unwrap_or_else(|| {
            self.next_bool_var += 1;
            self.next_bool_var - 1
        });
        let index = bool_var as usize;
        if index == self.atoms.len() {
            self.atoms.push(None);
            self.ref_counts.push(0);
        } else {
            self.atoms[index] = None;
            self.ref_counts[index] = 0;
        }
        if let Some(hooks) = hooks {
            hooks.on_mk(bool_var);
        }
        bool_var
    }

    // degree: the degree of the atom's maximal variable.
    pub fn get_degree(&self, pm: &PolynomialManager, atom: &Atom) -> u32 {
        let atom = match atom {
            Atom::Root(atom) => return pm.degree(&atom.polynomial, atom.max_var.get()),
            Atom::Ineq(atom) => atom,
        };
        let mut max = 0;
        for polynomial in &atom.polynomials {
            max = max.max(pm.degree(polynomial, atom.max_var.get()));
        }
        max
    }

    // reinit_cache: each polynomial back in the cache after a reset, and the maximal variables after
    // a renaming.
    pub fn reinit_cache(&self, pm: &mut PolynomialManager, cache: &mut PolynomialCache) {
        for atom in &self.atoms {
            let Some(atom) = atom else { continue };
            if let Atom::Ineq(atom) = &**atom {
                let mut max = 0;
                for polynomial in &atom.polynomials {
                    cache.mk_unique(pm, polynomial);
                    max = max.max(pm.max_var(polynomial));
                }
                atom.max_var.set(max);
                continue;
            }
            if let Atom::Root(atom) = &**atom {
                cache.mk_unique(pm, &atom.polynomial);
                atom.max_var.set(pm.max_var(&atom.polynomial));
            }
        }
    }

    pub fn get_atom(&self, literal: u32) -> Option<&AtomRef> {
        self.atoms
            .get((literal >> 1) as usize)
            .and_then(Option::as_ref)
    }

    pub fn get_max_var(&self, literal: u32) -> Var {
        self.get_atom(literal)
            .map_or(NULL_VAR, |atom| atom.max_var())
    }

    pub fn inc_ref(&mut self, literal: u32) {
        let bool_var = (literal >> 1) as usize;
        if !matches!(self.atoms.get(bool_var), Some(Some(_))) {
            return;
        }
        self.ref_counts[bool_var] += 1;
    }

    pub fn dec_ref(&mut self, hooks: Option<&mut (dyn BoolVarHooks + '_)>, literal: u32) {
        let bool_var = literal >> 1;
        let index = bool_var as usize;
        let Some(Some(atom)) = self.atoms.get(index) else {
            return;
        };
        self.ref_counts[index] -= 1;
        if self.ref_counts[index] > 0 {
            return;
        }
        if let Atom::Ineq(atom) = &**atom {
            let key = get_ineq_key(atom.kind, &atom.polynomials, &atom.is_even);
            self.ineq_atoms.remove(&key);
        } else {
            if let Some(key) = self.root_keys.get(&bool_var) {
                self.root_atoms.remove(key);
            }
            self.root_keys.remove(&bool_var);
        }
        self.atoms[index] = None;
        if let Some(hooks) = hooks {
            hooks.on_delete(bool_var);
        }
        self.free_bool_vars.push(bool_var);
    }

    // mk_ineq_atom: each factor sign-normalized and hash-consed, the kind flipped when an odd
    // factor changed sign.
    pub fn mk_ineq_atom(
        &mut self,
        pm: &mut PolynomialManager,
        cache: &mut PolynomialCache,
        hooks: Option<&mut dyn BoolVarHooks>,
        kind: IneqKind,
        polynomials: &[Polynomial],
        is_even: &[bool],
    ) -> u32 {
        let mut sign = 1;
        let mut max_var = NULL_VAR;
        let unique: Vec<Polynomial> = polynomials
            .iter()
            .enumerate()
            .map(|(index, polynomial)| {
                let normalized = pm.flip_sign_if_lm_neg(polynomial);
                if !Rc::ptr_eq(&normalized, polynomial) && !is_even[index] {
                    sign = -sign;
                }
                let variable = pm.max_var(&normalized);
                if variable > max_var || max_var == NULL_VAR {
                    max_var = variable;
                }
                cache.mk_unique(pm, &normalized)
            })
            .collect();
        let kind = if sign < 0 { flip_kind(kind) } else { kind };
        let key = get_ineq_key(kind, &unique, is_even);
        if let Some(existing) = self.ineq_atoms.get(&key) {
            return existing.bool_var();
        }
        let bool_var = self.mk_bool_var(hooks);
        let atom = Rc::new(Atom::Ineq(IneqAtom {
            kind,
            bool_var,
            max_var: max_var.into(),
            polynomials: unique,
            is_even: is_even.to_vec(),
        }));
        self.atoms[bool_var as usize] = Some(atom.clone());
        self.ineq_atoms.insert(key, atom);
        bool_var
    }

    // mk_ineq_literal: true or false for a product of constants.
    pub fn mk_ineq_literal(
        &mut self,
        pm: &mut PolynomialManager,
        cache: &mut PolynomialCache,
        hooks: Option<&mut dyn BoolVarHooks>,
        kind: IneqKind,
        polynomials: &[Polynomial],
        is_even: &[bool],
    ) -> u32 {
        let mut constant = Int::one();
        let mut is_const = true;
        for (index, polynomial) in polynomials.iter().enumerate() {
            if !pm.is_const(polynomial) {
                is_const = false;
                continue;
            }
            if pm.is_zero(polynomial) {
                constant = Int::zero();
                is_const = true;
                break;
            }
            let coeff = polynomial.coeff_at(0);
            constant = &constant * &coeff;
            if is_even[index] && coeff.is_negative() {
                constant = -constant;
            }
        }
        if is_const {
            let is_true = (constant.is_positive() && kind == IneqKind::Gt)
                || (constant.is_negative() && kind == IneqKind::Lt)
                || (constant.is_zero() && kind == IneqKind::Eq);
            return if is_true { TRUE_LITERAL } else { FALSE_LITERAL };
        }
        2 * self.mk_ineq_atom(pm, cache, hooks, kind, polynomials, is_even)
    }

    // mk_root_atom: p sign-normalized, which keeps its roots, and hash-consed.
    #[expect(
        clippy::too_many_arguments,
        reason = "the TS signature, and the manager, cache and hooks"
    )]
    pub fn mk_root_atom(
        &mut self,
        pm: &mut PolynomialManager,
        cache: &mut PolynomialCache,
        hooks: Option<&mut dyn BoolVarHooks>,
        kind: RootKind,
        variable: Var,
        index: u32,
        polynomial: &Polynomial,
    ) -> u32 {
        let normalized = pm.flip_sign_if_lm_neg(polynomial);
        let polynomial = cache.mk_unique(pm, &normalized);
        let key = get_root_key(kind, variable, index, &polynomial);
        if let Some(existing) = self.root_atoms.get(&key) {
            return existing.bool_var();
        }
        let bool_var = self.mk_bool_var(hooks);
        let atom = Rc::new(Atom::Root(RootAtom {
            kind,
            bool_var,
            max_var: variable.into(),
            index,
            polynomial,
        }));
        self.atoms[bool_var as usize] = Some(atom.clone());
        self.root_atoms.insert(key.clone(), atom);
        self.root_keys.insert(bool_var, key);
        bool_var
    }
}

fn get_ineq_key(kind: IneqKind, polynomials: &[Polynomial], is_even: &[bool]) -> String {
    let factors: Vec<String> = polynomials
        .iter()
        .enumerate()
        .map(|(index, polynomial)| {
            format!(
                "{}{}",
                polynomial.id(),
                if is_even[index] { "e" } else { "o" }
            )
        })
        .collect();
    format!("{kind:?},{}", factors.join(","))
}

fn get_root_key(kind: RootKind, max_var: Var, index: u32, polynomial: &Polynomial) -> String {
    format!("{kind:?},{max_var},{index},{}", polynomial.id())
}

// scoped_literal_vector: literals that hold a reference to their atoms.
#[derive(Default)]
pub struct ScopedLiterals {
    pub literals: Vec<u32>,
}

impl ScopedLiterals {
    pub fn new() -> ScopedLiterals {
        ScopedLiterals::default()
    }

    pub fn size(&self) -> usize {
        self.literals.len()
    }

    pub fn push(&mut self, table: &mut AtomTable, literal: u32) {
        table.inc_ref(literal);
        self.literals.push(literal);
    }

    pub fn set(
        &mut self,
        table: &mut AtomTable,
        hooks: Option<&mut dyn BoolVarHooks>,
        index: usize,
        literal: u32,
    ) {
        table.inc_ref(literal);
        table.dec_ref(hooks, self.literals[index]);
        self.literals[index] = literal;
    }

    pub fn shrink(
        &mut self,
        table: &mut AtomTable,
        mut hooks: Option<&mut dyn BoolVarHooks>,
        size: usize,
    ) {
        for &literal in &self.literals[size.min(self.literals.len())..] {
            table.dec_ref(hooks.as_deref_mut(), literal);
        }
        self.literals.truncate(size);
    }

    pub fn reset(&mut self, table: &mut AtomTable, hooks: Option<&mut dyn BoolVarHooks>) {
        self.shrink(table, hooks, 0);
    }
}

// scoped_literal: a literal that holds a reference to its atom.
#[derive(Default)]
pub struct ScopedLiteral {
    pub literal: u32,
}

impl ScopedLiteral {
    pub fn new() -> ScopedLiteral {
        ScopedLiteral {
            literal: TRUE_LITERAL,
        }
    }

    pub fn set(
        &mut self,
        table: &mut AtomTable,
        hooks: Option<&mut dyn BoolVarHooks>,
        literal: u32,
    ) {
        table.inc_ref(literal);
        table.dec_ref(hooks, self.literal);
        self.literal = literal;
    }
}
