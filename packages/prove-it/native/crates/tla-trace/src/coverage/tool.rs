//! TLC's `Tool`, as `FastTool` runs it with coverage on: `eval`, `getInitStates`,
//! `getNextStates` and `processUnchanged`, each counting into the cost model where TLC does
//! (`getAndIncrement`, `incInvocations`, `incSecondary`), over SANY's graph ([`super::sem`]).
//! The values are the trace evaluator's; TLC's `Value.cm`, which a value keeps from the node
//! that built it and counts its enumerations into, is a table beside them, by the value's
//! allocation ([`Tags`]).

use std::cell::RefCell;
use std::rc::{Rc, Weak};

use super::FastMap;
use super::model::{Cm, Model, NO_CM};
use super::sem::{Code, DefId, Op, SBound, SId, SKind, Sem, Sym};
use crate::eval::{Context as OldContext, Evaluator, Operand};
use crate::sets::is_member;
use crate::value::{
    Class, EvalError, Function, Lazy, Value, compare, elements, equals, find_key, set_of,
    sorted_function,
};

pub(crate) type St = Vec<Option<Value>>;

/// Why a walk stops: the port can't follow TLC, or TLC stops it, as a violation does.
#[derive(Debug)]
pub(crate) enum Halt {
    /// The port can't follow TLC.
    No(String),
    /// TLC fails to evaluate, as it reports with an error.
    Fail(String),
    /// The search stops, as at a violation.
    Stop,
}

impl From<EvalError> for Halt {
    fn from(error: EvalError) -> Halt {
        Halt::Fail(error.reason)
    }
}

fn fail<T>(why: impl Into<String>) -> R<T> {
    Err(Halt::Fail(why.into()))
}

pub(crate) type R<T> = Result<T, Halt>;

pub(crate) fn no<T>(why: impl Into<String>) -> R<T> {
    Err(Halt::No(why.into()))
}

/// `EvalControl`'s flags.
pub(crate) const KEEP_LAZY: u8 = 1;
pub(crate) const INIT: u8 = 2;
pub(crate) const CLEAR: u8 = 0;

/// A value as `Tool.eval` gives it: one of the trace evaluator's, or a function TLC keeps lazy
/// (`FcnLambdaValue`) that this port built.
#[derive(Clone)]
pub(crate) enum CVal {
    V(Value),
    Fcn(Rc<FcnLambda>),
}

impl CVal {
    pub fn value(self) -> R<Value> {
        match self {
            CVal::V(value) => Ok(value),
            CVal::Fcn(_) => no("a function TLC keeps lazy inside another value"),
        }
    }

    fn boolean(&self) -> R<bool> {
        match self {
            CVal::V(Value::Bool(boolean)) => Ok(*boolean),
            _ => no("a non-boolean where TLC expects a boolean"),
        }
    }
}

pub(crate) struct FcnLambda {
    /// Each group of bound names, whether it is a tuple, and its domain.
    params: Vec<(Vec<Sym>, bool, Value)>,
    body: SId,
    ctx: Ctx,
    /// The name the body applies it by (`makeRecursive`).
    recursive: Option<Sym>,
    s0: St,
    s1: Option<St>,
    control: u8,
    cm: Cm,
    fcn_rcd: RefCell<Option<Value>>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Key {
    Sym(Sym),
    Def(DefId),
    At,
}

#[derive(Clone)]
enum Bind {
    Val(CVal),
    Lazy(Rc<LazyCell>),
}

/// `LazyValue`: an operator's argument or a LET's definition, evaluated where it is used and
/// kept for the states it was evaluated in.
struct LazyCell {
    expr: SId,
    ctx: Ctx,
    cm: Cm,
    cache: RefCell<Option<Cached>>,
}

/// A lazy value's value, with the states and the control it was evaluated in.
type Cached = (CVal, St, Option<St>, u8);

/// TLC's `Context`: bindings innermost first.
#[derive(Clone, Default)]
pub(crate) struct Ctx(Option<Rc<Frame>>);

struct Frame {
    key: Key,
    bind: Bind,
    next: Ctx,
}

impl Ctx {
    fn cons(&self, key: Key, bind: Bind) -> Ctx {
        Ctx(Some(Rc::new(Frame {
            key,
            bind,
            next: self.clone(),
        })))
    }

    pub fn bind_value(&self, sym: Sym, value: CVal) -> Ctx {
        self.cons(Key::Sym(sym), Bind::Val(value))
    }

    fn lookup(&self, key: Key) -> Option<Bind> {
        let mut frame = self.0.as_ref();
        while let Some(current) = frame {
            if current.key == key {
                return Some(current.bind.clone());
            }
            frame = current.next.0.as_ref();
        }
        None
    }
}

// --- the cost models of values ---

enum WeakValue {
    Set(Weak<Vec<Value>>),
    Function(Weak<Function>),
    Lazy(Weak<Lazy>),
}

/// TLC's `Value.cm` of the values `Tool` built, by the address of their allocation, with a weak
/// reference that tells a live value from one whose address was freed and taken again.
#[derive(Default)]
pub(crate) struct Tags {
    table: FastMap<usize, (WeakValue, Cm)>,
    swept_at: usize,
}

fn address(value: &Value) -> Option<usize> {
    match value {
        Value::Set(rc) => Some(Rc::as_ptr(rc) as usize),
        Value::Function(rc) => Some(Rc::as_ptr(rc) as usize),
        Value::Lazy(rc) => Some(Rc::as_ptr(rc) as *const u8 as usize),
        _ => None,
    }
}

impl Tags {
    pub fn tag(&mut self, value: &Value, cm: Cm) {
        if cm == NO_CM {
            return;
        }
        let (Some(key), weak) = (
            address(value),
            match value {
                Value::Set(rc) => WeakValue::Set(Rc::downgrade(rc)),
                Value::Function(rc) => WeakValue::Function(Rc::downgrade(rc)),
                Value::Lazy(rc) => WeakValue::Lazy(Rc::downgrade(rc)),
                _ => return,
            },
        ) else {
            return;
        };
        self.table.insert(key, (weak, cm));
        if self.table.len() > 2 * self.swept_at.max(1 << 16) {
            self.table.retain(|_, (weak, _)| match weak {
                WeakValue::Set(weak) => weak.strong_count() > 0,
                WeakValue::Function(weak) => weak.strong_count() > 0,
                WeakValue::Lazy(weak) => weak.strong_count() > 0,
            });
            self.swept_at = self.table.len();
        }
    }

    pub fn get(&self, value: &Value) -> Cm {
        let Some(key) = address(value) else {
            return NO_CM;
        };
        let Some((weak, cm)) = self.table.get(&key) else {
            return NO_CM;
        };
        let is_same = match (weak, value) {
            (WeakValue::Set(weak), Value::Set(rc)) => {
                weak.upgrade().is_some_and(|held| Rc::ptr_eq(&held, rc))
            }
            (WeakValue::Function(weak), Value::Function(rc)) => {
                weak.upgrade().is_some_and(|held| Rc::ptr_eq(&held, rc))
            }
            (WeakValue::Lazy(weak), Value::Lazy(rc)) => {
                weak.upgrade().is_some_and(|held| Rc::ptr_eq(&held, rc))
            }
            _ => false,
        };
        if is_same { *cm } else { NO_CM }
    }
}

// --- the walks' lists of what is left (`ActionItemList`) ---

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Conjunct,
    Pred,
    Unchanged,
    Changed,
}

#[derive(Clone, Default)]
struct Acts(Option<Rc<Item>>);

struct Item {
    pred: SId,
    ctx: Ctx,
    kind: Kind,
    cm: Cm,
    next: Acts,
}

impl Acts {
    fn cons(&self, pred: SId, ctx: Ctx, cm: Cm, kind: Kind) -> Acts {
        Acts(Some(Rc::new(Item {
            pred,
            ctx,
            kind,
            cm,
            next: self.clone(),
        })))
    }
}

/// An action as TLC splits it, with its bindings.
#[derive(Clone)]
pub(crate) struct Action {
    pub pred: SId,
    pub ctx: Ctx,
    pub cm: Cm,
}

/// What a next-state walk does with each successor: `INextStateFunctor.addElement`, which may
/// stop the walk with `Halt::Stop`.
pub(crate) type NextFunctor<'f, 'a, 'ir> = dyn FnMut(&mut Tool<'a, 'ir>, &St) -> R<()> + 'f;
pub(crate) type InitFunctor<'f, 'a, 'ir> = dyn FnMut(&mut Tool<'a, 'ir>, &St) -> R<()> + 'f;

pub(crate) struct Tool<'a, 'ir> {
    pub sem: &'a Sem<'ir>,
    pub model: Model,
    pub old: Evaluator<'ir>,
    pub tags: Tags,
    pub is_warning_enabled: bool,
    empty: Rc<St>,
    /// The values TLC computed at startup, by definition, or none where it failed.
    constants: FastMap<DefId, Option<Value>>,
    /// The enumeration counts of values built at startup aren't counted.
    pub width: usize,
}

fn primitive_equals(left: &Value, right: &Value) -> R<bool> {
    Ok(equals(left, right)?)
}

impl<'a, 'ir> Tool<'a, 'ir> {
    pub fn new(sem: &'a Sem<'ir>, old: Evaluator<'ir>, is_warning_enabled: bool) -> Self {
        let width = sem.ir.variables.len();
        Tool {
            sem,
            model: Model::new(),
            old,
            tags: Tags::default(),
            is_warning_enabled,
            empty: Rc::new(vec![None; width]),
            constants: FastMap::default(),
            width,
        }
    }

    fn get(&mut self, cm: Cm, node: SId) -> Cm {
        self.model.get(cm, node, self.sem)
    }

    fn mismatch(&self) -> R<()> {
        match &self.model.mismatch {
            Some(why) => no(why.clone()),
            None => Ok(()),
        }
    }

    fn tagged(&mut self, value: Value, cm: Cm) -> CVal {
        self.tags.tag(&value, cm);
        CVal::V(value)
    }

    fn appl(&self, id: SId) -> (Op, &'a [Option<SId>], &'a [SBound], Option<Sym>) {
        match &self.sem.node(id).kind {
            SKind::Appl {
                op,
                args,
                bounds,
                recursive,
            } => (*op, args, bounds, *recursive),
            _ => unreachable!("an application"),
        }
    }

    // --- eval ---

    /// `Tool.eval`.
    pub fn eval(
        &mut self,
        expr: SId,
        c: &Ctx,
        s0: &St,
        s1: Option<&St>,
        control: u8,
        cm: Cm,
    ) -> R<CVal> {
        match &self.sem.node(expr).kind {
            SKind::Num(int) => Ok(CVal::V(Value::Int(*int))),
            SKind::Str(text) => Ok(CVal::V(Value::Str(self.old.text(*text)))),
            SKind::At => match c.lookup(Key::At) {
                Some(Bind::Val(value)) => Ok(value),
                _ => no("@ outside an EXCEPT"),
            },
            SKind::Let { defs, body } => {
                let mut c1 = c.clone();
                for &def in defs {
                    if self.sem.def(def).params.is_empty() {
                        let lazy = self.lazy(self.sem.def(def).body.expect("a body"), &c1, cm);
                        c1 = c1.cons(Key::Def(def), Bind::Lazy(lazy));
                    }
                }
                self.eval(*body, &c1, s0, s1, control, cm)
            }
            SKind::Appl { .. } => {
                let cm = self.get(cm, expr);
                self.eval_appl(expr, c, s0, s1, control, cm)
            }
        }
    }

    fn lazy(&mut self, expr: SId, c: &Ctx, cm: Cm) -> Rc<LazyCell> {
        let cm = self.get(cm, expr);
        Rc::new(LazyCell {
            expr,
            ctx: c.clone(),
            cm,
            cache: RefCell::new(None),
        })
    }

    fn eval_value(
        &mut self,
        expr: SId,
        c: &Ctx,
        s0: &St,
        s1: Option<&St>,
        control: u8,
        cm: Cm,
    ) -> R<Value> {
        self.eval(expr, c, s0, s1, control, cm)?.value()
    }

    fn eval_bool(
        &mut self,
        expr: SId,
        c: &Ctx,
        s0: &St,
        s1: Option<&St>,
        control: u8,
        cm: Cm,
    ) -> R<bool> {
        self.eval(expr, c, s0, s1, control, cm)?.boolean()
    }

    // `TLCState.isSubset`: every variable the cached state holds, the state holds equal.
    fn is_subset(state: Option<&St>, cached: Option<&St>) -> Option<bool> {
        let Some(cached) = cached else {
            return Some(true);
        };
        for (index, held) in cached.iter().enumerate() {
            let Some(held) = held else { continue };
            let Some(value) = state.and_then(|state| state[index].as_ref()) else {
                return Some(false);
            };
            match equals(value, held) {
                Ok(true) => {}
                Ok(false) => return Some(false),
                Err(_) => return None,
            }
        }
        Some(true)
    }

    /// `LazyValue.getValue`.
    fn lazy_value(
        &mut self,
        lazy: &Rc<LazyCell>,
        s0: &St,
        s1: Option<&St>,
        control: u8,
    ) -> R<CVal> {
        if let Some((value, cached0, cached1, cached_control)) = &*lazy.cache.borrow() {
            let equivalent =
                (control & !(KEEP_LAZY | INIT)) == (cached_control & !(KEEP_LAZY | INIT));
            if equivalent
                && Self::is_subset(Some(s0), Some(cached0)) == Some(true)
                && Self::is_subset(s1, cached1.as_ref()) == Some(true)
            {
                return Ok(value.clone());
            }
        }
        let value = self.eval(lazy.expr, &lazy.ctx.clone(), s0, s1, control, lazy.cm)?;
        *lazy.cache.borrow_mut() = Some((value.clone(), s0.clone(), s1.cloned(), control));
        Ok(value)
    }

    /// A definition's value as TLC computed it at startup, or none where TLC evaluates it each
    /// time.
    fn constant(&mut self, def: DefId) -> R<Option<Value>> {
        if !self.sem.def(def).is_constant {
            return Ok(None);
        }
        if let Some(value) = self.constants.get(&def) {
            return match value {
                Some(value) => Ok(Some(value.clone())),
                None => no("a constant definition whose value TLC computes at startup fails"),
            };
        }
        let node = self.sem.def(def).node;
        let value = self.old.definition_value(node, &OldContext::default()).ok();
        self.constants.insert(def, value.clone());
        match value {
            Some(value) => Ok(Some(value)),
            None => no("a constant definition whose value TLC computes at startup fails"),
        }
    }

    // `getOpContext`: the arguments as lazy values in the caller's context.
    fn op_context(&mut self, def: DefId, args: &[Option<SId>], c: &Ctx, cm: Cm) -> Ctx {
        let mut c1 = c.clone();
        for (index, arg) in args.iter().enumerate() {
            let arg = arg.expect("an argument");
            let lazy = self.lazy(arg, c, cm);
            c1 = c1.cons(Key::Sym(self.sem.def(def).params[index]), Bind::Lazy(lazy));
        }
        c1
    }

    fn builtin(&mut self, index: tla_ir::Index, values: Vec<Value>) -> R<Value> {
        let name = self.sem.text(self.sem.ir.builtins[index as usize].name);
        // What Print and PrintT print the search printed already; their values are these.
        match (name, &values[..]) {
            ("Print", [_, value]) => return Ok(value.clone()),
            ("PrintT", [_]) => return Ok(Value::Bool(true)),
            _ => {}
        }
        if !is_overridden(name) {
            return no(format!(
                "the builtin {name}, which TLC may not override in Java"
            ));
        }
        // The conversions TLC's Java makes of its arguments, which count into their cost models.
        match name {
            "@@" => {
                for value in &values {
                    self.count_to_fcn_rcd(value);
                }
            }
            "Len" | "Head" | "Tail" | "Append" | "SubSeq" => self.count_to_tuple(&values[0]),
            "\\o" => {
                for value in &values {
                    self.count_to_tuple(value);
                }
            }
            "Cardinality" | "IsFiniteSet" | "Permutations"
                if values.iter().any(|value| {
                    matches!(value, Value::Lazy(_)) && self.tags.get(value) != NO_CM
                }) =>
            {
                return no(format!("{name} of a lazy set with a cost model"));
            }
            _ => {}
        }
        let operands: Vec<Operand> = values.into_iter().map(Operand::Value).collect();
        Ok(self.old.builtin(index, &operands, &OldContext::default())?)
    }

    /// `toFcnRcd` of a tuple or a record, which counts its elements into its cost model.
    fn count_to_fcn_rcd(&mut self, value: &Value) {
        if let Value::Function(function) = value
            && matches!(function.class.get(), Class::Tuple | Class::Record)
        {
            let cm = self.tags.get(value);
            self.model.add_secondary(cm, function.domain.len() as u64);
        }
    }

    /// `toTuple` of a function over a set of integers 1..n that isn't an interval, which counts
    /// its elements into its cost model.
    fn count_to_tuple(&mut self, value: &Value) {
        if let Value::Function(function) = value
            && matches!(function.class.get(), Class::Plain | Class::Lambda)
            && function.interval.is_none()
            && function
                .domain
                .iter()
                .enumerate()
                .all(|(index, key)| matches!(key, Value::Int(int) if *int as usize == index + 1))
        {
            let cm = self.tags.get(value);
            self.model.add_secondary(cm, function.domain.len() as u64);
        }
    }

    fn eval_appl(
        &mut self,
        expr: SId,
        c: &Ctx,
        s0: &St,
        s1: Option<&St>,
        control: u8,
        cm: Cm,
    ) -> R<CVal> {
        self.model.increment(cm);
        self.mismatch()?;
        let (op, args, bounds, recursive) = self.appl(expr);
        let code = match op {
            Op::Code(code) => code,
            Op::Sym(sym) => {
                return match c.lookup(Key::Sym(sym)) {
                    Some(Bind::Val(value)) => Ok(value),
                    Some(Bind::Lazy(lazy)) => {
                        if s1.is_none() {
                            let ctx = lazy.ctx.clone();
                            self.eval(lazy.expr, &ctx, s0, None, control, lazy.cm)
                        } else {
                            self.lazy_value(&lazy, s0, s1, control)
                        }
                    }
                    None => no("a name bound outside what the port follows"),
                };
            }
            Op::Var(index) => {
                return match &s0[index as usize] {
                    Some(value) => Ok(CVal::V(value.clone())),
                    None => fail("a variable TLC reads unassigned"),
                };
            }
            Op::Const(index) => {
                let Some(value) = self.sem.ir.constants[index as usize].value else {
                    return no("a constant the IR can't hold");
                };
                return Ok(CVal::V(self.old.value(value)?));
            }
            Op::Builtin(index) => {
                let mut values = Vec::with_capacity(args.len());
                for arg in args {
                    values.push(self.eval_value(
                        arg.expect("an argument"),
                        c,
                        s0,
                        s1,
                        control,
                        cm,
                    )?);
                }
                return Ok(CVal::V(self.builtin(index, values)?));
            }
            Op::Def(def) => {
                if let Some(bind) = c.lookup(Key::Def(def)) {
                    return match bind {
                        Bind::Val(value) => Ok(value),
                        Bind::Lazy(lazy) => {
                            if s1.is_none() {
                                let ctx = lazy.ctx.clone();
                                self.eval(lazy.expr, &ctx, s0, None, control, lazy.cm)
                            } else {
                                self.lazy_value(&lazy, s0, s1, control)
                            }
                        }
                    };
                }
                if let Some(value) = self.constant(def)? {
                    return Ok(CVal::V(value));
                }
                let c1 = self.op_context(def, args, c, cm);
                let body = self.sem.def(def).body.expect("a body");
                return self.eval(body, &c1, s0, s1, control, cm);
            }
            Op::Substituted(def) => {
                let c1 = self.op_context(def, args, c, cm);
                let body = self.sem.def(def).body.expect("a body");
                return self.eval(body, &c1, s0, s1, control, cm);
            }
        };
        let arg = |index: usize| args[index].expect("an operand");
        Ok(match code {
            Code::BoundedChoose => {
                let bound = &bounds[0];
                let set = self.eval_value(bound.set, c, s0, s1, control, cm)?;
                let mut enumeration = self.elements(&set, true)?;
                while let Some(element) = self.next(&mut enumeration)? {
                    let c1 = self.bind_bound(c, bound, &element)?;
                    if self.eval_bool(arg(0), &c1, s0, s1, control, cm)? {
                        return Ok(CVal::V(element));
                    }
                }
                return no("CHOOSE found no element");
            }
            Code::BoundedExists | Code::BoundedForall => {
                let is_exists = code == Code::BoundedExists;
                let mut contexts = self.contexts(bounds, c, s0, s1, control, cm)?;
                while let Some(c1) = self.next_context(&mut contexts)? {
                    if self.eval_bool(arg(0), &c1, s0, s1, control, cm)? == is_exists {
                        return Ok(CVal::V(Value::Bool(is_exists)));
                    }
                }
                CVal::V(Value::Bool(!is_exists))
            }
            Code::Case => {
                let mut other = None;
                let mut cm = cm;
                for pair in args.iter().flatten() {
                    let pair_args = self.appl(*pair).1;
                    match pair_args[0] {
                        None => {
                            other = pair_args[1];
                            cm = self.get(cm, *pair);
                        }
                        Some(condition) => {
                            let pair_cm = self.get(cm, *pair);
                            if self.eval_bool(condition, c, s0, s1, control, pair_cm)? {
                                let pair_cm = self.get(cm, *pair);
                                return self.eval(
                                    pair_args[1].expect("a value"),
                                    c,
                                    s0,
                                    s1,
                                    control,
                                    pair_cm,
                                );
                            }
                        }
                    }
                }
                match other {
                    Some(other) => return self.eval(other, c, s0, s1, control, cm),
                    None => return no("a CASE with no condition true"),
                }
            }
            Code::CartesianProd => {
                let mut sets = Vec::new();
                for arg in args.iter().flatten() {
                    sets.push(self.eval_value(*arg, c, s0, s1, control, cm)?);
                }
                let value = Value::Lazy(Rc::new(Lazy::Product(sets)));
                self.tagged(value, cm)
            }
            Code::ConjList | Code::DisjList => {
                let is_and = code == Code::ConjList;
                for arg in args.iter().flatten() {
                    if self.eval_bool(*arg, c, s0, s1, control, cm)? != is_and {
                        return Ok(CVal::V(Value::Bool(!is_and)));
                    }
                }
                CVal::V(Value::Bool(is_and))
            }
            Code::Except => self.except(expr, c, s0, s1, control, cm)?,
            Code::FcnApply => {
                let function = self.eval(arg(0), c, s0, s1, control | KEEP_LAZY, cm)?;
                let argument = self.eval_value(arg(1), c, s0, s1, control, cm)?;
                self.apply(&function, &argument, control)?
            }
            Code::FcnConstructor | Code::NonRecursiveFcnSpec | Code::RecursiveFcnSpec => {
                let mut params = Vec::new();
                let mut is_reducible = true;
                for bound in bounds {
                    let domain = self.eval_value(bound.set, c, s0, s1, control, cm)?;
                    is_reducible &= matches!(domain, Value::Set(_) | Value::Interval(..));
                    params.push((bound.syms.clone(), bound.is_tuple, domain));
                }
                let is_recursive = code == Code::RecursiveFcnSpec;
                let lambda = Rc::new(FcnLambda {
                    params,
                    body: arg(0),
                    ctx: c.clone(),
                    recursive: if is_recursive { recursive } else { None },
                    s0: s0.clone(),
                    s1: s1.cloned(),
                    control: if is_recursive {
                        control | KEEP_LAZY
                    } else {
                        control
                    },
                    cm,
                    fcn_rcd: RefCell::new(None),
                });
                if is_reducible && !is_recursive && control & KEEP_LAZY == 0 {
                    CVal::V(self.fcn_rcd_of(&lambda)?)
                } else {
                    CVal::Fcn(lambda)
                }
            }
            Code::IfThenElse => {
                let branch = if self.eval_bool(arg(0), c, s0, s1, control, cm)? {
                    arg(1)
                } else {
                    arg(2)
                };
                return self.eval(branch, c, s0, s1, control, cm);
            }
            Code::RcdConstructor => {
                let mut fields = Vec::new();
                for pair in args.iter().flatten() {
                    let pair_args = self.appl(*pair).1;
                    let SKind::Str(name) = self.sem.node(pair_args[0].expect("a name")).kind else {
                        return no("a record field without a name");
                    };
                    let pair_cm = self.get(cm, *pair);
                    let value = self.eval_value(
                        pair_args[1].expect("a value"),
                        c,
                        s0,
                        s1,
                        control,
                        pair_cm,
                    )?;
                    fields.push((self.old.text(name), value));
                }
                let value = Value::record(fields)?;
                self.tagged(value, cm)
            }
            Code::RcdSelect => {
                let record = self.eval_value(arg(0), c, s0, s1, control, cm)?;
                let SKind::Str(name) = self.sem.node(arg(1)).kind else {
                    return no("a field selected without a name");
                };
                let key = Value::Str(self.old.text(name));
                let Value::Function(function) = &record else {
                    return no("a field selected from a non-record");
                };
                if function.class.get() == Class::Tuple {
                    // `toFcnRcd` of a tuple counts into the tuple's cost model.
                    self.count_conversion(&record)?;
                }
                match find_key(function, &key)? {
                    Some(position) => CVal::V(function.range[position].clone()),
                    None => return no("a field selected that the record lacks"),
                }
            }
            Code::SetEnumerate => {
                let mut values = Vec::new();
                for arg in args.iter().flatten() {
                    values.push(self.eval_value(*arg, c, s0, s1, control, cm)?);
                }
                let set = self.set_of(values)?;
                self.tagged(set, cm)
            }
            Code::SetOfAll => {
                let mut values = Vec::new();
                let mut contexts = self.contexts(bounds, c, s0, s1, control, cm)?;
                while let Some(c1) = self.next_context(&mut contexts)? {
                    values.push(self.eval_value(arg(0), &c1, s0, s1, control, cm)?);
                }
                let set = self.set_of(values)?;
                self.tagged(set, cm)
            }
            Code::SetOfRcds => {
                let mut fields = Vec::new();
                for pair in args.iter().flatten() {
                    let pair_args = self.appl(*pair).1;
                    let SKind::Str(name) = self.sem.node(pair_args[0].expect("a name")).kind else {
                        return no("a record field without a name");
                    };
                    let pair_cm = self.get(cm, *pair);
                    let value = self.eval_value(
                        pair_args[1].expect("a value"),
                        c,
                        s0,
                        s1,
                        control,
                        pair_cm,
                    )?;
                    fields.push((self.old.text(name), value));
                }
                let value = record_set(fields)?;
                self.tagged(value, cm)
            }
            Code::SetOfFcns => {
                let domain = self.eval_value(arg(0), c, s0, s1, control, cm)?;
                let range = self.eval_value(arg(1), c, s0, s1, control, cm)?;
                let value = Value::Lazy(Rc::new(Lazy::FunctionSet(domain, range)));
                self.tagged(value, cm)
            }
            Code::SubsetOf => {
                let bound = &bounds[0];
                let set = self.eval_value(bound.set, c, s0, s1, control, cm)?;
                if !matches!(set, Value::Set(_) | Value::Interval(..)) {
                    return no("a set filter TLC keeps lazy (SetPredValue)");
                }
                let mut kept = Vec::new();
                let mut enumeration = self.elements(&set, false)?;
                while let Some(element) = self.next(&mut enumeration)? {
                    let c1 = self.bind_bound(c, bound, &element)?;
                    if self.eval_bool(arg(0), &c1, s0, s1, control, cm)? {
                        kept.push(element);
                    }
                }
                let set = self.set_of(kept)?;
                self.tagged(set, cm)
            }
            Code::Tuple => {
                let mut values = Vec::new();
                for arg in args.iter().flatten() {
                    values.push(self.eval_value(*arg, c, s0, s1, control, cm)?);
                }
                let value = Value::tuple(values);
                self.tagged(value, cm)
            }
            Code::Lnot => CVal::V(Value::Bool(!self.eval_bool(
                arg(0),
                c,
                s0,
                s1,
                control,
                cm,
            )?)),
            Code::Subset => {
                let base = self.eval_value(arg(0), c, s0, s1, control, cm)?;
                let value = Value::Lazy(Rc::new(Lazy::Subset(base)));
                self.tagged(value, cm)
            }
            Code::Union => {
                let sets = self.eval_value(arg(0), c, s0, s1, control, cm)?;
                self.union(&sets)?
            }
            Code::Domain => {
                let function = self.eval(arg(0), c, s0, s1, control, cm)?;
                CVal::V(self.domain(&function)?)
            }
            Code::Eq | Code::Noteq => {
                let left = self.eval(arg(0), c, s0, s1, control, cm)?;
                let right = self.eval(arg(1), c, s0, s1, control, cm)?;
                let is_equal = self.tlc_equals_cval(&left, &right)?;
                CVal::V(Value::Bool(is_equal == (code == Code::Eq)))
            }
            Code::Land | Code::Lor => {
                let is_and = code == Code::Land;
                let left = self.eval_bool(arg(0), c, s0, s1, control, cm)?;
                if left != is_and {
                    return Ok(CVal::V(Value::Bool(left)));
                }
                CVal::V(Value::Bool(self.eval_bool(
                    arg(1),
                    c,
                    s0,
                    s1,
                    control,
                    cm,
                )?))
            }
            Code::Implies => {
                if self.eval_bool(arg(0), c, s0, s1, control, cm)? {
                    CVal::V(Value::Bool(self.eval_bool(
                        arg(1),
                        c,
                        s0,
                        s1,
                        control,
                        cm,
                    )?))
                } else {
                    CVal::V(Value::Bool(true))
                }
            }
            Code::Equiv => {
                let left = self.eval_bool(arg(0), c, s0, s1, control, cm)?;
                let right = self.eval_bool(arg(1), c, s0, s1, control, cm)?;
                CVal::V(Value::Bool(left == right))
            }
            Code::Subseteq => {
                let left = self.eval_value(arg(0), c, s0, s1, control, cm)?;
                let right = self.eval_value(arg(1), c, s0, s1, control, cm)?;
                CVal::V(Value::Bool(self.is_subseteq(&left, &right)?))
            }
            Code::In | Code::Notin => {
                let element = self.eval_value(arg(0), c, s0, s1, control, cm)?;
                let set = self.eval_value(arg(1), c, s0, s1, control, cm)?;
                let is_in = self.member(&element, &set)?;
                CVal::V(Value::Bool(is_in == (code == Code::In)))
            }
            Code::Setdiff | Code::Cap | Code::Cup => {
                let left = self.eval_value(arg(0), c, s0, s1, control, cm)?;
                let right = self.eval_value(arg(1), c, s0, s1, control, cm)?;
                CVal::V(self.set_operation(code, left, right, cm)?)
            }
            Code::Prime => {
                let Some(next) = s1 else {
                    return no("a prime TLC evaluates in no next state");
                };
                return self.eval(arg(0), c, next, None, control, cm);
            }
            Code::Unchanged => {
                let empty = Rc::clone(&self.empty);
                let before = self.eval(arg(0), c, s0, Some(&empty), control, cm)?;
                let Some(next) = s1 else {
                    return no("UNCHANGED in no next state");
                };
                let after = self.eval(arg(0), c, next, None, control, cm)?;
                CVal::V(Value::Bool(self.tlc_equals_cval(&before, &after)?))
            }
            Code::AngleAct | Code::SquareAct => {
                let holds = self.eval_bool(arg(0), c, s0, s1, control, cm)?;
                let is_angle = code == Code::AngleAct;
                if holds != is_angle {
                    return Ok(CVal::V(Value::Bool(holds)));
                }
                let empty = Rc::clone(&self.empty);
                let before = self.eval(arg(1), c, s0, Some(&empty), control, cm)?;
                let Some(next) = s1 else {
                    return no("an action TLC evaluates in no next state");
                };
                let after = self.eval(arg(1), c, next, None, control, cm)?;
                let is_equal = self.tlc_equals_cval(&before, &after)?;
                CVal::V(Value::Bool(is_equal != is_angle))
            }
            Code::Pair | Code::Seq => return no("a $Pair evaluated"),
        })
    }

    fn bind_bound(&mut self, c: &Ctx, bound: &SBound, element: &Value) -> R<Ctx> {
        if !bound.is_tuple {
            return Ok(c.bind_value(bound.syms[0], CVal::V(element.clone())));
        }
        let Some(items) = tuple_items(element) else {
            return no("a tuple bound to a value that isn't one");
        };
        if items.len() != bound.syms.len() {
            return no("a tuple bound to one of another length");
        }
        let mut c1 = c.clone();
        for (sym, item) in bound.syms.iter().zip(items) {
            c1 = c1.bind_value(*sym, CVal::V(item.clone()));
        }
        Ok(c1)
    }

    fn set_of(&mut self, values: Vec<Value>) -> R<Value> {
        // Sorting compares the elements, which converts a tuple or a record compared with a
        // function, counting into its cost model.
        let mut classes = values.iter().filter_map(|value| match value {
            Value::Function(function) => Some(function.class.get() == Class::Plain),
            _ => None,
        });
        if let Some(first) = classes.next()
            && classes.any(|class| class != first)
        {
            return no("a set of functions of different classes");
        }
        if self.is_converted_in_comparison(&values) {
            return no("a set of tuples or records and other values");
        }
        Ok(set_of(values)?)
    }

    /// Whether comparing the values converts a tuple or a record with a cost model, as TLC
    /// does comparing one with a value that isn't a function.
    fn is_converted_in_comparison(&self, values: &[Value]) -> bool {
        values.iter().any(|value| self.is_tagged_tuple(value))
            && values
                .iter()
                .any(|value| !matches!(value, Value::Function(_)))
    }

    fn is_tagged_tuple(&self, value: &Value) -> bool {
        matches!(value, Value::Function(function) if function.class.get() != Class::Plain)
            && self.tags.get(value) != NO_CM
    }

    // `UnionValue.union`.
    fn union(&mut self, sets: &Value) -> R<CVal> {
        if let Value::Set(elements) = sets
            && elements
                .iter()
                .all(|element| matches!(element, Value::Set(_)))
        {
            let mut all = Vec::new();
            for element in elements.iter() {
                if let Value::Set(inner) = element {
                    all.extend(inner.iter().cloned());
                }
            }
            let result = self.set_of(all)?;
            let cm = self.tags.get(sets);
            return Ok(self.tagged(result, cm));
        }
        if self.tags.get(sets) != NO_CM {
            return no("a UNION TLC keeps lazy (UnionValue)");
        }
        Ok(CVal::V(Value::Lazy(Rc::new(Lazy::Union(sets.clone())))))
    }

    fn domain(&mut self, function: &CVal) -> R<Value> {
        match function {
            CVal::Fcn(lambda) => {
                if let Some(rcd) = &*lambda.fcn_rcd.borrow() {
                    return self.domain(&CVal::V(rcd.clone()));
                }
                if lambda.params.len() != 1 || lambda.params[0].1 {
                    return no("DOMAIN of a lazy function of several parameters");
                }
                Ok(lambda.params[0].2.clone())
            }
            CVal::V(Value::Function(function)) => Ok(match function.interval {
                Some((low, high)) => Value::Interval(low, high),
                None => Value::Set(Rc::new(function.domain.clone())),
            }),
            CVal::V(_) => no("DOMAIN of a value TLC can't take it of"),
        }
    }

    // `S \ T`, `S \cap T`, `S \cup T`: a set enumeration or an interval combines eagerly.
    fn set_operation(&mut self, code: Code, left: Value, right: Value, cm: Cm) -> R<Value> {
        let reducible = |value: &Value| matches!(value, Value::Set(_) | Value::Interval(..));
        if reducible(&left) {
            return self.reduce(code, &left, &right);
        }
        if code != Code::Setdiff && reducible(&right) {
            return self.reduce(code, &right, &left);
        }
        if self.tags.get(&left) != NO_CM || self.tags.get(&right) != NO_CM {
            return no("a set operation TLC keeps lazy of a set with a cost model");
        }
        let value = Value::Lazy(Rc::new(match code {
            Code::Setdiff => Lazy::Diff(left, right),
            Code::Cap => Lazy::Cap(left, right),
            _ => Lazy::Cup(left, right),
        }));
        if code == Code::Cup {
            self.tags.tag(&value, cm);
        }
        Ok(value)
    }

    // `Reducible.diff`, `cap` and `cup` of a set enumeration or an interval.
    fn reduce(&mut self, code: Code, set: &Value, other: &Value) -> R<Value> {
        let own_cm = self.tags.get(set);
        let own = elements(set)?;
        match code {
            Code::Setdiff | Code::Cap => {
                let mut kept = Vec::new();
                for element in own.iter() {
                    if self.member(element, other)? == (code == Code::Cap) {
                        kept.push(element.clone());
                    }
                }
                let result = self.set_of(kept)?;
                if matches!(set, Value::Set(_)) {
                    self.tags.tag(&result, own_cm);
                }
                Ok(result)
            }
            _ => {
                if matches!(set, Value::Set(_)) && own.is_empty() {
                    return Ok(other.clone());
                }
                if let Value::Interval(low, high) = set
                    && let Value::Interval(other_low, other_high) = other
                    && low <= high
                    && other_low <= other_high
                    && i64::from(*other_low) <= i64::from(*high) + 1
                    && i64::from(*low) <= i64::from(*other_high) + 1
                {
                    return Ok(Value::Interval(*low.min(other_low), *high.max(other_high)));
                }
                if !matches!(other, Value::Set(_) | Value::Interval(..)) {
                    return no("a union TLC keeps lazy (SetCupValue)");
                }
                let mut all = own.to_vec();
                let mut enumeration = self.elements(other, false)?;
                while let Some(element) = self.next(&mut enumeration)? {
                    all.push(element);
                }
                self.set_of(all)
            }
        }
    }

    // --- functions ---

    /// `FunctionValue.apply`.
    fn apply(&mut self, function: &CVal, argument: &Value, control: u8) -> R<CVal> {
        let lambda = match function {
            CVal::V(Value::Function(function)) => {
                return match find_key(function, argument)? {
                    Some(position) => Ok(CVal::V(function.range[position].clone())),
                    None => no("a function applied outside its domain"),
                };
            }
            CVal::V(Value::Lambda(lambda)) => {
                // A function TLC computed at startup, which counts nothing.
                return Ok(CVal::V(self.old.apply_lambda(lambda, argument)?));
            }
            CVal::V(_) => return no("a non-function applied as a function"),
            CVal::Fcn(lambda) => lambda,
        };
        if let Some(rcd) = lambda.fcn_rcd.borrow().clone() {
            return self.apply(&CVal::V(rcd), argument, control);
        }
        if lambda.params.len() != 1 || lambda.params[0].1 {
            return no("a lazy function of several parameters applied");
        }
        let (syms, _, domain) = &lambda.params[0];
        if !self.member(argument, domain)? {
            return no("a function applied outside its domain");
        }
        let mut c1 = lambda.ctx.clone();
        if let Some(name) = lambda.recursive {
            c1 = c1.bind_value(name, CVal::Fcn(Rc::clone(lambda)));
        }
        let c1 = c1.bind_value(syms[0], CVal::V(argument.clone()));
        let body = lambda.body;
        let (s0, s1) = (lambda.s0.clone(), lambda.s1.clone());
        self.eval(body, &c1, &s0, s1.as_ref(), control, lambda.cm)
    }

    /// `FcnLambdaValue.toFcnRcd`.
    fn fcn_rcd_of(&mut self, lambda: &Rc<FcnLambda>) -> R<Value> {
        if let Some(rcd) = &*lambda.fcn_rcd.borrow() {
            return Ok(rcd.clone());
        }
        if lambda.params.len() != 1 || lambda.params[0].1 || lambda.params[0].0.len() != 1 {
            return no("a function of several parameters TLC builds");
        }
        let (syms, _, domain) = &lambda.params[0];
        let mut keys = Vec::new();
        let mut values = Vec::new();
        let mut enumeration = self.elements(domain, false)?;
        let (s0, s1) = (lambda.s0.clone(), lambda.s1.clone());
        while let Some(key) = self.next(&mut enumeration)? {
            let mut c1 = lambda.ctx.clone();
            if let Some(name) = lambda.recursive {
                c1 = c1.bind_value(name, CVal::Fcn(Rc::clone(lambda)));
            }
            let c1 = c1.bind_value(syms[0], CVal::V(key.clone()));
            values.push(self.eval_value(
                lambda.body,
                &c1,
                &s0,
                s1.as_ref(),
                lambda.control,
                lambda.cm,
            )?);
            keys.push(key);
        }
        let size = keys.len() as u64;
        let function = match domain {
            Value::Interval(low, _) => Value::over_interval(*low, values, Class::Plain),
            _ => sorted_function(keys, values, Class::Plain)?,
        };
        self.model.add_secondary(lambda.cm, size);
        self.tags.tag(&function, lambda.cm);
        *lambda.fcn_rcd.borrow_mut() = Some(function.clone());
        Ok(function)
    }

    // `[f EXCEPT ![a]... = e, ...]`.
    fn except(
        &mut self,
        expr: SId,
        c: &Ctx,
        s0: &St,
        s1: Option<&St>,
        control: u8,
        cm: Cm,
    ) -> R<CVal> {
        let args = self.appl(expr).1;
        let mut result = self.eval_value(args[0].expect("a function"), c, s0, s1, control, cm)?;
        for pair in args[1..].iter().flatten() {
            let pair_args = self.appl(*pair).1;
            let seq = pair_args[0].expect("a path");
            let pair_cm = self.get(cm, *pair);
            let seq_cm = self.get(pair_cm, seq);
            let mut path = Vec::new();
            for step in self.appl(seq).1.iter().flatten() {
                path.push(self.eval_value(*step, c, s0, s1, control, seq_cm)?);
            }
            let Some(at) = select_path(&result, &path)? else {
                return no("an EXCEPT of a key the function lacks, which TLC warns of");
            };
            let c1 = c.cons(Key::At, Bind::Val(CVal::V(at)));
            let pair_cm = self.get(cm, *pair);
            let value = self.eval_value(
                pair_args[1].expect("a value"),
                &c1,
                s0,
                s1,
                control,
                pair_cm,
            )?;
            result = replace_path(&result, &path, value)?;
        }
        Ok(CVal::V(result))
    }

    // --- enumerations, as TLC's `ValueEnumeration`s count them ---

    /// `Enumerable.elements()`, or with `is_normalized` `elements(Ordering.NORMALIZED)`.
    pub(crate) fn elements(&mut self, set: &Value, is_normalized: bool) -> R<Enumeration> {
        let cm = self.tags.get(set);
        match set {
            Value::Set(elements) => Ok(Enumeration::SetEnum {
                elements: Rc::clone(elements),
                index: 0,
                cm,
            }),
            Value::Interval(low, high) => Ok(Enumeration::Interval {
                low: *low,
                high: *high,
                index: i64::from(*low),
                cm,
            }),
            Value::Lazy(lazy) if cm == NO_CM && !self.has_tagged_parts(lazy) => {
                // A set computed at startup counts nothing as it is enumerated, and its parts
                // are TLC's normalized order where its own is.
                if !is_normalized && !super::is_streamed_in_order(set) {
                    return no("a set TLC streams in an order of its own");
                }
                Ok(Enumeration::List {
                    elements: elements(set)?.to_vec(),
                    index: 0,
                })
            }
            Value::Lazy(lazy) => {
                if is_normalized {
                    // `EnumerableValue.elements(NORMALIZED)` converts to a set enumeration,
                    // but SUBSET's own enumeration is normalized.
                    if let Lazy::Subset(_) = &**lazy {
                        return self.lazy_elements(set, lazy, cm);
                    }
                    let enumerated = self.set_enum_of(set)?;
                    return self.elements(&enumerated, false);
                }
                self.lazy_elements(set, lazy, cm)
            }
            _ => no("an enumeration of a value that isn't a set"),
        }
    }

    fn has_tagged_parts(&self, lazy: &Lazy) -> bool {
        let parts: Vec<&Value> = match lazy {
            Lazy::Subset(base) => vec![base],
            Lazy::FunctionSet(domain, range) => vec![domain, range],
            Lazy::RecordSet(fields, _) => fields.iter().map(|(_, set)| set).collect(),
            Lazy::Product(sets) => sets.iter().collect(),
            Lazy::Cap(left, right) | Lazy::Cup(left, right) | Lazy::Diff(left, right) => {
                vec![left, right]
            }
            Lazy::Union(sets) => vec![sets],
            _ => Vec::new(),
        };
        parts.into_iter().any(|part| {
            self.tags.get(part) != NO_CM
                || matches!(part, Value::Lazy(inner) if self.has_tagged_parts(inner))
        })
    }

    fn lazy_elements(&mut self, set: &Value, lazy: &Lazy, cm: Cm) -> R<Enumeration> {
        match lazy {
            Lazy::Subset(base) => {
                let base = self.set_enum_of(base)?;
                let elements = elements(&base)?.to_vec();
                Ok(Enumeration::Subsets {
                    elements,
                    k: 0,
                    indices: Vec::new(),
                    cm,
                })
            }
            Lazy::FunctionSet(domain, range) => {
                if crate::eval::is_empty(set)? {
                    return Ok(Enumeration::List {
                        elements: Vec::new(),
                        index: 0,
                    });
                }
                let interval = match domain {
                    Value::Interval(low, high) => Some((*low, *high)),
                    _ => None,
                };
                let keys = match domain {
                    Value::Interval(..) => Vec::new(),
                    _ => {
                        let keys = self.set_enum_of(domain)?;
                        elements(&keys)?.to_vec()
                    }
                };
                let count = match interval {
                    Some((low, high)) => (i64::from(high) - i64::from(low) + 1).max(0) as usize,
                    None => keys.len(),
                };
                let mut parts = Vec::with_capacity(count);
                for _ in 0..count {
                    parts.push(range.clone());
                }
                let product = self.product(parts)?;
                Ok(Enumeration::Product {
                    product,
                    make: Make::Function { keys, interval },
                    cm,
                })
            }
            Lazy::RecordSet(fields, _) => {
                if crate::eval::is_empty(set)? {
                    return Ok(Enumeration::List {
                        elements: Vec::new(),
                        index: 0,
                    });
                }
                let names = fields.iter().map(|(name, _)| Rc::clone(name)).collect();
                let product = self.product(fields.iter().map(|(_, set)| set.clone()).collect())?;
                Ok(Enumeration::Product {
                    product,
                    make: Make::Record(names),
                    cm,
                })
            }
            Lazy::Product(sets) => {
                if crate::eval::is_empty(set)? {
                    return Ok(Enumeration::List {
                        elements: Vec::new(),
                        index: 0,
                    });
                }
                let product = self.product(sets.clone())?;
                Ok(Enumeration::Product {
                    product,
                    make: Make::Tuple,
                    cm,
                })
            }
            _ => no("an enumeration of a lazy set the port doesn't follow"),
        }
    }

    // The nested enumerations of a set of functions, records or tuples, each taking its first
    // element; none where one is empty.
    fn product(&mut self, sets: Vec<Value>) -> R<Option<Product>> {
        let mut enums = Vec::with_capacity(sets.len());
        let mut current = Vec::with_capacity(sets.len());
        for set in &sets {
            let mut enumeration = self.elements(set, false)?;
            match self.next(&mut enumeration)? {
                Some(first) => {
                    enums.push(enumeration);
                    current.push(first);
                }
                None => return Ok(None),
            }
        }
        Ok(Some(Product {
            enums,
            current,
            is_done: false,
        }))
    }

    /// `ValueEnumeration.reset`: a product's parts reset and take their first elements again.
    fn reset(&mut self, enumeration: &mut Enumeration) -> R<()> {
        match enumeration {
            Enumeration::SetEnum { index, .. } => *index = 0,
            Enumeration::Interval { low, index, .. } => *index = i64::from(*low),
            Enumeration::List { index, .. } => *index = 0,
            Enumeration::Subsets { k, indices, .. } => {
                *k = 0;
                indices.clear();
            }
            Enumeration::Product { product, .. } => {
                if let Some(state) = product {
                    for position in 0..state.enums.len() {
                        self.reset(&mut state.enums[position])?;
                        match self.next(&mut state.enums[position])? {
                            Some(element) => state.current[position] = element,
                            None => return no("a reset enumeration that is empty"),
                        }
                    }
                    state.is_done = false;
                }
            }
        }
        Ok(())
    }

    /// `ValueEnumeration.nextElement`.
    pub(crate) fn next(&mut self, enumeration: &mut Enumeration) -> R<Option<Value>> {
        match enumeration {
            Enumeration::SetEnum {
                elements,
                index,
                cm,
            } => {
                self.model.add_secondary(*cm, 1);
                let element = elements.get(*index).cloned();
                if element.is_some() {
                    *index += 1;
                }
                Ok(element)
            }
            Enumeration::Interval {
                low: _,
                high,
                index,
                cm,
            } => {
                if *index > i64::from(*high) {
                    return Ok(None);
                }
                self.model.add_secondary(*cm, 1);
                let current = *index as i32;
                *index += 1;
                Ok(Some(Value::Int(current)))
            }
            Enumeration::List { elements, index } => {
                let element = elements.get(*index).cloned();
                if element.is_some() {
                    *index += 1;
                }
                Ok(element)
            }
            Enumeration::Subsets {
                elements,
                k,
                indices,
                cm,
            } => {
                let n = elements.len();
                if n == 0 {
                    if *k > 0 {
                        return Ok(None);
                    }
                    *k = 1;
                    let empty = Value::empty_set();
                    self.tags.tag(&empty, *cm);
                    return Ok(Some(empty));
                }
                if *k > n {
                    return Ok(None);
                }
                if *k == 0 {
                    *k = 1;
                    *indices = (0..1).collect();
                    let empty = Value::empty_set();
                    self.tags.tag(&empty, *cm);
                    return Ok(Some(empty));
                }
                let size = *k;
                let subset: Vec<Value> = indices
                    .iter()
                    .map(|&index| elements[index].clone())
                    .collect();
                let result = Value::Set(Rc::new(subset));
                self.tags.tag(&result, *cm);
                // The next subset of this size, or the first of the next size.
                let mut position = size;
                while position > 0 && indices[position - 1] == n - size + position - 1 {
                    position -= 1;
                }
                if position == 0 {
                    *k = size + 1;
                    *indices = (0..size + 1).collect();
                } else {
                    indices[position - 1] += 1;
                    for later in position..size {
                        indices[later] = indices[later - 1] + 1;
                    }
                }
                Ok(Some(result))
            }
            Enumeration::Product { product, make, cm } => {
                let Some(state) = product else {
                    return Ok(None);
                };
                if state.is_done {
                    return Ok(None);
                }
                let values = state.current.clone();
                if state.current.is_empty() {
                    state.is_done = true;
                } else {
                    // The function set counts each function's values; an empty domain once.
                    for position in (0..state.current.len()).rev() {
                        match self.next(&mut state.enums[position])? {
                            Some(element) => {
                                state.current[position] = element;
                                break;
                            }
                            None if position == 0 => {
                                state.is_done = true;
                                break;
                            }
                            None => {
                                self.reset(&mut state.enums[position])?;
                                state.current[position] =
                                    self.next(&mut state.enums[position])?.ok_or_else(|| {
                                        Halt::No("an enumeration that ran out".into())
                                    })?;
                            }
                        }
                    }
                }
                let count = values.len().max(1) as u64;
                let made = match make {
                    Make::Function { keys, interval } => match interval {
                        Some((low, _)) => Value::over_interval(*low, values, Class::Plain),
                        None => Value::function(keys.clone(), values, Class::Plain),
                    },
                    Make::Record(names) => {
                        Value::record(names.iter().cloned().zip(values).collect())?
                    }
                    Make::Tuple => Value::tuple(values),
                };
                self.model.add_secondary(*cm, count);
                self.tags.tag(&made, *cm);
                Ok(Some(made))
            }
        }
    }

    /// `toSetEnum` of a set, which counts the elements of a lazy set into its cost model.
    pub(crate) fn set_enum_of(&mut self, set: &Value) -> R<Value> {
        match set {
            Value::Set(_) => Ok(set.clone()),
            Value::Interval(..) => Ok(Value::Set(elements(set)?)),
            Value::Lazy(lazy) => {
                let cm = self.tags.get(set);
                if cm == NO_CM && !self.has_tagged_parts(lazy) {
                    return Ok(Value::Set(elements(set)?));
                }
                let mut enumeration = self.lazy_elements(set, lazy, cm)?;
                let mut all = Vec::new();
                while let Some(element) = self.next(&mut enumeration)? {
                    all.push(element);
                }
                let size = all.len() as u64;
                self.model.add_secondary(cm, size);
                let result = self.set_of(all)?;
                self.tags.tag(&result, cm);
                Ok(result)
            }
            _ => no("a set enumeration of a value that isn't a set"),
        }
    }

    // --- comparison ---

    /// `toFcnRcd`, `toTuple` or `toRcd` of a function of another class, which counts into the
    /// cost model of the function converted.
    fn count_conversion(&mut self, value: &Value) -> R<()> {
        let cm = self.tags.get(value);
        if let Value::Function(function) = value {
            self.model.add_secondary(cm, function.domain.len() as u64);
        }
        Ok(())
    }

    /// `Value.equals`, with the conversions TLC makes between classes of functions.
    pub(crate) fn tlc_equals(&mut self, left: &Value, right: &Value) -> R<bool> {
        if self.is_converted_in_comparison(&[left.clone(), right.clone()]) {
            return no("an equality of a tuple or a record with another value");
        }
        match (left, right) {
            (Value::Function(own), Value::Function(other)) => {
                let (own_class, other_class) = (own.class.get(), other.class.get());
                let is_plain = |class: Class| matches!(class, Class::Plain | Class::Lambda);
                if own_class != other_class && !(is_plain(own_class) && is_plain(other_class)) {
                    // `TupleValue.equals`: the other as a tuple; `FcnRcdValue.equals`: the other
                    // as a function; `RecordValue.equals`: the other as a record.
                    match (own_class, other_class) {
                        (Class::Tuple, _) | (Class::Record, _) => self.count_conversion(right)?,
                        (_, Class::Tuple) | (_, Class::Record) => self.count_conversion(right)?,
                        _ => {}
                    }
                    if self.tags.get(left) != NO_CM || self.tags.get(right) != NO_CM {
                        return no("an equality of functions of different classes");
                    }
                }
                if own.domain.len() != other.domain.len() {
                    return primitive_equals(left, right);
                }
                for (own_key, other_key) in own.domain.iter().zip(&other.domain) {
                    if !primitive_equals(own_key, other_key)? {
                        return primitive_equals(left, right);
                    }
                }
                for (own_value, other_value) in own.range.iter().zip(&other.range) {
                    if !self.tlc_equals(own_value, other_value)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (Value::Set(own), Value::Set(other)) => {
                if own.len() != other.len() {
                    return Ok(false);
                }
                for (own_element, other_element) in own.iter().zip(other.iter()) {
                    if !self.tlc_equals(own_element, other_element)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (Value::Lazy(_), _) | (_, Value::Lazy(_))
                if self.tags.get(left) != NO_CM || self.tags.get(right) != NO_CM =>
            {
                no("an equality of a lazy set with a cost model")
            }
            _ => primitive_equals(left, right),
        }
    }

    fn tlc_equals_cval(&mut self, left: &CVal, right: &CVal) -> R<bool> {
        let left = match left {
            CVal::Fcn(lambda) => self.fcn_rcd_of(lambda)?,
            CVal::V(value) => value.clone(),
        };
        let right = match right {
            CVal::Fcn(lambda) => self.fcn_rcd_of(lambda)?,
            CVal::V(value) => value.clone(),
        };
        self.tlc_equals(&left, &right)
    }

    /// `Value.member`.
    pub(crate) fn member(&mut self, element: &Value, set: &Value) -> R<bool> {
        if let Value::Function(function) = element
            && self.tags.get(element) != NO_CM
            && let Value::Set(elements) = set
            && elements.iter().any(|held| {
                matches!(held, Value::Function(other) if other.class.get() != function.class.get())
            })
        {
            return no("a membership of a function among functions of other classes");
        }
        if let Value::Set(elements) = set
            && match element {
                Value::Function(_) => {
                    self.is_tagged_tuple(element)
                        && elements
                            .iter()
                            .any(|held| !matches!(held, Value::Function(_)))
                }
                _ => elements.iter().any(|held| self.is_tagged_tuple(held)),
            }
        {
            return no("a membership of a tuple or a record among other values");
        }
        let Value::Lazy(lazy) = set else {
            return Ok(is_member(element, set)?);
        };
        match &**lazy {
            // `SubsetValue.member` enumerates the value.
            Lazy::Subset(base)
                if matches!(
                    element,
                    Value::Set(_) | Value::Interval(..) | Value::Lazy(_)
                ) =>
            {
                let mut enumeration = self.elements(element, false)?;
                while let Some(held) = self.next(&mut enumeration)? {
                    if !self.member(&held, base)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Lazy::Cup(left, right) => {
                Ok(self.member(element, left)? || self.member(element, right)?)
            }
            Lazy::Cap(left, right) => {
                Ok(self.member(element, left)? && self.member(element, right)?)
            }
            Lazy::Diff(left, right) => {
                Ok(self.member(element, left)? && !self.member(element, right)?)
            }
            // `UnionValue.member` enumerates its set of sets.
            Lazy::Union(sets) => {
                let mut enumeration = self.elements(sets, false)?;
                while let Some(held) = self.next(&mut enumeration)? {
                    if self.member(element, &held)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            // `SetOfFcnsValue.member`, `SetOfRcdsValue.member` and `SetOfTuplesValue.member`
            // convert the value, which counts, then test its values.
            Lazy::FunctionSet(domain, range) => {
                let Value::Function(function) = element else {
                    return Ok(is_member(element, set)?);
                };
                self.check_converted(element)?;
                if matches!(function.class.get(), Class::Tuple | Class::Record) {
                    self.count_to_fcn_rcd(element);
                }
                let own_domain = match function.interval {
                    Some((low, high)) => Value::Interval(low, high),
                    None => self.set_of(function.domain.clone())?,
                };
                if !self.tlc_equals(domain, &own_domain)? {
                    return Ok(false);
                }
                for value in function.range.iter() {
                    if !self.member(value, range)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Lazy::RecordSet(fields, _) => {
                let Value::Function(function) = element else {
                    return Ok(is_member(element, set)?);
                };
                self.check_converted(element)?;
                match function.class.get() {
                    Class::Record => {}
                    Class::Plain
                        if function
                            .domain
                            .iter()
                            .all(|key| matches!(key, Value::Str(_))) =>
                    {
                        let cm = self.tags.get(element);
                        self.model.add_secondary(cm, function.domain.len() as u64);
                    }
                    _ if function.domain.is_empty() => {}
                    _ => return Ok(is_member(element, set)?),
                }
                if fields.len() != function.domain.len() {
                    return Ok(false);
                }
                // Both in TLC's order of the names.
                for ((name, values), (key, value)) in fields
                    .iter()
                    .zip(function.domain.iter().zip(function.range.iter()))
                {
                    if !primitive_equals(&Value::Str(Rc::clone(name)), key)?
                        || !self.member(value, values)?
                    {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Lazy::Product(sets) => {
                let Value::Function(function) = element else {
                    return Ok(is_member(element, set)?);
                };
                self.check_converted(element)?;
                match function.class.get() {
                    Class::Tuple => {}
                    _ if function.domain.is_empty() => {}
                    Class::Plain => self.count_to_tuple(element),
                    _ => return Ok(is_member(element, set)?),
                }
                let Some(items) = tuple_items(element) else {
                    return Ok(is_member(element, set)?);
                };
                if items.len() != sets.len() {
                    return Ok(false);
                }
                for (item, held) in items.iter().zip(sets.iter()) {
                    if !self.member(item, held)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            // `SeqValue.member` converts the value to a tuple, then tests its elements.
            Lazy::Seq(range) => {
                if !matches!(element, Value::Function(_)) {
                    return Ok(is_member(element, set)?);
                }
                self.check_converted(element)?;
                self.count_to_tuple(element);
                let Some(items) = tuple_items(element) else {
                    return Ok(is_member(element, set)?);
                };
                for item in items.iter() {
                    if !self.member(item, range)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            // `SetPredValue.member` tests the value against its set, then its predicate, which
            // counts nothing.
            Lazy::Filter(base, _) => {
                Ok(self.member(element, base)? && self.old.member(element, set)?)
            }
            _ => Ok(is_member(element, set)?),
        }
    }

    /// Declines a conversion TLC caches for a function it keeps lazy, which counts only once.
    fn check_converted(&mut self, element: &Value) -> R<()> {
        if let Value::Function(function) = element
            && function.class.get() == Class::Lambda
            && self.tags.get(element) != NO_CM
        {
            return no("a membership of a lazy function with a cost model");
        }
        Ok(())
    }

    // `Enumerable.isSubsetEq`.
    fn is_subseteq(&mut self, left: &Value, right: &Value) -> R<bool> {
        if let (Value::Interval(low, high), Value::Interval(other_low, other_high)) = (left, right)
            && other_low <= low
            && other_high >= high
        {
            return Ok(true);
        }
        if let Value::Lazy(lazy) = left
            && matches!(&**lazy, Lazy::Subset(_))
        {
            return no("SUBSET S \\subseteq T");
        }
        let mut enumeration = self.elements(left, false)?;
        while let Some(element) = self.next(&mut enumeration)? {
            if !self.member(&element, right)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    // --- contexts (`ContextEnumerator`), normalized as `Tool.contexts` asks ---

    pub(crate) fn contexts(
        &mut self,
        bounds: &[SBound],
        c: &Ctx,
        s0: &St,
        s1: Option<&St>,
        control: u8,
        cm: Cm,
    ) -> R<Contexts> {
        let mut vars = Vec::new();
        let mut enums = Vec::new();
        for bound in bounds {
            let set = self.eval_value(bound.set, c, s0, s1, control, cm)?;
            if bound.is_tuple {
                vars.push((bound.syms.clone(), true));
                enums.push(self.elements(&set, true)?);
            } else {
                for &sym in &bound.syms {
                    vars.push((vec![sym], false));
                    enums.push(self.elements(&set, true)?);
                }
            }
        }
        let mut current = Vec::with_capacity(enums.len());
        let mut is_done = false;
        for enumeration in &mut enums {
            match self.next(enumeration)? {
                Some(element) => current.push(element),
                None => {
                    is_done = true;
                    break;
                }
            }
        }
        Ok(Contexts {
            ctx: c.clone(),
            vars,
            enums,
            current,
            is_done,
        })
    }

    pub(crate) fn next_context(&mut self, contexts: &mut Contexts) -> R<Option<Ctx>> {
        if contexts.is_done {
            return Ok(None);
        }
        let mut c1 = contexts.ctx.clone();
        for (index, (syms, is_tuple)) in contexts.vars.iter().enumerate() {
            let value = &contexts.current[index];
            if *is_tuple {
                let Some(items) = tuple_items(value) else {
                    return no("a tuple bound to a value that isn't one");
                };
                if items.len() != syms.len() {
                    return no("a tuple bound to one of another length");
                }
                for (sym, item) in syms.iter().zip(items) {
                    c1 = c1.bind_value(*sym, CVal::V(item.clone()));
                }
            } else {
                c1 = c1.bind_value(syms[0], CVal::V(value.clone()));
            }
        }
        let count = contexts.enums.len();
        for index in 0..count {
            match self.next(&mut contexts.enums[index])? {
                Some(element) => {
                    contexts.current[index] = element;
                    break;
                }
                None if index == count - 1 => {
                    contexts.is_done = true;
                    break;
                }
                None => {
                    self.reset(&mut contexts.enums[index])?;
                    match self.next(&mut contexts.enums[index])? {
                        Some(element) => contexts.current[index] = element,
                        None => return no("an enumeration that ran out"),
                    }
                }
            }
        }
        Ok(Some(c1))
    }

    // --- the initial predicate (`getInitStates`) ---

    /// `Tool.getInitStates(IStateFunctor)` over the initial predicates in order.
    pub(crate) fn init_states(
        &mut self,
        inits: &[Action],
        functor: &mut InitFunctor<'_, 'a, 'ir>,
    ) -> R<()> {
        let Some((first, rest)) = inits.split_first() else {
            return Ok(());
        };
        let mut acts = Acts::default();
        for action in rest.iter().rev() {
            acts = acts.cons(action.pred, action.ctx.clone(), action.cm, Kind::Pred);
        }
        let mut ps: St = vec![None; self.width];
        self.init_walk(
            first.pred,
            &acts,
            &first.ctx.clone(),
            &mut ps,
            functor,
            first.cm,
        )
    }

    fn init_walk(
        &mut self,
        init: SId,
        acts: &Acts,
        c: &Ctx,
        ps: &mut St,
        functor: &mut InitFunctor<'_, 'a, 'ir>,
        cm: Cm,
    ) -> R<()> {
        match &self.sem.node(init).kind {
            SKind::Appl { .. } => self.init_appl(init, acts, c, ps, functor, cm),
            SKind::Let { body, .. } => self.init_walk(*body, acts, c, ps, functor, cm),
            _ => no("an initial predicate that isn't a boolean expression"),
        }
    }

    fn init_rest(
        &mut self,
        acts: &Acts,
        ps: &mut St,
        functor: &mut InitFunctor<'_, 'a, 'ir>,
        cm: Cm,
    ) -> R<()> {
        let Some(item) = &acts.0 else {
            self.model.increment(cm);
            let root = self.model.root_of(cm);
            self.model.increment(root);
            return functor(self, ps);
        };
        if ps.iter().all(Option::is_some) {
            let mut acts = acts.clone();
            let empty = Rc::clone(&self.empty);
            while let Some(item) = acts.0.clone() {
                let holds = self.eval_bool(
                    item.pred,
                    &item.ctx.clone(),
                    ps,
                    Some(&empty),
                    INIT,
                    item.cm,
                )?;
                if !holds {
                    let root = self.model.root_of(cm);
                    self.model.add_secondary(root, 1);
                    return Ok(());
                }
                acts = item.next.clone();
            }
            self.model.increment(cm);
            let root = self.model.root_of(cm);
            self.model.increment(root);
            return functor(self, ps);
        }
        let item = Rc::clone(item);
        self.init_walk(
            item.pred,
            &item.next,
            &item.ctx.clone(),
            ps,
            functor,
            item.cm,
        )
    }

    fn init_appl(
        &mut self,
        init: SId,
        acts: &Acts,
        c: &Ctx,
        ps: &mut St,
        functor: &mut InitFunctor<'_, 'a, 'ir>,
        cm: Cm,
    ) -> R<()> {
        let cm = self.get(cm, init);
        self.mismatch()?;
        let (op, args, bounds, _) = self.appl(init);
        let empty = Rc::clone(&self.empty);
        let code = match op {
            Op::Code(code) => code,
            _ => {
                // `getInitStatesAppl` with opcode 0: an operator's body, a lazy value not yet
                // computed, or a value that must be a boolean.
                match op {
                    Op::Def(def)
                        if c.lookup(Key::Def(def)).is_none() && self.constant(def)?.is_none() =>
                    {
                        let c1 = self.op_context(def, args, c, cm);
                        let body = self.sem.def(def).body.expect("a body");
                        return self.init_walk(body, acts, &c1, ps, functor, cm);
                    }
                    Op::Substituted(def) => {
                        let c1 = self.op_context(def, args, c, cm);
                        let body = self.sem.def(def).body.expect("a body");
                        return self.init_walk(body, acts, &c1, ps, functor, cm);
                    }
                    Op::Sym(_) | Op::Def(_) => {
                        let key = match op {
                            Op::Sym(sym) => Key::Sym(sym),
                            Op::Def(def) => Key::Def(def),
                            _ => unreachable!("a name"),
                        };
                        if let Some(Bind::Lazy(lazy)) = c.lookup(key) {
                            match self.cached(&lazy, ps, None, CLEAR) {
                                None => {
                                    let ctx = lazy.ctx.clone();
                                    return self.init_walk(lazy.expr, acts, &ctx, ps, functor, cm);
                                }
                                Some(value) => {
                                    if value.boolean()? {
                                        return self.init_rest(acts, ps, functor, cm);
                                    }
                                    return Ok(());
                                }
                            }
                        }
                    }
                    _ => {}
                }
                let value = match op {
                    Op::Builtin(index) => {
                        let mut values = Vec::with_capacity(args.len());
                        for arg in args {
                            values.push(self.eval_value(
                                arg.expect("an argument"),
                                c,
                                ps,
                                Some(&empty),
                                INIT,
                                cm,
                            )?);
                        }
                        CVal::V(self.builtin(index, values)?)
                    }
                    Op::Var(index) => match &ps[index as usize] {
                        Some(value) => CVal::V(value.clone()),
                        None => return fail("a variable TLC reads unassigned"),
                    },
                    Op::Const(index) => {
                        let Some(value) = self.sem.ir.constants[index as usize].value else {
                            return no("a constant the IR can't hold");
                        };
                        CVal::V(self.old.value(value)?)
                    }
                    Op::Def(def) => match self.constant(def)? {
                        Some(value) => CVal::V(value),
                        None => return no("a definition the walk can't take"),
                    },
                    Op::Sym(sym) => match c.lookup(Key::Sym(sym)) {
                        Some(Bind::Val(value)) => value,
                        _ => return no("a name bound outside what the port follows"),
                    },
                    _ => return no("an operator the walk can't take"),
                };
                if value.boolean()? {
                    return self.init_rest(acts, ps, functor, cm);
                }
                return Ok(());
            }
        };
        let arg = |index: usize| args[index].expect("an operand");
        match code {
            Code::DisjList | Code::Lor => {
                for operand in args.iter().flatten() {
                    self.init_walk(*operand, acts, c, ps, functor, cm)?;
                }
                Ok(())
            }
            Code::ConjList | Code::Land => {
                let mut acts1 = acts.clone();
                for operand in args[1..].iter().rev().flatten() {
                    let item_cm = self.get(cm, *operand);
                    acts1 = acts1.cons(*operand, c.clone(), item_cm, Kind::Conjunct);
                }
                self.init_walk(arg(0), &acts1, c, ps, functor, cm)
            }
            Code::BoundedExists => {
                let mut contexts = self.contexts(bounds, c, ps, Some(&empty), INIT, cm)?;
                while let Some(c1) = self.next_context(&mut contexts)? {
                    self.init_walk(arg(0), acts, &c1, ps, functor, cm)?;
                }
                Ok(())
            }
            Code::BoundedForall => {
                let mut contexts = self.contexts(bounds, c, ps, Some(&empty), INIT, cm)?;
                let Some(first) = self.next_context(&mut contexts)? else {
                    return self.init_rest(acts, ps, functor, cm);
                };
                let mut acts1 = acts.clone();
                while let Some(c2) = self.next_context(&mut contexts)? {
                    let item_cm = self.get(cm, arg(0));
                    acts1 = acts1.cons(arg(0), c2, item_cm, Kind::Pred);
                }
                self.init_walk(arg(0), &acts1, &first, ps, functor, cm)
            }
            Code::IfThenElse => {
                let branch = if self.eval_bool(arg(0), c, ps, Some(&empty), INIT, cm)? {
                    arg(1)
                } else {
                    arg(2)
                };
                self.init_walk(branch, acts, c, ps, functor, cm)
            }
            Code::Case => {
                let mut other = None;
                for pair in args.iter().flatten() {
                    let pair_args = self.appl(*pair).1;
                    match pair_args[0] {
                        None => other = pair_args[1],
                        Some(condition) => {
                            if self.eval_bool(condition, c, ps, Some(&empty), INIT, cm)? {
                                return self.init_walk(
                                    pair_args[1].expect("a value"),
                                    acts,
                                    c,
                                    ps,
                                    functor,
                                    cm,
                                );
                            }
                        }
                    }
                }
                match other {
                    Some(other) => self.init_walk(other, acts, c, ps, functor, cm),
                    None => no("a CASE with no condition true"),
                }
            }
            Code::Eq | Code::In => {
                let variable = self.get_var(arg(0), c, false)?;
                let Some(variable) = variable else {
                    let value = self.eval_appl_value(init, c, ps, Some(&empty), INIT, cm)?;
                    if !value.boolean()? {
                        return Ok(());
                    }
                    return self.init_rest(acts, ps, functor, cm);
                };
                let index = variable as usize;
                let right = self.eval_value(arg(1), c, ps, Some(&empty), INIT, cm)?;
                if code == Code::Eq {
                    match ps[index].clone() {
                        None => {
                            ps[index] = Some(right);
                            let result = self.init_rest(acts, ps, functor, cm);
                            ps[index] = None;
                            result
                        }
                        Some(held) => {
                            if !self.tlc_equals(&held, &right)? {
                                return Ok(());
                            }
                            self.init_rest(acts, ps, functor, cm)
                        }
                    }
                } else {
                    match ps[index].clone() {
                        None => {
                            let mut enumeration = self.elements(&right, false)?;
                            while let Some(element) = self.next(&mut enumeration)? {
                                ps[index] = Some(element);
                                let result = self.init_rest(acts, ps, functor, cm);
                                ps[index] = None;
                                result?;
                            }
                            Ok(())
                        }
                        Some(held) => {
                            if !self.member(&held, &right)? {
                                return Ok(());
                            }
                            self.init_rest(acts, ps, functor, cm)
                        }
                    }
                }
            }
            Code::Implies => {
                if self.eval_bool(arg(0), c, ps, Some(&empty), INIT, cm)? {
                    self.init_walk(arg(1), acts, c, ps, functor, cm)
                } else {
                    self.init_rest(acts, ps, functor, cm)
                }
            }
            Code::Subseteq => no("x \\subseteq S in the initial predicate"),
            Code::FcnApply => no("a function application in the initial predicate's walk"),
            _ => {
                let value = self.eval_appl_value(init, c, ps, Some(&empty), INIT, cm)?;
                if value.boolean()? {
                    return self.init_rest(acts, ps, functor, cm);
                }
                Ok(())
            }
        }
    }

    // `eval(init, ...)` of an application whose wrapper `cm` already is.
    fn eval_appl_value(
        &mut self,
        expr: SId,
        c: &Ctx,
        s0: &St,
        s1: Option<&St>,
        control: u8,
        cm: Cm,
    ) -> R<CVal> {
        let cm = self.get(cm, expr);
        self.eval_appl(expr, c, s0, s1, control, cm)
    }

    /// `getVar`: the variable an expression names, through 0-ary definitions and lazy values.
    fn get_var(&mut self, expr: SId, c: &Ctx, _cutoff: bool) -> R<Option<u32>> {
        let SKind::Appl { op, args, .. } = &self.sem.node(expr).kind else {
            return Ok(match &self.sem.node(expr).kind {
                SKind::Let { .. } => return no("a LET where TLC looks for a variable"),
                _ => None,
            });
        };
        if !args.is_empty() {
            return Ok(None);
        }
        match *op {
            Op::Var(index) => Ok(Some(index)),
            Op::Sym(sym) => match c.lookup(Key::Sym(sym)) {
                Some(Bind::Lazy(lazy)) => {
                    let ctx = lazy.ctx.clone();
                    self.get_var(lazy.expr, &ctx, false)
                }
                _ => Ok(None),
            },
            Op::Def(def) => match c.lookup(Key::Def(def)) {
                Some(Bind::Lazy(lazy)) => {
                    let ctx = lazy.ctx.clone();
                    self.get_var(lazy.expr, &ctx, false)
                }
                Some(Bind::Val(_)) => Ok(None),
                None if self.constant(def)?.is_some() => Ok(None),
                None => {
                    let body = self.sem.def(def).body.expect("a body");
                    self.get_var(body, c, false)
                }
            },
            Op::Substituted(def) => {
                let body = self.sem.def(def).body.expect("a body");
                self.get_var(body, c, false)
            }
            _ => Ok(None),
        }
    }

    /// `getPrimedVar`.
    fn get_primed_var(&mut self, expr: SId, c: &Ctx) -> R<Option<u32>> {
        match &self.sem.node(expr).kind {
            SKind::Let { defs, body } => {
                let mut c1 = c.clone();
                for &def in defs {
                    if self.sem.def(def).params.is_empty() {
                        let lazy = Rc::new(LazyCell {
                            expr: self.sem.def(def).body.expect("a body"),
                            ctx: c1.clone(),
                            cm: NO_CM,
                            cache: RefCell::new(None),
                        });
                        c1 = c1.cons(Key::Def(def), Bind::Lazy(lazy));
                    }
                }
                self.get_primed_var(*body, &c1)
            }
            SKind::Appl { op, args, .. } => {
                if *op == Op::Code(Code::Prime) {
                    return self.get_var(args[0].expect("an operand"), c, false);
                }
                if !args.is_empty() {
                    return Ok(None);
                }
                match *op {
                    Op::Sym(sym) => match c.lookup(Key::Sym(sym)) {
                        Some(Bind::Lazy(lazy)) => {
                            let ctx = lazy.ctx.clone();
                            self.get_primed_var(lazy.expr, &ctx)
                        }
                        _ => Ok(None),
                    },
                    Op::Def(def) => match c.lookup(Key::Def(def)) {
                        Some(Bind::Lazy(lazy)) => {
                            let ctx = lazy.ctx.clone();
                            self.get_primed_var(lazy.expr, &ctx)
                        }
                        Some(Bind::Val(_)) => Ok(None),
                        None if self.constant(def)?.is_some() => Ok(None),
                        None => {
                            let body = self.sem.def(def).body.expect("a body");
                            self.get_primed_var(body, c)
                        }
                    },
                    Op::Substituted(def) => {
                        let body = self.sem.def(def).body.expect("a body");
                        self.get_primed_var(body, c)
                    }
                    _ => Ok(None),
                }
            }
            _ => Ok(None),
        }
    }

    // --- the next-state relation (`getNextStates`) ---

    /// `Tool.getNextStates(action, ...)`: whether the walk added a successor.
    pub(crate) fn next_states(
        &mut self,
        action: &Action,
        s0: &St,
        functor: &mut NextFunctor<'_, 'a, 'ir>,
    ) -> R<bool> {
        let mut s1: St = vec![None; self.width];
        let ctx = action.ctx.clone();
        self.next_walk(
            action.pred,
            &Acts::default(),
            &ctx,
            s0,
            &mut s1,
            functor,
            action.cm,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn next_walk(
        &mut self,
        pred: SId,
        acts: &Acts,
        c: &Ctx,
        s0: &St,
        s1: &mut St,
        functor: &mut NextFunctor<'_, 'a, 'ir>,
        cm: Cm,
    ) -> R<bool> {
        match &self.sem.node(pred).kind {
            SKind::Appl { .. } => {
                let cm = self.get(cm, pred);
                self.mismatch()?;
                self.next_appl(pred, acts, c, s0, s1, functor, cm)
            }
            SKind::Let { body, .. } => self.next_walk(*body, acts, c, s0, s1, functor, cm),
            _ => no("a next-state relation that isn't a boolean expression"),
        }
    }

    // `getNextStates(action, acts, s0, s1, nss, cm)`: counts into `cm` where the rest added a
    // successor.
    fn next_rest(
        &mut self,
        acts: &Acts,
        s0: &St,
        s1: &mut St,
        functor: &mut NextFunctor<'_, 'a, 'ir>,
        cm: Cm,
    ) -> R<bool> {
        let added = self.next_rest0(acts, s0, s1, functor)?;
        if added {
            self.model.increment(cm);
        }
        Ok(added)
    }

    fn next_rest0(
        &mut self,
        acts: &Acts,
        s0: &St,
        s1: &mut St,
        functor: &mut NextFunctor<'_, 'a, 'ir>,
    ) -> R<bool> {
        let Some(item) = acts.0.clone() else {
            functor(self, s1)?;
            return Ok(true);
        };
        if self.is_warning_enabled && s1.iter().all(Option::is_some) {
            return self.next_all_assigned(acts, s0, s1, functor);
        }
        let c = item.ctx.clone();
        match item.kind {
            Kind::Conjunct | Kind::Pred => {
                self.next_walk(item.pred, &item.next, &c, s0, s1, functor, item.cm)
            }
            Kind::Unchanged => self.unchanged(item.pred, &item.next, &c, s0, s1, functor, item.cm),
            Kind::Changed => {
                let empty = Rc::clone(&self.empty);
                let before = self.eval(item.pred, &c, s0, Some(&empty), CLEAR, item.cm)?;
                let after = self.eval(item.pred, &c, s1, Some(&empty), CLEAR, item.cm)?;
                if !self.tlc_equals_cval(&before, &after)? {
                    return self.next_rest(&item.next, s0, s1, functor, item.cm);
                }
                Ok(false)
            }
        }
    }

    fn next_all_assigned(
        &mut self,
        acts: &Acts,
        s0: &St,
        s1: &mut St,
        functor: &mut NextFunctor<'_, 'a, 'ir>,
    ) -> R<bool> {
        let mut acts = acts.clone();
        while let Some(item) = acts.0.clone() {
            let c = item.ctx.clone();
            match item.kind {
                Kind::Conjunct | Kind::Pred => {
                    let next = s1.clone();
                    if !self.eval_bool(item.pred, &c, s0, Some(&next), CLEAR, item.cm)? {
                        return Ok(false);
                    }
                }
                Kind::Unchanged => {
                    return self.unchanged(item.pred, &item.next, &c, s0, s1, functor, item.cm);
                }
                Kind::Changed => {
                    let empty = Rc::clone(&self.empty);
                    let before = self.eval(item.pred, &c, s0, Some(&empty), CLEAR, item.cm)?;
                    let after = self.eval(item.pred, &c, s1, Some(&empty), CLEAR, item.cm)?;
                    if self.tlc_equals_cval(&before, &after)? {
                        return Ok(false);
                    }
                }
            }
            acts = item.next.clone();
        }
        functor(self, s1)?;
        Ok(true)
    }

    #[allow(clippy::too_many_arguments)]
    fn next_appl(
        &mut self,
        pred: SId,
        acts: &Acts,
        c: &Ctx,
        s0: &St,
        s1: &mut St,
        functor: &mut NextFunctor<'_, 'a, 'ir>,
        cm: Cm,
    ) -> R<bool> {
        let (op, args, bounds, _) = self.appl(pred);
        let arg = |index: usize| args[index].expect("an operand");
        let code = match op {
            Op::Code(code) => code,
            _ => {
                // A user-defined operator, walked into, or a value.
                match op {
                    Op::Def(def)
                        if c.lookup(Key::Def(def)).is_none() && self.constant(def)?.is_none() =>
                    {
                        let c1 = self.op_context(def, args, c, cm);
                        let body = self.sem.def(def).body.expect("a body");
                        return self.next_walk(body, acts, &c1, s0, s1, functor, cm);
                    }
                    Op::Substituted(def) => {
                        let c1 = self.op_context(def, args, c, cm);
                        let body = self.sem.def(def).body.expect("a body");
                        return self.next_walk(body, acts, &c1, s0, s1, functor, cm);
                    }
                    Op::Sym(sym) => {
                        if let Some(Bind::Lazy(lazy)) = c.lookup(Key::Sym(sym)) {
                            let cached = self.cached(&lazy, s0, Some(s1), CLEAR);
                            match cached {
                                None => {
                                    let ctx = lazy.ctx.clone();
                                    return self.next_walk(
                                        lazy.expr, acts, &ctx, s0, s1, functor, lazy.cm,
                                    );
                                }
                                Some(value) => {
                                    return self.next_value(value, acts, s0, s1, functor, cm);
                                }
                            }
                        }
                    }
                    Op::Def(def) => {
                        if let Some(Bind::Lazy(lazy)) = c.lookup(Key::Def(def)) {
                            let cached = self.cached(&lazy, s0, Some(s1), CLEAR);
                            match cached {
                                None => {
                                    let ctx = lazy.ctx.clone();
                                    return self.next_walk(
                                        lazy.expr, acts, &ctx, s0, s1, functor, lazy.cm,
                                    );
                                }
                                Some(value) => {
                                    return self.next_value(value, acts, s0, s1, functor, cm);
                                }
                            }
                        }
                    }
                    _ => {}
                }
                // The operator's value: a constant's, a variable's, a builtin's applied.
                let next = s1.clone();
                let value = match op {
                    Op::Builtin(index) => {
                        let mut values = Vec::with_capacity(args.len());
                        for arg in args {
                            values.push(self.eval_value(
                                arg.expect("an argument"),
                                c,
                                s0,
                                Some(&next),
                                CLEAR,
                                cm,
                            )?);
                        }
                        CVal::V(self.builtin(index, values)?)
                    }
                    Op::Var(index) => match &s0[index as usize] {
                        Some(value) => CVal::V(value.clone()),
                        None => return no("a variable TLC reads unassigned"),
                    },
                    Op::Const(index) => {
                        let Some(value) = self.sem.ir.constants[index as usize].value else {
                            return no("a constant the IR can't hold");
                        };
                        CVal::V(self.old.value(value)?)
                    }
                    Op::Def(def) => match self.constant(def)? {
                        Some(value) => CVal::V(value),
                        None => return no("a definition the walk can't take"),
                    },
                    Op::Sym(sym) => match c.lookup(Key::Sym(sym)) {
                        Some(Bind::Val(value)) => value,
                        _ => return no("a name bound outside what the port follows"),
                    },
                    _ => return no("an operator the walk can't take"),
                };
                return self.next_value(value, acts, s0, s1, functor, cm);
            }
        };
        match code {
            Code::ConjList | Code::Land => {
                let mut acts1 = acts.clone();
                for operand in args[1..].iter().rev().flatten() {
                    let item_cm = self.get(cm, *operand);
                    acts1 = acts1.cons(*operand, c.clone(), item_cm, Kind::Conjunct);
                }
                self.next_walk(arg(0), &acts1, c, s0, s1, functor, cm)
            }
            Code::DisjList | Code::Lor => {
                let mut added = false;
                for operand in args.iter().flatten() {
                    added |= self.next_walk(*operand, acts, c, s0, s1, functor, cm)?;
                }
                Ok(added)
            }
            Code::BoundedExists => {
                let next = s1.clone();
                let mut contexts = self.contexts(bounds, c, s0, Some(&next), CLEAR, cm)?;
                let mut added = false;
                while let Some(c1) = self.next_context(&mut contexts)? {
                    added |= self.next_walk(arg(0), acts, &c1, s0, s1, functor, cm)?;
                }
                Ok(added)
            }
            Code::BoundedForall => {
                let next = s1.clone();
                let mut contexts = self.contexts(bounds, c, s0, Some(&next), CLEAR, cm)?;
                let Some(first) = self.next_context(&mut contexts)? else {
                    return self.next_rest(acts, s0, s1, functor, cm);
                };
                let mut acts1 = acts.clone();
                while let Some(c2) = self.next_context(&mut contexts)? {
                    let item_cm = self.get(cm, arg(0));
                    acts1 = acts1.cons(arg(0), c2, item_cm, Kind::Pred);
                }
                self.next_walk(arg(0), &acts1, &first, s0, s1, functor, cm)
            }
            Code::FcnApply => {
                let next = s1.clone();
                let function = self.eval(arg(0), c, s0, Some(&next), KEEP_LAZY, cm)?;
                if let CVal::Fcn(lambda) = &function
                    && lambda.fcn_rcd.borrow().is_none()
                {
                    return no("a lazy function applied in the next-state relation's walk");
                }
                let argument = self.eval_value(arg(1), c, s0, Some(&next), CLEAR, cm)?;
                let holds = self.apply(&function, &argument, CLEAR)?.boolean()?;
                if holds {
                    return self.next_rest(acts, s0, s1, functor, cm);
                }
                Ok(false)
            }
            Code::AngleAct => {
                let item_cm = self.get(cm, arg(1));
                let acts1 = acts.cons(arg(1), c.clone(), item_cm, Kind::Changed);
                self.next_walk(arg(0), &acts1, c, s0, s1, functor, cm)
            }
            Code::SquareAct => {
                let added = self.next_walk(arg(0), acts, c, s0, s1, functor, cm)?;
                Ok(self.unchanged(arg(1), acts, c, s0, s1, functor, cm)? | added)
            }
            Code::IfThenElse => {
                let next = s1.clone();
                let branch = if self.eval_bool(arg(0), c, s0, Some(&next), CLEAR, cm)? {
                    arg(1)
                } else {
                    arg(2)
                };
                self.next_walk(branch, acts, c, s0, s1, functor, cm)
            }
            Code::Case => {
                let mut other = None;
                let mut last = None;
                for pair in args.iter().flatten() {
                    last = Some(*pair);
                    let pair_args = self.appl(*pair).1;
                    match pair_args[0] {
                        None => other = pair_args[1],
                        Some(condition) => {
                            let next = s1.clone();
                            let pair_cm = self.get(cm, *pair);
                            if self.eval_bool(condition, c, s0, Some(&next), CLEAR, pair_cm)? {
                                let pair_cm = self.get(cm, *pair);
                                return self.next_walk(
                                    pair_args[1].expect("a value"),
                                    acts,
                                    c,
                                    s0,
                                    s1,
                                    functor,
                                    pair_cm,
                                );
                            }
                        }
                    }
                }
                match other {
                    Some(other) => {
                        let last_cm = self.get(cm, last.expect("an arm"));
                        self.next_walk(other, acts, c, s0, s1, functor, last_cm)
                    }
                    None => no("a CASE with no condition true"),
                }
            }
            Code::Eq | Code::In => {
                let variable = self.get_primed_var(arg(0), c)?;
                let next = s1.clone();
                let Some(variable) = variable else {
                    let value = self.eval_appl_value(pred, c, s0, Some(&next), CLEAR, cm)?;
                    if !value.boolean()? {
                        return Ok(false);
                    }
                    return self.next_rest(acts, s0, s1, functor, cm);
                };
                let index = variable as usize;
                let right = self.eval_value(arg(1), c, s0, Some(&next), CLEAR, cm)?;
                match s1[index].clone() {
                    None if code == Code::Eq => {
                        s1[index] = Some(right);
                        let added = self.next_rest(acts, s0, s1, functor, cm);
                        s1[index] = None;
                        added
                    }
                    None => {
                        let mut enumeration = self.elements(&right, false)?;
                        let mut added = false;
                        while let Some(element) = self.next(&mut enumeration)? {
                            s1[index] = Some(element);
                            let result = self.next_rest(acts, s0, s1, functor, cm);
                            s1[index] = None;
                            added |= result?;
                        }
                        Ok(added)
                    }
                    Some(held) => {
                        let holds = if code == Code::Eq {
                            self.tlc_equals(&held, &right)?
                        } else {
                            self.member(&held, &right)?
                        };
                        if !holds {
                            return Ok(false);
                        }
                        self.next_rest(acts, s0, s1, functor, cm)
                    }
                }
            }
            Code::Subseteq => no("x' \\subseteq S in the next-state relation"),
            Code::Implies => {
                let next = s1.clone();
                if self.eval_bool(arg(0), c, s0, Some(&next), CLEAR, cm)? {
                    self.next_walk(arg(1), acts, c, s0, s1, functor, cm)
                } else {
                    self.next_rest(acts, s0, s1, functor, cm)
                }
            }
            Code::Unchanged => self.unchanged(arg(0), acts, c, s0, s1, functor, cm),
            _ => {
                let next = s1.clone();
                let value = self.eval_appl_value(pred, c, s0, Some(&next), CLEAR, cm)?;
                if value.boolean()? {
                    return self.next_rest(acts, s0, s1, functor, cm);
                }
                Ok(false)
            }
        }
    }

    pub(crate) fn count_root(&mut self, cm: Cm) {
        self.model.increment(cm);
    }

    pub(crate) fn count_roots(&mut self, cm: Cm, count: u64) {
        self.model.add_count(cm, count);
    }

    pub(crate) fn count_distinct(&mut self, cm: Cm) {
        self.model.add_secondary(cm, 1);
    }

    pub(crate) fn mismatch_check(&self) -> R<()> {
        self.mismatch()
    }

    /// `TLCState.equals`, the wanted state's values first.
    pub(crate) fn states_equal(&mut self, candidate: &St, wanted: &St) -> R<bool> {
        for (wanted, candidate) in wanted.iter().zip(candidate) {
            let (Some(wanted), Some(candidate)) = (wanted, candidate) else {
                return Ok(false);
            };
            if !self.tlc_equals(wanted, candidate)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub(crate) fn is_bound(&self, ctx: &Ctx, def: DefId) -> bool {
        ctx.lookup(Key::Def(def)).is_some()
    }

    pub(crate) fn is_constant(&mut self, def: DefId) -> R<bool> {
        Ok(self.constant(def)?.is_some())
    }

    pub(crate) fn primed_variable(&mut self, expr: SId, ctx: &Ctx) -> R<Option<u32>> {
        self.get_primed_var(expr, ctx)
    }

    /// What `collectPrimedLocs` walks into for an operator application: the body of an
    /// operator TLC doesn't compute at startup, in its arguments, or a lazy value's expression.
    pub(crate) fn walked_into(&mut self, node: SId, ctx: &Ctx) -> R<Option<(SId, Ctx)>> {
        let (op, args, _, _) = self.appl(node);
        let key = match op {
            Op::Sym(sym) => Some(Key::Sym(sym)),
            Op::Def(def) if ctx.lookup(Key::Def(def)).is_some() => Some(Key::Def(def)),
            _ => None,
        };
        if let Some(key) = key {
            return Ok(match ctx.lookup(key) {
                Some(Bind::Lazy(lazy)) => Some((lazy.expr, lazy.ctx.clone())),
                _ => None,
            });
        }
        Ok(match op {
            Op::Def(def) => {
                if self.constant(def)?.is_some() || self.sem.def(def).is_recursive {
                    None
                } else {
                    let c1 = self.op_context(def, args, ctx, NO_CM);
                    Some((self.sem.def(def).body.expect("a body"), c1))
                }
            }
            Op::Substituted(def) => {
                let c1 = self.op_context(def, args, ctx, NO_CM);
                Some((self.sem.def(def).body.expect("a body"), c1))
            }
            _ => None,
        })
    }

    fn cached(
        &mut self,
        lazy: &Rc<LazyCell>,
        s0: &St,
        s1: Option<&St>,
        control: u8,
    ) -> Option<CVal> {
        lazy.cache
            .borrow()
            .as_ref()
            .and_then(|(value, cached0, cached1, cached_control)| {
                let equivalent =
                    (control & !(KEEP_LAZY | INIT)) == (cached_control & !(KEEP_LAZY | INIT));
                (equivalent
                    && Self::is_subset(Some(s0), Some(cached0)) == Some(true)
                    && Self::is_subset(s1, cached1.as_ref()) == Some(true))
                .then(|| value.clone())
            })
    }

    // `getNextStatesApplUsrDefOp`: a value that must be a boolean.
    fn next_value(
        &mut self,
        value: CVal,
        acts: &Acts,
        s0: &St,
        s1: &mut St,
        functor: &mut NextFunctor<'_, 'a, 'ir>,
        cm: Cm,
    ) -> R<bool> {
        if value.boolean()? {
            return self.next_rest(acts, s0, s1, functor, cm);
        }
        Ok(false)
    }

    /// `processUnchanged`.
    #[allow(clippy::too_many_arguments)]
    fn unchanged(
        &mut self,
        expr: SId,
        acts: &Acts,
        c: &Ctx,
        s0: &St,
        s1: &mut St,
        functor: &mut NextFunctor<'_, 'a, 'ir>,
        cm: Cm,
    ) -> R<bool> {
        let cm = self.get(cm, expr);
        self.mismatch()?;
        if let Some(variable) = self.get_var(expr, c, false)? {
            let index = variable as usize;
            let before = s0[index].clone().expect("a current state");
            return match s1[index].clone() {
                None => {
                    s1[index] = Some(before);
                    let added = self.next_rest(acts, s0, s1, functor, cm);
                    s1[index] = None;
                    added
                }
                Some(after) => {
                    if self.tlc_equals(&before, &after)? {
                        self.next_rest(acts, s0, s1, functor, cm)
                    } else {
                        no(
                            "a variable changed that the action leaves UNCHANGED, which TLC warns of",
                        )
                    }
                }
            };
        }
        if let SKind::Appl { op, args, .. } = &self.sem.node(expr).kind {
            if *op == Op::Code(Code::Tuple) {
                let nested = self.get(cm, expr);
                if args.is_empty() {
                    return self.next_rest(acts, s0, s1, functor, cm);
                }
                let mut acts1 = acts.clone();
                for item in args[1..].iter().rev().flatten() {
                    let item_cm = self.get(nested, *item);
                    acts1 = acts1.cons(*item, c.clone(), item_cm, Kind::Unchanged);
                }
                return self.unchanged(
                    args[0].expect("an item"),
                    &acts1,
                    c,
                    s0,
                    s1,
                    functor,
                    nested,
                );
            }
            if args.is_empty() {
                match *op {
                    Op::Def(def) => match c.lookup(Key::Def(def)) {
                        Some(Bind::Lazy(lazy)) => {
                            let ctx = lazy.ctx.clone();
                            return self.unchanged(lazy.expr, acts, &ctx, s0, s1, functor, cm);
                        }
                        Some(Bind::Val(_)) => {}
                        None => {
                            if self.constant(def)?.is_none() {
                                let body = self.sem.def(def).body.expect("a body");
                                return self.unchanged(body, acts, c, s0, s1, functor, cm);
                            }
                        }
                    },
                    Op::Sym(sym) => {
                        if let Some(Bind::Lazy(lazy)) = c.lookup(Key::Sym(sym)) {
                            let ctx = lazy.ctx.clone();
                            return self.unchanged(lazy.expr, acts, &ctx, s0, s1, functor, cm);
                        }
                    }
                    Op::Substituted(def) => {
                        let body = self.sem.def(def).body.expect("a body");
                        return self.unchanged(body, acts, c, s0, s1, functor, cm);
                    }
                    _ => {}
                }
            }
        }
        // `verifyUnchanged`.
        let empty = Rc::clone(&self.empty);
        let before = self.eval(expr, c, s0, Some(&empty), CLEAR, cm)?;
        let after = self.eval(expr, c, s1, None, CLEAR, cm)?;
        if self.tlc_equals_cval(&before, &after)? {
            return self.next_rest(acts, s0, s1, functor, cm);
        }
        Ok(false)
    }

    // --- the checks ---

    /// `isValid(act, s0, s1)`: an invariant (`s1` empty) or an action's predicate.
    pub(crate) fn is_valid(&mut self, action: &Action, s0: &St, s1: Option<&St>) -> R<bool> {
        let ctx = action.ctx.clone();
        self.eval_bool(action.pred, &ctx, s0, s1, CLEAR, action.cm)
    }

    /// `isInModel(constraint, state)` and `isInActions(constraint, s0, s1)`.
    pub(crate) fn is_in(&mut self, constraint: &Action, s0: &St, s1: Option<&St>) -> R<bool> {
        let empty = Rc::clone(&self.empty);
        let holds = self.eval_bool(
            constraint.pred,
            &Ctx::default(),
            s0,
            Some(s1.unwrap_or(&empty)),
            CLEAR,
            constraint.cm,
        )?;
        if holds {
            self.model.add_secondary(constraint.cm, 1);
        } else {
            self.model.increment(constraint.cm);
        }
        Ok(holds)
    }
}

fn tuple_items(value: &Value) -> Option<&[Value]> {
    crate::sets::as_tuple(value)
}

fn record_set(fields: Vec<(Rc<crate::value::Text>, Value)>) -> R<Value> {
    let count = fields.len();
    let mut sorted: Vec<(usize, (Rc<crate::value::Text>, Value))> =
        fields.into_iter().enumerate().collect();
    sorted.sort_by(|left, right| {
        compare(
            &Value::Str(Rc::clone(&left.1.0)),
            &Value::Str(Rc::clone(&right.1.0)),
        )
        .unwrap_or(std::cmp::Ordering::Equal)
    });
    let mut written = vec![0; count];
    for (position, (index, _)) in sorted.iter().enumerate() {
        written[*index] = position as u32;
    }
    Ok(Value::Lazy(Rc::new(Lazy::RecordSet(
        sorted.into_iter().map(|(_, field)| field).collect(),
        written,
    ))))
}

// `select` of a path of keys: the value there, or none where a key is missing.
fn select_path(value: &Value, path: &[Value]) -> R<Option<Value>> {
    let Some((first, rest)) = path.split_first() else {
        return Ok(Some(value.clone()));
    };
    let Value::Function(function) = value else {
        return no("an EXCEPT of a value that isn't a function");
    };
    match find_key(function, first)? {
        Some(position) => select_path(&function.range[position], rest),
        None => Ok(None),
    }
}

// `takeExcept`: the function with the value at the path replaced, of the same class.
fn replace_path(value: &Value, path: &[Value], new: Value) -> R<Value> {
    let Some((first, rest)) = path.split_first() else {
        return Ok(new);
    };
    let Value::Function(function) = value else {
        return no("an EXCEPT of a value that isn't a function");
    };
    let Some(position) = find_key(function, first)? else {
        return no("an EXCEPT of a key the function lacks");
    };
    let mut range = function.range.clone();
    range[position] = replace_path(&range[position], rest, new)?;
    Ok(Value::Function(Rc::new(Function {
        domain: function.domain.clone(),
        range,
        class: std::cell::Cell::new(function.class.get()),
        written: RefCell::new(function.written.borrow().clone()),
        search: std::cell::Cell::new(function.search.get()),
        interval: function.interval,
    })))
}

/// The builtins TLC overrides with Java, which evaluate their arguments and count nothing.
fn is_overridden(name: &str) -> bool {
    matches!(
        name,
        "TRUE"
            | "FALSE"
            | "BOOLEAN"
            | "STRING"
            | "Nat"
            | "Int"
            | "+"
            | "-"
            | "*"
            | "\\div"
            | "%"
            | "^"
            | "-."
            | "<"
            | ">"
            | "<="
            | ">="
            | ".."
            | "Cardinality"
            | "IsFiniteSet"
            | "Seq"
            | "Len"
            | "Head"
            | "Tail"
            | "Append"
            | "\\o"
            | "SubSeq"
            | ":>"
            | "@@"
            | "Assert"
            | "Permutations"
    )
}

/// A nested enumeration of a set of functions, records or tuples.
pub(crate) struct Product {
    enums: Vec<Enumeration>,
    current: Vec<Value>,
    is_done: bool,
}

pub(crate) enum Make {
    Function {
        keys: Vec<Value>,
        interval: Option<(i32, i32)>,
    },
    Record(Vec<Rc<crate::value::Text>>),
    Tuple,
}

/// A `ValueEnumeration`, with the counting of its class.
pub(crate) enum Enumeration {
    SetEnum {
        elements: Rc<Vec<Value>>,
        index: usize,
        cm: Cm,
    },
    Interval {
        low: i32,
        high: i32,
        index: i64,
        cm: Cm,
    },
    /// The elements of a set that counts nothing.
    List { elements: Vec<Value>, index: usize },
    Subsets {
        elements: Vec<Value>,
        k: usize,
        indices: Vec<usize>,
        cm: Cm,
    },
    Product {
        product: Option<Product>,
        make: Make,
        cm: Cm,
    },
}

/// `ContextEnumerator`.
pub(crate) struct Contexts {
    ctx: Ctx,
    vars: Vec<(Vec<Sym>, bool)>,
    enums: Vec<Enumeration>,
    current: Vec<Value>,
    is_done: bool,
}
