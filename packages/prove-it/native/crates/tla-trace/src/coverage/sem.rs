//! The model's expressions as SANY's semantic graph holds them, which TLC's cost model mirrors and
//! its `Tool` walks: an `OpApplNode` for every application of an operator, a variable, a constant,
//! a definition or a bound name, with the location SANY gives it. The IR keeps an infix chain
//! `A /\ B /\ C` as one junction, which SANY nests as `(A /\ B) /\ C`; a record's fields, a CASE's
//! arms and an EXCEPT's updates as parts of their node, which SANY makes `$Pair` nodes of; and a
//! name as the definition it resolves to. Each IR node is translated once, so a node met again
//! (`NodeKind::Reference`) is the same node, as in SANY's graph.

use std::collections::HashMap;

use tla_ir::{
    Bound, Definition, DefinitionForm, Index, Ir, Name, NodeId, NodeKind, PathStep, Pattern,
    Resolution, SourceRange, TextId,
};

use crate::Unsupported;

pub(crate) type SId = u32;
pub(crate) type Sym = u32;
pub(crate) type DefId = u32;

/// TLC's opcodes of SANY's built-in operators (`BuiltInOPs`), the ones the port evaluates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Code {
    Eq,
    Noteq,
    In,
    Notin,
    Subseteq,
    Cup,
    Cap,
    Setdiff,
    Subset,
    Union,
    Domain,
    Lnot,
    Land,
    Lor,
    Implies,
    Equiv,
    ConjList,
    DisjList,
    BoundedExists,
    BoundedForall,
    BoundedChoose,
    IfThenElse,
    Case,
    Pair,
    SetEnumerate,
    SubsetOf,
    SetOfAll,
    Tuple,
    FcnConstructor,
    NonRecursiveFcnSpec,
    RecursiveFcnSpec,
    SetOfFcns,
    RcdConstructor,
    SetOfRcds,
    Except,
    Seq,
    FcnApply,
    RcdSelect,
    CartesianProd,
    SquareAct,
    AngleAct,
    Prime,
    Unchanged,
}

/// The operator of an application.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Op {
    Code(Code),
    /// A builtin of the IR: an operator of a standard module that TLC overrides with Java, or a
    /// built-in constant such as TRUE.
    Builtin(Index),
    Var(u32),
    Const(Index),
    Def(DefId),
    /// A declared constant the configuration replaces with a definition (`N <- Def`), which TLC
    /// evaluates afresh each time.
    Substituted(DefId),
    /// A bound name: an operator's parameter, a quantified or a function's variable.
    Sym(Sym),
}

/// A group of bound names over one set, as SANY groups `x, y \in S`.
#[derive(Clone, Debug)]
pub(crate) struct SBound {
    pub syms: Vec<Sym>,
    pub is_tuple: bool,
    pub set: SId,
}

#[derive(Clone, Debug)]
pub(crate) enum SKind {
    Num(i32),
    Str(TextId),
    /// The `@` of an EXCEPT.
    At,
    Appl {
        op: Op,
        /// `None` for the missing condition of an OTHER arm.
        args: Vec<Option<SId>>,
        bounds: Vec<SBound>,
        /// The name a recursive function's body applies it by.
        recursive: Option<Sym>,
    },
    Let {
        defs: Vec<DefId>,
        body: SId,
    },
}

#[derive(Clone, Debug)]
pub(crate) struct SNode {
    pub range: Option<SourceRange>,
    pub kind: SKind,
}

impl SNode {
    pub fn is_appl(&self) -> bool {
        matches!(self.kind, SKind::Appl { .. })
    }
}

/// A definition: the module's, or one a LET makes.
#[derive(Clone, Debug)]
pub(crate) struct SDef {
    pub name: TextId,
    pub params: Vec<Sym>,
    /// The body, or `None` while it is translated.
    pub body: Option<SId>,
    /// The IR's definition node.
    pub node: NodeId,
    /// Whether TLC computes the definition as it starts (`processConstantDefns`).
    pub is_constant: bool,
    pub is_recursive: bool,
}

/// A name in the scope of an expression.
#[derive(Clone, Copy)]
enum Scoped {
    Sym(Sym),
    Def(DefId),
}

pub(crate) struct Sem<'ir> {
    pub ir: &'ir Ir,
    pub nodes: Vec<SNode>,
    pub defs: Vec<SDef>,
    pub sym_count: u32,
    /// The name of each bound symbol, by its number.
    pub sym_names: Vec<TextId>,
    translated: HashMap<NodeId, SId>,
    globals: HashMap<Index, DefId>,
    scope: Vec<(TextId, Scoped)>,
    recursive_syms: Vec<Sym>,
    texts: HashMap<TextId, std::rc::Rc<Vec<Vec<char>>>>,
}

fn unsupported<T>(reason: impl Into<String>) -> Result<T, Unsupported> {
    Err(Unsupported(reason.into()))
}

type Translated<T> = Result<T, Unsupported>;

impl<'ir> Sem<'ir> {
    pub fn new(ir: &'ir Ir, sources: &dyn Fn(&str) -> Option<String>) -> Sem<'ir> {
        // The sources of the modules the IR's places name.
        let mut texts = HashMap::new();
        for node in &ir.nodes.arena {
            if let Some(range) = node.range
                && !texts.contains_key(&range.module)
                && let Some(text) = sources(&ir.texts[range.module as usize])
            {
                let lines: Vec<Vec<char>> =
                    text.lines().map(|line| line.chars().collect()).collect();
                texts.insert(range.module, std::rc::Rc::new(blank_comments(lines)));
            }
        }
        Sem {
            ir,
            nodes: Vec::new(),
            defs: Vec::new(),
            sym_count: 0,
            sym_names: Vec::new(),
            translated: HashMap::new(),
            globals: HashMap::new(),
            scope: Vec::new(),
            recursive_syms: Vec::new(),
            texts,
        }
    }

    pub fn node(&self, id: SId) -> &SNode {
        &self.nodes[id as usize]
    }

    pub fn def(&self, id: DefId) -> &SDef {
        &self.defs[id as usize]
    }

    pub fn text(&self, id: TextId) -> &'ir str {
        &self.ir.texts[id as usize]
    }

    fn resolve(&self, mut node: NodeId) -> NodeId {
        while let NodeKind::Reference(target) = self.ir.nodes.arena[node as usize].kind {
            node = target;
        }
        node
    }

    fn ir_range(&self, node: NodeId) -> Option<SourceRange> {
        self.ir.nodes.arena[self.resolve(node) as usize].range
    }

    fn push(&mut self, range: Option<SourceRange>, kind: SKind) -> SId {
        self.nodes.push(SNode { range, kind });
        (self.nodes.len() - 1) as SId
    }

    fn new_sym(&mut self, name: TextId) -> Sym {
        self.sym_count += 1;
        self.sym_names.push(name);
        self.sym_count - 1
    }

    /// The module's definition at `index`, translated once.
    pub fn global(&mut self, index: Index) -> Translated<DefId> {
        if let Some(&def) = self.globals.get(&index) {
            return Ok(def);
        }
        let node = self.ir.definitions[index as usize];
        let saved = std::mem::take(&mut self.scope);
        let result = self.definition(node, Some(index));
        self.scope = saved;
        result
    }

    // Translates a definition in the current scope, its body seeing its parameters.
    fn definition(&mut self, node: NodeId, index: Option<Index>) -> Translated<DefId> {
        let node = self.resolve(node);
        let NodeKind::Definition(definition) = &self.ir.nodes.arena[node as usize].kind else {
            return unsupported("a definition the IR doesn't hold as one");
        };
        let definition: &'ir Definition = definition;
        let id = self.defs.len() as DefId;
        self.defs.push(SDef {
            name: definition.name,
            params: Vec::new(),
            body: None,
            node,
            is_constant: index.is_some() && definition.flags & Definition::NORMALIZED != 0,
            is_recursive: definition.flags & Definition::RECURSIVE != 0,
        });
        if let Some(index) = index {
            self.globals.insert(index, id);
        }
        let depth = self.scope.len();
        let body = match &definition.form {
            DefinitionForm::Operator(params) => {
                let mut syms = Vec::new();
                for param in params {
                    if param.arity != 0 {
                        return unsupported("an operator that takes an operator");
                    }
                    let sym = self.new_sym(param.name);
                    self.scope.push((param.name, Scoped::Sym(sym)));
                    syms.push(sym);
                }
                self.defs[id as usize].params = syms;
                self.expression(definition.body)
            }
            DefinitionForm::Function(bounds) => {
                if definition.flags & Definition::LOCAL != 0 {
                    return unsupported("a LOCAL function definition");
                }
                let is_recursive = definition.flags & Definition::SELF_REFERENTIAL != 0;
                let recursive = is_recursive.then(|| self.new_sym(definition.name));
                self.recursive_syms.extend(recursive);
                if let Some(sym) = recursive {
                    self.scope.push((definition.name, Scoped::Sym(sym)));
                }
                let range = self.ir_range(node);
                self.bounded(range, bounds, definition.body, |bounds, body| SKind::Appl {
                    op: Op::Code(if is_recursive {
                        Code::RecursiveFcnSpec
                    } else {
                        Code::NonRecursiveFcnSpec
                    }),
                    args: vec![Some(body)],
                    bounds,
                    recursive,
                })
            }
        };
        self.scope.truncate(depth);
        self.defs[id as usize].body = Some(body?);
        Ok(id)
    }

    // A node over bounds, its body translated in their scope: SANY's ranges, grouped where the IR
    // holds one set for several names.
    fn bounded(
        &mut self,
        range: Option<SourceRange>,
        bounds: &[Bound],
        body: NodeId,
        make: impl FnOnce(Vec<SBound>, SId) -> SKind,
    ) -> Translated<SId> {
        let groups = self.bounds(bounds)?;
        let depth = self.scope.len();
        for group in &groups {
            for &sym in &group.syms {
                self.scope
                    .push((self.sym_names[sym as usize], Scoped::Sym(sym)));
            }
        }
        let body = self.expression(body);
        self.scope.truncate(depth);
        let body = body?;
        Ok(self.push(range, make(groups, body)))
    }

    // The bounds, their sets translated in the enclosing scope, as SANY groups them: the names
    // of consecutive bounds over one set node are one group.
    fn bounds(&mut self, bounds: &[Bound]) -> Translated<Vec<SBound>> {
        let mut groups: Vec<(NodeId, SBound)> = Vec::new();
        for bound in bounds {
            let set_node = self.resolve(bound.set);
            let (names, is_tuple) = match &bound.pattern {
                Pattern::Name(name) => (vec![*name], false),
                Pattern::Tuple(names) => (names.clone(), true),
            };
            let syms: Vec<Sym> = names.iter().map(|&name| self.new_sym(name)).collect();
            if let Some((last, group)) = groups.last_mut()
                && *last == set_node
                && !is_tuple
                && !group.is_tuple
            {
                group.syms.extend(syms);
                continue;
            }
            let set = self.expression(bound.set)?;
            groups.push((
                set_node,
                SBound {
                    syms,
                    is_tuple,
                    set,
                },
            ));
        }
        Ok(groups.into_iter().map(|(_, group)| group).collect())
    }

    fn is_instanced(&self, index: Index) -> bool {
        let model = &self.ir.model;
        model
            .instance_names
            .iter()
            .any(|&(named, _)| named == index)
            || model
                .instance_actions
                .iter()
                .any(|action| action.definition == index)
    }

    fn lookup(&self, text: TextId) -> Option<Scoped> {
        self.scope
            .iter()
            .rev()
            .find(|(name, _)| *name == text)
            .map(|(_, scoped)| *scoped)
    }

    // The operator a name applies.
    fn operator(&mut self, name: &Name, arity: usize) -> Translated<Op> {
        if name.is_local {
            return match self.lookup(name.text) {
                Some(Scoped::Sym(sym)) if arity == 0 => Ok(Op::Sym(sym)),
                Some(Scoped::Sym(_)) => unsupported("an operator's parameter applied to arguments"),
                Some(Scoped::Def(def)) => Ok(Op::Def(def)),
                None => unsupported("a name bound outside the expression, as by an INSTANCE"),
            };
        }
        Ok(match name.resolution {
            Resolution::Variable(index) => {
                if index as usize >= self.ir.variables.len() {
                    return unsupported("a variable of ENABLED's rewrite");
                }
                Op::Var(index)
            }
            Resolution::Constant(index) => Op::Const(index),
            Resolution::Definition(_)
                if let Some(Scoped::Sym(sym)) = self.lookup(name.text)
                    && self.recursive_syms.contains(&sym) =>
            {
                if arity != 0 {
                    return unsupported("a recursive function applied as an operator");
                }
                Op::Sym(sym)
            }
            Resolution::Definition(index) => {
                if self.is_instanced(index) {
                    return unsupported("a definition an INSTANCE copies");
                }
                let def = self.global(index)?;
                // The IR names a definition of an extended module by a key, `name@module`.
                let unkeyed = |text: &str| {
                    text.rsplit_once('@')
                        .filter(|(name, _)| !name.is_empty())
                        .map_or(text, |(name, _)| name)
                        .to_owned()
                };
                if unkeyed(self.text(self.def(def).name)) != unkeyed(self.text(name.text)) {
                    // The configuration replaces a declared constant, or a definition, with the
                    // definition. SANY's graph walks the body of a definition replaced too, which
                    // TLC never evaluates, so it reports nothing of it.
                    if self.defs[def as usize].is_recursive {
                        return unsupported("a RECURSIVE operator the configuration substitutes");
                    }
                    Op::Substituted(def)
                } else {
                    Op::Def(def)
                }
            }
            Resolution::Builtin(index) => Op::Builtin(index),
            Resolution::None => return unsupported("a name the IR doesn't resolve"),
        })
    }

    fn appl(&mut self, range: Option<SourceRange>, op: Op, args: Vec<SId>) -> SId {
        self.push(
            range,
            SKind::Appl {
                op,
                args: args.into_iter().map(Some).collect(),
                bounds: Vec::new(),
                recursive: None,
            },
        )
    }

    fn all(&mut self, nodes: &[NodeId]) -> Translated<Vec<SId>> {
        nodes.iter().map(|&node| self.expression(node)).collect()
    }

    /// Translates an expression in the current scope, once.
    pub fn expression(&mut self, node: NodeId) -> Translated<SId> {
        let node = self.resolve(node);
        if let Some(&id) = self.translated.get(&node) {
            return Ok(id);
        }
        let id = self.translate(node)?;
        self.translated.insert(node, id);
        Ok(id)
    }

    fn builtin_code(&self, index: Index) -> Option<Code> {
        let builtin = &self.ir.builtins[index as usize];
        Some(match self.text(builtin.name) {
            "=" => Code::Eq,
            "#" | "/=" => Code::Noteq,
            "\\in" => Code::In,
            "\\notin" => Code::Notin,
            "\\subseteq" => Code::Subseteq,
            "\\cup" | "\\union" => Code::Cup,
            "\\cap" | "\\intersect" => Code::Cap,
            "\\" => Code::Setdiff,
            "SUBSET" => Code::Subset,
            "UNION" => Code::Union,
            "DOMAIN" => Code::Domain,
            "~" | "\\lnot" | "\\neg" => Code::Lnot,
            "/\\" | "\\land" => Code::Land,
            "\\/" | "\\lor" => Code::Lor,
            "=>" => Code::Implies,
            "<=>" | "\\equiv" => Code::Equiv,
            _ => return None,
        })
    }

    fn translate(&mut self, node: NodeId) -> Translated<SId> {
        let ir_node = &self.ir.nodes.arena[node as usize];
        let range = ir_node.range;
        let kind: &'ir NodeKind = &ir_node.kind;
        Ok(match kind {
            NodeKind::Number(int) => self.push(range, SKind::Num(*int)),
            NodeKind::String(text) => self.push(range, SKind::Str(*text)),
            NodeKind::ExceptAt => self.push(range, SKind::At),
            NodeKind::Identifier(name) => {
                let op = self.operator(name, 0)?;
                let op = match op {
                    Op::Builtin(index) if self.builtin_code(index).is_some() => {
                        return unsupported("a built-in operator used as a value");
                    }
                    op => op,
                };
                self.appl(range, op, Vec::new())
            }
            NodeKind::Apply { name, args } => {
                let op = self.operator(name, args.len())?;
                let op = match op {
                    Op::Builtin(index) => match self.builtin_code(index) {
                        Some(code) => {
                            let arity = match code {
                                Code::Subset | Code::Union | Code::Domain | Code::Lnot => 1,
                                _ => 2,
                            };
                            if args.len() != arity {
                                return unsupported("a built-in operator of another arity");
                            }
                            Op::Code(code)
                        }
                        None => op,
                    },
                    op => op,
                };
                if let Op::Def(def) | Op::Substituted(def) = op
                    && self.def(def).params.len() != args.len()
                {
                    return unsupported("an operator applied to another number of arguments");
                }
                let args = self.all(args)?;
                self.appl(range, op, args)
            }
            NodeKind::And(operands) | NodeKind::Or(operands) => {
                let is_and = matches!(kind, NodeKind::And(_));
                self.junction(node, range, operands, is_and)?
            }
            NodeKind::Prime(inner) => {
                let inner = self.expression(*inner)?;
                self.appl(range, Op::Code(Code::Prime), vec![inner])
            }
            NodeKind::Unchanged(inner) => {
                let inner = self.expression(*inner)?;
                self.appl(range, Op::Code(Code::Unchanged), vec![inner])
            }
            NodeKind::If {
                condition,
                consequent,
                alternative,
            } => {
                let args = self.all(&[*condition, *consequent, *alternative])?;
                self.appl(range, Op::Code(Code::IfThenElse), args)
            }
            NodeKind::Case { arms, other } => {
                let mut pairs = Vec::new();
                for &(condition, body) in arms {
                    let start = self.ir_range(condition);
                    let end = self.ir_range(body);
                    let (Some(start), Some(end)) = (start, end) else {
                        return unsupported("a CASE arm without a place in the source");
                    };
                    // The arm runs from its condition to its expression, unless one is
                    // parenthesized, which SANY's arm covers.
                    self.expect_before(start, &["CASE", "[]"])?;
                    self.expect_before(end, &["->"])?;
                    let condition = self.expression(condition)?;
                    let body = self.expression(body)?;
                    let pair = self.appl(
                        Some(SourceRange {
                            end_line: end.end_line,
                            end_column: end.end_column,
                            ..start
                        }),
                        Op::Code(Code::Pair),
                        vec![condition, body],
                    );
                    pairs.push(Some(pair));
                }
                if let Some(other) = other {
                    let Some(end) = self.ir_range(*other) else {
                        return unsupported("a CASE arm without a place in the source");
                    };
                    let start = self.start_of_other(end)?;
                    let body = self.expression(*other)?;
                    let pair = self.push(
                        Some(SourceRange {
                            end_line: end.end_line,
                            end_column: end.end_column,
                            ..start
                        }),
                        SKind::Appl {
                            op: Op::Code(Code::Pair),
                            args: vec![None, Some(body)],
                            bounds: Vec::new(),
                            recursive: None,
                        },
                    );
                    pairs.push(Some(pair));
                }
                self.push(
                    range,
                    SKind::Appl {
                        op: Op::Code(Code::Case),
                        args: pairs,
                        bounds: Vec::new(),
                        recursive: None,
                    },
                )
            }
            NodeKind::Let {
                instances,
                definitions,
                body,
            } => {
                if *instances != 0 {
                    return unsupported("an INSTANCE in a LET");
                }
                let depth = self.scope.len();
                let mut defs = Vec::new();
                let mut result = Ok(());
                for &definition in definitions {
                    match self.definition(definition, None) {
                        Ok(def) => {
                            let name = self.defs[def as usize].name;
                            self.scope.push((name, Scoped::Def(def)));
                            defs.push(def);
                        }
                        Err(error) => {
                            result = Err(error);
                            break;
                        }
                    }
                }
                let body = result.and_then(|()| self.expression(*body));
                self.scope.truncate(depth);
                let body = body?;
                self.push(range, SKind::Let { defs, body })
            }
            NodeKind::Forall { bounds, body } | NodeKind::Exists { bounds, body } => {
                let code = if matches!(kind, NodeKind::Forall { .. }) {
                    Code::BoundedForall
                } else {
                    Code::BoundedExists
                };
                self.bounded(range, bounds, *body, |bounds, body| SKind::Appl {
                    op: Op::Code(code),
                    args: vec![Some(body)],
                    bounds,
                    recursive: None,
                })?
            }
            NodeKind::Choose {
                pattern,
                set: Some(set),
                body,
            } => {
                let bound = [Bound {
                    pattern: pattern.clone(),
                    set: *set,
                }];
                let groups = self.bounds(&bound)?;
                let depth = self.scope.len();
                for &sym in &groups[0].syms {
                    self.scope
                        .push((self.sym_names[sym as usize], Scoped::Sym(sym)));
                }
                let body = self.expression(*body);
                self.scope.truncate(depth);
                let body = body?;
                self.push(
                    range,
                    SKind::Appl {
                        op: Op::Code(Code::BoundedChoose),
                        args: vec![Some(body)],
                        bounds: groups,
                        recursive: None,
                    },
                )
            }
            NodeKind::SetEnumeration(items) => {
                let items = self.all(items)?;
                self.appl(range, Op::Code(Code::SetEnumerate), items)
            }
            NodeKind::SetFilter { bound, predicate } => self.bounded(
                range,
                std::slice::from_ref(bound),
                *predicate,
                |bounds, body| SKind::Appl {
                    op: Op::Code(Code::SubsetOf),
                    args: vec![Some(body)],
                    bounds,
                    recursive: None,
                },
            )?,
            NodeKind::SetMap { expression, bounds } => {
                self.bounded(range, bounds, *expression, |bounds, body| SKind::Appl {
                    op: Op::Code(Code::SetOfAll),
                    args: vec![Some(body)],
                    bounds,
                    recursive: None,
                })?
            }
            NodeKind::Tuple(items) => {
                let items = self.all(items)?;
                self.appl(range, Op::Code(Code::Tuple), items)
            }
            NodeKind::FunctionConstruction {
                is_recursive: false,
                bounds,
                body,
            } => self.bounded(range, bounds, *body, |bounds, body| SKind::Appl {
                op: Op::Code(Code::FcnConstructor),
                args: vec![Some(body)],
                bounds,
                recursive: None,
            })?,
            NodeKind::FunctionSet { domain, range: to } => {
                let args = self.all(&[*domain, *to])?;
                self.appl(range, Op::Code(Code::SetOfFcns), args)
            }
            NodeKind::Record(fields) | NodeKind::RecordSet(fields) => {
                let is_set = matches!(kind, NodeKind::RecordSet(_));
                let mut pairs = Vec::new();
                for &(field, value) in fields {
                    let Some(end) = self.ir_range(value) else {
                        return unsupported("a record field without a place in the source");
                    };
                    let start =
                        self.start_of_field(end, field, if is_set { ":" } else { "|->" })?;
                    let name = self.push(None, SKind::Str(field));
                    let value = self.expression(value)?;
                    pairs.push(self.appl(
                        Some(SourceRange {
                            end_line: end.end_line,
                            end_column: end.end_column,
                            ..start
                        }),
                        Op::Code(Code::Pair),
                        vec![name, value],
                    ));
                }
                let code = if is_set {
                    Code::SetOfRcds
                } else {
                    Code::RcdConstructor
                };
                self.appl(range, Op::Code(code), pairs)
            }
            NodeKind::Except { function, updates } => {
                let function = self.expression(*function)?;
                let mut args = vec![function];
                for update in updates {
                    let Some(end) = self.ir_range(update.value) else {
                        return unsupported("an EXCEPT without a place in the source");
                    };
                    let start = self.start_of_update(&update.path, end)?;
                    let spec = Some(SourceRange {
                        end_line: end.end_line,
                        end_column: end.end_column,
                        ..start
                    });
                    let mut steps = Vec::new();
                    for step in &update.path {
                        steps.push(match step {
                            PathStep::Field(field) => self.push(None, SKind::Str(*field)),
                            PathStep::Index(indices) if indices.len() == 1 => {
                                self.expression(indices[0])?
                            }
                            PathStep::Index(_) => {
                                return unsupported("an EXCEPT of a function of several arguments");
                            }
                        });
                    }
                    let seq = self.appl(spec, Op::Code(Code::Seq), steps);
                    let value = self.expression(update.value)?;
                    args.push(self.appl(spec, Op::Code(Code::Pair), vec![seq, value]));
                }
                self.appl(range, Op::Code(Code::Except), args)
            }
            NodeKind::FunctionApplication { function, args } => {
                let function = self.expression(*function)?;
                let argument = match &args[..] {
                    [single] => self.expression(*single)?,
                    _ => {
                        let items = self.all(args)?;
                        self.appl(range, Op::Code(Code::Tuple), items)
                    }
                };
                self.appl(range, Op::Code(Code::FcnApply), vec![function, argument])
            }
            NodeKind::FieldAccess { record, field } => {
                let record = self.expression(*record)?;
                let name = self.push(None, SKind::Str(*field));
                self.appl(range, Op::Code(Code::RcdSelect), vec![record, name])
            }
            NodeKind::Product(factors) => {
                let factors = self.all(factors)?;
                self.appl(range, Op::Code(Code::CartesianProd), factors)
            }
            NodeKind::BoxAction { action, subscript }
            | NodeKind::AngleAction { action, subscript } => {
                let code = match kind {
                    NodeKind::BoxAction { .. } => Code::SquareAct,
                    _ => Code::AngleAct,
                };
                let args = self.all(&[*action, *subscript])?;
                // The IR keeps a tuple subscript's start but not its place, which ends the
                // action's.
                let held = &self.ir.nodes.arena[self.resolve(*subscript) as usize];
                if self.nodes[args[1] as usize].range.is_none()
                    && let Some(range) = range
                {
                    self.nodes[args[1] as usize].range = Some(SourceRange {
                        start_line: held.line,
                        start_column: held.column,
                        ..range
                    });
                }
                self.appl(range, Op::Code(code), args)
            }
            // SANY's LabelNode is no OpApplNode: TLC evaluates its body, and the cost model finds
            // the body under the label's parent.
            NodeKind::Label { body, .. } => return self.expression(*body),
            NodeKind::WideNumber(_) => return unsupported("an integer outside 32 bits"),
            NodeKind::Decimal(_) => return unsupported("a real number"),
            NodeKind::OperatorReference(_) | NodeKind::Lambda { .. } => {
                return unsupported("an operator passed as an argument");
            }
            NodeKind::Enabled(_) => return unsupported("ENABLED"),
            NodeKind::UnboundedQuantifier { .. } | NodeKind::Choose { set: None, .. } => {
                return unsupported("an unbounded quantifier");
            }
            NodeKind::FunctionConstruction {
                is_recursive: true, ..
            } => return unsupported("a recursive function construction"),
            NodeKind::Bracket(_) => return unsupported("a bracket expression"),
            NodeKind::Always(_)
            | NodeKind::Eventually(_)
            | NodeKind::WeakFairness { .. }
            | NodeKind::StrongFairness { .. } => return unsupported("a temporal formula"),
            NodeKind::Subexpression(_) => return unsupported("a subexpression name"),
            NodeKind::Definition(_) => return unsupported("a definition as an expression"),
            NodeKind::Reference(_) => unreachable!("references are resolved"),
        })
    }

    // A junction: a bulleted list as one `$ConjList` or `$DisjList`, an infix chain as SANY
    // nests it, each prefix of two or more operands a node of its own.
    fn junction(
        &mut self,
        node: NodeId,
        range: Option<SourceRange>,
        operands: &'ir [NodeId],
        is_and: bool,
    ) -> Translated<SId> {
        let junction = self.ir.nodes.junctions.get(&node);
        let args = self.all(operands)?;
        if junction.is_some_and(|junction| junction.is_bulleted) {
            let code = if is_and {
                Code::ConjList
            } else {
                Code::DisjList
            };
            return Ok(self.appl(range, Op::Code(code), args));
        }
        let code = if is_and { Code::Land } else { Code::Lor };
        if args.len() < 2 {
            return unsupported("an infix junction of fewer than two operands");
        }
        let ends = junction.map(|junction| &junction.prefix_ends[..]);
        if args.len() > 2 && ends.is_none_or(|ends| ends.len() + 1 < args.len()) {
            return unsupported("an infix junction without the places of its prefixes");
        }
        let mut current = args[0];
        for count in 2..=args.len() {
            let prefix_range = if count == args.len() {
                range
            } else {
                let (line, column) = ends.expect("prefix ends")[count - 2];
                range.map(|range| SourceRange {
                    end_line: line,
                    end_column: column,
                    ..range
                })
            };
            current = self.appl(prefix_range, Op::Code(code), vec![current, args[count - 1]]);
        }
        Ok(current)
    }

    /// Where SANY places a definition's name and parameters (`N_IdentLHS`), which TLC names an
    /// action by: `A` or `A(p, q)` from where the definition starts.
    pub fn declaration(&self, def: DefId) -> Translated<SourceRange> {
        let node = self.defs[def as usize].node;
        let name: Vec<char> = self.text(self.defs[def as usize].name).chars().collect();
        let Some(range) = self.ir_range(node) else {
            return unsupported("a definition without a place in the source");
        };
        let Some(lines) = self.lines(range.module) else {
            return unsupported("a module whose source the port can't read");
        };
        let line = range.start_line as usize;
        let Some(text) = lines.get(line.wrapping_sub(1)) else {
            return unsupported("a definition outside its module's source");
        };
        let start = range.start_column as usize - 1;
        if text.get(start..start + name.len()) != Some(&name[..])
            || text.contains(&'\t')
            || !name
                .iter()
                .all(|character| character.is_ascii_alphanumeric() || *character == '_')
        {
            return unsupported("a definition whose name the port can't place");
        }
        let mut end = start + name.len();
        let mut position = end;
        while text.get(position) == Some(&' ') {
            position += 1;
        }
        if text.get(position) == Some(&'(') {
            let mut depth = 0;
            loop {
                match text.get(position) {
                    Some('(') => depth += 1,
                    Some(')') => {
                        depth -= 1;
                        if depth == 0 {
                            end = position + 1;
                            break;
                        }
                    }
                    Some(_) => {}
                    None => return unsupported("a definition whose parameters span lines"),
                }
                position += 1;
            }
        }
        Ok(SourceRange {
            start_line: range.start_line,
            start_column: range.start_column,
            end_line: range.start_line,
            end_column: end as i32,
            ..range
        })
    }

    /// The definition `Name == ` written right before an expression, with where its name is.
    pub fn definition_before(&self, range: SourceRange) -> Option<(String, SourceRange)> {
        // Scans only as far as the name, since what comes before it may be a comment.
        let found = self.before_until(range, |found| match found {
            [first, second, ..] if (first.2, second.2) != ('=', '=') => true,
            [.., previous, last] if found.len() > 3 => {
                last.0 != previous.0
                    || last.1 != previous.1 - 1
                    || !(last.2.is_ascii_alphanumeric() || last.2 == '_')
            }
            _ => false,
        })?;
        if found.len() < 3 || found[0].2 != '=' || found[1].2 != '=' {
            return None;
        }
        let (line, end, _) = found[2];
        let mut start = 2;
        while start + 1 < found.len()
            && found[start + 1].0 == line
            && found[start + 1].1 == found[start].1 - 1
            && (found[start + 1].2.is_ascii_alphanumeric() || found[start + 1].2 == '_')
        {
            start += 1;
        }
        let name: String = found[2..=start]
            .iter()
            .rev()
            .map(|&(_, _, character)| character)
            .collect();
        // The name starts its line, or follows white space, as a definition's does.
        let lines = self.lines(range.module)?;
        let column = found[start].1;
        if column > 1 && !lines[line as usize - 1][column as usize - 2].is_ascii_whitespace() {
            return None;
        }
        if !name
            .chars()
            .all(|character| character.is_ascii_alphanumeric() || character == '_')
            || !name
                .chars()
                .any(|character| character.is_ascii_alphabetic())
            || name == "LOCAL"
        {
            return None;
        }
        Some((
            name,
            SourceRange {
                start_line: line,
                start_column: column,
                end_line: line,
                end_column: end,
                ..range
            },
        ))
    }

    /// Whether an expression ends a definition: what follows it is the end of the module or
    /// what starts a unit of the module; none where the port can't tell.
    pub fn ends_definition(&self, range: SourceRange) -> Option<bool> {
        let lines = self.lines(range.module)?;
        let mut line = range.end_line as usize - 1;
        let mut column = range.end_column as usize;
        let mut depth = 0;
        let mut words: Vec<String> = Vec::new();
        while words.len() < 3 {
            let Some(text) = lines.get(line) else {
                return Some(true);
            };
            if column >= text.len() {
                line += 1;
                column = 0;
                continue;
            }
            let character = text[column];
            let following = text.get(column + 1).copied();
            if !character.is_ascii() || character == '\t' {
                return None;
            }
            if depth > 0 {
                if character == '*' && following == Some(')') {
                    depth -= 1;
                    column += 2;
                } else if character == '(' && following == Some('*') {
                    depth += 1;
                    column += 2;
                } else {
                    column += 1;
                }
                continue;
            }
            if character == '(' && following == Some('*') {
                depth += 1;
                column += 2;
            } else if character == '\\' && following == Some('*') {
                line += 1;
                column = 0;
            } else if character.is_ascii_whitespace() {
                column += 1;
            } else if character.is_ascii_alphanumeric() || character == '_' {
                let start = column;
                while column < text.len()
                    && (text[column].is_ascii_alphanumeric() || text[column] == '_')
                {
                    column += 1;
                }
                words.push(text[start..column].iter().collect());
            } else {
                let start = column;
                while column < text.len()
                    && !text[column].is_ascii_alphanumeric()
                    && !text[column].is_ascii_whitespace()
                    && text[column] != '('
                    || column == start
                {
                    column += 1;
                }
                words.push(text[start..column].iter().collect());
            }
        }
        const UNITS: [&str; 15] = [
            "VARIABLE",
            "VARIABLES",
            "CONSTANT",
            "CONSTANTS",
            "ASSUME",
            "ASSUMPTION",
            "AXIOM",
            "THEOREM",
            "LEMMA",
            "PROPOSITION",
            "COROLLARY",
            "RECURSIVE",
            "LOCAL",
            "INSTANCE",
            "EXTENDS",
        ];
        let first = words[0].as_str();
        Some(
            first.starts_with("====")
                || first.starts_with("----")
                || UNITS.contains(&first)
                || words
                    .get(1)
                    .is_some_and(|word| word == "==" || word == "(" || word == "["),
        )
    }

    /// Where each variable is declared, in the IR's order: the name in its VARIABLE declaration,
    /// found in the modules the IR's places name.
    pub fn variable_places(&self) -> Translated<Vec<SourceRange>> {
        let mut modules: Vec<TextId> = self.texts.keys().copied().collect();
        modules.sort_unstable();
        let mut found: HashMap<String, Vec<SourceRange>> = HashMap::new();
        for module in modules {
            let Some(lines) = self.lines(module) else {
                continue;
            };
            for (name, line, column) in declared_variables(&lines)? {
                found.entry(name).or_default().push(SourceRange {
                    module,
                    start_line: line,
                    start_column: column,
                    end_line: line,
                    end_column: column,
                });
            }
        }
        let mut places = Vec::new();
        for &variable in &self.ir.variables {
            let name = self.text(variable);
            match found.get(name).map(Vec::as_slice) {
                Some([place]) => places.push(SourceRange {
                    end_column: place.start_column + name.chars().count() as i32 - 1,
                    ..*place
                }),
                _ => return unsupported("a variable whose declaration the port can't place"),
            }
        }
        Ok(places)
    }

    // --- the source, for the places of the nodes SANY makes of parts of the IR's ---

    fn lines(&self, module: TextId) -> Option<std::rc::Rc<Vec<Vec<char>>>> {
        self.texts.get(&module).cloned()
    }

    // The characters before a place, back to the start of the module, nearest first, past white
    // space, as (line, column, character); `None` at a comment or a character that isn't ASCII.
    fn before(&self, range: SourceRange, count: usize) -> Option<Vec<(i32, i32, char)>> {
        self.before_until(range, |found| found.len() >= count)
    }

    // The characters before a place, nearest first, past white space and comments, until
    // `is_done` says so or the module starts; `None` at a tab or a character that isn't ASCII.
    fn before_until(
        &self,
        range: SourceRange,
        is_done: impl Fn(&[(i32, i32, char)]) -> bool,
    ) -> Option<Vec<(i32, i32, char)>> {
        let lines = self.lines(range.module)?;
        let mut found: Vec<(i32, i32, char)> = Vec::new();
        let mut line = range.start_line;
        let mut column = range.start_column - 1;
        while !is_done(&found) && found.len() < 1000 {
            if column <= 0 {
                line -= 1;
                if line <= 0 {
                    break;
                }
                column = lines.get(line as usize - 1)?.len() as i32;
                continue;
            }
            let character = *lines.get(line as usize - 1)?.get(column as usize - 1)?;
            if !character.is_ascii() || character == '\t' {
                return None;
            }
            if !character.is_ascii_whitespace() {
                found.push((line, column, character));
            }
            column -= 1;
        }
        Some(found)
    }

    // Checks that one of the tokens comes right before a place, past white space.
    fn expect_before(&self, range: SourceRange, tokens: &[&str]) -> Translated<()> {
        let longest = tokens.iter().map(|token| token.len()).max().unwrap_or(0);
        let found = self.before(range, longest).unwrap_or_default();
        let text: String = found
            .iter()
            .rev()
            .map(|&(_, _, character)| character)
            .collect();
        if tokens.iter().any(|token| text.ends_with(token)) {
            Ok(())
        } else {
            unsupported("a CASE arm SANY may place apart from its expressions")
        }
    }

    // Where an `OTHER -> e` arm starts, from where e starts.
    fn start_of_other(&self, value: SourceRange) -> Translated<SourceRange> {
        let found = self.before(value, 7).unwrap_or_default();
        let text: String = found
            .iter()
            .rev()
            .map(|&(_, _, character)| character)
            .collect();
        if !text.ends_with("OTHER->") || found.len() < 7 {
            return unsupported("an OTHER arm the port can't place");
        }
        let (line, column, _) = found[6];
        Ok(SourceRange {
            start_line: line,
            start_column: column,
            ..value
        })
    }

    // Where a field `name |-> e` (or `name : S`) starts, from where e starts: at the name, which
    // follows `[` or `,`.
    fn start_of_field(
        &self,
        value: SourceRange,
        field: TextId,
        separator: &str,
    ) -> Translated<SourceRange> {
        let name: Vec<char> = self.text(field).chars().collect();
        let count = separator.len() + name.len() + 1;
        let found = self.before(value, count).unwrap_or_default();
        let text: String = found
            .iter()
            .rev()
            .map(|&(_, _, character)| character)
            .collect();
        let expected =
            |opening: char| format!("{opening}{}{separator}", name.iter().collect::<String>());
        let first = found.get(count - 2).copied();
        let last = found.get(separator.len()).copied();
        match (first, last) {
            (Some((line, column, _)), Some((last_line, last_column, _)))
                if (text == expected('[') || text == expected(','))
                    && line == last_line
                    && last_column - column + 1 == name.len() as i32 =>
            {
                Ok(SourceRange {
                    start_line: line,
                    start_column: column,
                    ..value
                })
            }
            _ => unsupported("a record field the port can't place"),
        }
    }

    // Where an update `!... = e` of an EXCEPT starts: at its `!`, which the scan finds back from
    // e past `=` and the path, written with no comment or nested brackets.
    fn start_of_update(&self, path: &[PathStep], value: SourceRange) -> Translated<SourceRange> {
        // Back to a `!` at no depth of brackets.
        let found = self
            .before_until(value, |found| {
                let mut depth = 0;
                for &(_, _, character) in found.iter().skip(1) {
                    match character {
                        ']' => depth += 1,
                        '[' => depth -= 1,
                        '!' if depth == 0 => return true,
                        _ => {}
                    }
                }
                depth < 0
            })
            .unwrap_or_default();
        if found.first().map(|&(_, _, character)| character) != Some('=') {
            return unsupported("an EXCEPT the port can't place");
        }
        // Back to the `!` that starts the path: brackets balance, and the path has as many steps.
        let mut depth = 0;
        let mut steps = 0;
        for &(line, column, character) in &found[1..] {
            match character {
                ']' => {
                    if depth == 0 {
                        steps += 1;
                    }
                    depth += 1;
                }
                '[' => depth -= 1,
                '.' if depth == 0 => steps += 1,
                '!' if depth == 0 => {
                    if steps != path.len() {
                        break;
                    }
                    return Ok(SourceRange {
                        start_line: line,
                        start_column: column,
                        ..value
                    });
                }
                _ => {}
            }
            if depth < 0 {
                break;
            }
        }
        unsupported("an EXCEPT the port can't place")
    }
}

/// The names a module's VARIABLE declarations declare, each with its line and column, past
/// comments and strings.
fn declared_variables(lines: &[Vec<char>]) -> Translated<Vec<(String, i32, i32)>> {
    // The tokens: identifiers and keywords with their places, and other characters alone.
    let mut tokens: Vec<(String, i32, i32)> = Vec::new();
    let mut depth = 0;
    let mut modules = 0;
    for (index, line) in lines.iter().enumerate() {
        if line.contains(&'\t') || !line.iter().all(char::is_ascii) {
            if depth == 0 && line.iter().collect::<String>().contains("VARIABLE") {
                return unsupported("a VARIABLE declaration the port can't place");
            }
            continue;
        }
        let mut position = 0;
        while position < line.len() {
            let character = line[position];
            let following = line.get(position + 1).copied();
            if depth > 0 {
                if character == '*' && following == Some(')') {
                    depth -= 1;
                    position += 2;
                } else if character == '(' && following == Some('*') {
                    depth += 1;
                    position += 2;
                } else {
                    position += 1;
                }
                continue;
            }
            if character == '(' && following == Some('*') {
                depth += 1;
                position += 2;
            } else if character == '\\' && following == Some('*') {
                break;
            } else if character == '"' {
                position += 1;
                while position < line.len() && line[position] != '"' {
                    position += if line[position] == '\\' { 2 } else { 1 };
                }
                position += 1;
            } else if character.is_ascii_alphanumeric() || character == '_' {
                let start = position;
                while position < line.len()
                    && (line[position].is_ascii_alphanumeric() || line[position] == '_')
                {
                    position += 1;
                }
                let word: String = line[start..position].iter().collect();
                if word == "MODULE" {
                    modules += 1;
                }
                tokens.push((word, index as i32 + 1, start as i32 + 1));
            } else {
                if !character.is_ascii_whitespace() {
                    tokens.push((character.to_string(), index as i32 + 1, position as i32 + 1));
                }
                position += 1;
            }
        }
    }
    if modules > 1 {
        return unsupported("a module with modules inside it");
    }
    let mut declared = Vec::new();
    let mut index = 0;
    while index < tokens.len() {
        if tokens[index].0 == "VARIABLE" || tokens[index].0 == "VARIABLES" {
            index += 1;
            while let Some(token) = tokens.get(index) {
                declared.push(token.clone());
                if tokens.get(index + 1).map(|token| token.0.as_str()) != Some(",") {
                    break;
                }
                index += 2;
            }
        }
        index += 1;
    }
    Ok(declared)
}

// The lines with the characters of comments blanked, but for tabs and characters that aren't
// ASCII, which keep the places after them in doubt.
fn blank_comments(mut lines: Vec<Vec<char>>) -> Vec<Vec<char>> {
    let mut depth = 0;
    for line in &mut lines {
        let mut column = 0;
        let mut is_in_string = false;
        while column < line.len() {
            let character = line[column];
            let following = line.get(column + 1).copied();
            let blanked = if depth > 0 {
                match (character, following) {
                    ('(', Some('*')) => {
                        depth += 1;
                        2
                    }
                    ('*', Some(')')) => {
                        depth -= 1;
                        2
                    }
                    _ => 1,
                }
            } else if is_in_string {
                is_in_string = character != '"';
                column += if character == '\\' { 2 } else { 1 };
                continue;
            } else {
                match (character, following) {
                    ('"', _) => {
                        is_in_string = true;
                        column += 1;
                        continue;
                    }
                    ('(', Some('*')) => {
                        depth = 1;
                        2
                    }
                    ('\\', Some('*')) => line.len() - column,
                    _ => {
                        column += 1;
                        continue;
                    }
                }
            };
            for held in &mut line[column..column + blanked] {
                if held.is_ascii() && *held != '\t' {
                    *held = ' ';
                }
            }
            column += blanked;
        }
    }
    lines
}
