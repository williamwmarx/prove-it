//! The expressions of `generateModule` (`generator.ts` lines 1159–1815): junctions, CASE, EXCEPT,
//! records, LET, CHOOSE, `generateExpression`, bounds, labels and the parameters and spans of
//! definitions.

// HACK: the bodies are stubs, to be ported.
#![allow(dead_code, unused_variables)]

use std::rc::Rc;

use crate::ast::{
    Bound, Declaration, Definition, Expr, Instance, Location, OperatorParam, Position,
};
use crate::sany::Result;
use crate::sany::nodes::NodeId;
use crate::sany::source::TokenSpan;

use super::{BoundSymbols, ModuleGenerator};

/// `LetUnit`: a unit of a LET, in source order.
#[derive(Clone, Debug)]
pub(super) enum LetUnit {
    Recursive(Vec<Rc<Declaration>>),
    Instance(Rc<Instance>),
    Definition(Rc<Definition>),
}

/// What `getUnresolvedOperator` finds: an infix, prefix or postfix operator that no symbol
/// defines, with the token SANY names it by. `fixity` is "prefix", "infix" or "postfix".
#[derive(Clone, Debug)]
pub(super) struct UnresolvedOperator {
    pub(super) index: usize,
    pub(super) name: String,
    pub(super) fixity: &'static str,
}

impl ModuleGenerator<'_> {
    /// `generateJunction` (generator.ts 1159–1180): A /\ B /\ C nests as ((A /\ B) /\ C) in
    /// SANY, and the parser flattens it. `expression` is a `Junction`.
    pub(super) fn generate_junction(&mut self, expression: &Expr) -> Result<NodeId> {
        todo!("port generator.ts 1159-1180")
    }

    /// `generateCase` (generator.ts 1182–1208). `expression` is a `Case`.
    pub(super) fn generate_case(&mut self, expression: &Expr) -> Result<NodeId> {
        todo!("port generator.ts 1182-1208")
    }

    /// `findTokenBefore` (generator.ts 1210–1215).
    pub(super) fn find_token_before(&self, index: usize, text: &str) -> usize {
        todo!("port generator.ts 1210-1215")
    }

    /// `generateExcept` (generator.ts 1217–1256). `expression` is an `Except`.
    pub(super) fn generate_except(&mut self, expression: &Expr) -> Result<NodeId> {
        todo!("port generator.ts 1217-1256")
    }

    /// `findNameOrKeyword` (generator.ts 1258–1263).
    pub(super) fn find_name_or_keyword(&self, start: usize, name: &str) -> usize {
        todo!("port generator.ts 1258-1263")
    }

    /// `generateRecordFields` (generator.ts 1265–1290): `operator` is "$RcdConstructor" or
    /// "$SetOfRcds", and `expression` a `Record`.
    pub(super) fn generate_record_fields(
        &mut self,
        operator: &str,
        expression: &Expr,
    ) -> Result<NodeId> {
        todo!("port generator.ts 1265-1290")
    }

    /// `getTokenPosition` (generator.ts 1292–1297).
    pub(super) fn get_token_position(&self, index: usize) -> Position {
        todo!("port generator.ts 1292-1297")
    }

    /// `getRecursiveDeclarations` (generator.ts 1299–1324): the declarations of a RECURSIVE
    /// statement from the token at `start`, which the syntax tree of a LET leaves out.
    pub(super) fn get_recursive_declarations(&self, start: usize) -> Vec<Rc<Declaration>> {
        todo!("port generator.ts 1299-1324")
    }

    /// `getLetUnits` (generator.ts 1326–1354): the units of a LET in source order, with its
    /// RECURSIVE statements found among its tokens. `expression` is a `Let`.
    pub(super) fn get_let_units(&self, expression: &Expr) -> Vec<LetUnit> {
        todo!("port generator.ts 1326-1354")
    }

    /// `generateLet` (generator.ts 1356–1384). `expression` is a `Let`.
    pub(super) fn generate_let(&mut self, expression: &Expr) -> Result<NodeId> {
        todo!("port generator.ts 1356-1384")
    }

    /// `generateChoose` (generator.ts 1386–1420). `expression` is a `Choose`.
    pub(super) fn generate_choose(&mut self, expression: &Expr) -> Result<NodeId> {
        todo!("port generator.ts 1386-1420")
    }

    /// `getUnresolvedOperator` (generator.ts 1422–1450). `expression` is an `Apply`.
    pub(super) fn get_unresolved_operator(&self, expression: &Expr) -> Option<UnresolvedOperator> {
        todo!("port generator.ts 1422-1450")
    }

    /// `generateExpression` (generator.ts 1452–1686).
    pub(super) fn generate_expression(&mut self, expression: &Expr) -> Result<NodeId> {
        todo!("port generator.ts 1452-1686")
    }

    /// `generateBoundsWithRanges` (generator.ts 1688–1711).
    pub(super) fn generate_bounds_with_ranges(
        &mut self,
        bounds: &[Bound],
        search_start: usize,
        ranges: Vec<NodeId>,
    ) -> BoundSymbols {
        todo!("port generator.ts 1688-1711")
    }

    /// `generateLabel` (generator.ts 1713–1782). `expression` is a `Label`.
    pub(super) fn generate_label(&mut self, expression: &Expr) -> Result<NodeId> {
        todo!("port generator.ts 1713-1782")
    }

    /// `getParams` (generator.ts 1785–1805): the parameters of a definition's or instance's
    /// left-hand side, located as SANY locates them.
    pub(super) fn get_params(
        &mut self,
        params: &[OperatorParam],
        span: TokenSpan,
        is_added: bool,
    ) -> Vec<NodeId> {
        todo!("port generator.ts 1785-1805")
    }

    /// `getDefinitionSpan` (generator.ts 1807–1815): the span of a definition or instance at
    /// `location`, with the LOCAL before it.
    pub(super) fn get_definition_span(&self, location: &Location, is_local: bool) -> TokenSpan {
        todo!("port generator.ts 1807-1815")
    }
}
