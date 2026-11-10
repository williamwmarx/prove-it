//! A port of `src/sany/selectors.ts`: SANY's `Generator.selectorToNode`, which turns a name such
//! as `Op(a)!lab(b)!:!2` into the semantic node it names, following the Subexpression algorithm of
//! SANY's Subexpression.tla.

use crate::ast::Expr;
use crate::sany::Result;
use crate::sany::nodes::{Graph, Name, NodeId, SanyLocation};

/// What `createSelectorResolver` takes from the generator (`SelectorGenerator` in
/// `selectors.ts`), which `generator.rs` implements. TLC 1.7.4 is retired, so there is no
/// `version`: the port follows TLC master.
pub trait SelectorGenerator {
    fn graph(&self) -> &Graph;
    fn graph_mut(&mut self) -> &mut Graph;
    fn resolve_symbol(&self, name: &str) -> Option<NodeId>;
    fn resolve_synonym(&self, name: &str) -> Name;
    fn generate_expression(&mut self, expression: &Expr) -> Result<NodeId>;
    fn generate_argument(
        &mut self,
        operator: NodeId,
        index: usize,
        argument: &Expr,
        location: &SanyLocation,
    ) -> Result<NodeId>;
    /// `createOpAppl`, followed by `matchArguments` as the generator's resolver does.
    fn create_op_appl(
        &mut self,
        operator: NodeId,
        operands: Vec<NodeId>,
        location: &SanyLocation,
    ) -> Result<NodeId>;
    fn create_op_arg(&mut self, operator: NodeId, location: &SanyLocation) -> NodeId;
    fn create_formal_param(
        &mut self,
        name: Name,
        arity: usize,
        location: Option<SanyLocation>,
    ) -> NodeId;
    fn create_lambda(
        &mut self,
        params: Vec<NodeId>,
        body: NodeId,
        location: &SanyLocation,
    ) -> NodeId;
    fn copy_subst_in(&mut self, prefix: NodeId, body: NodeId) -> NodeId;
    fn get_builtin(&self, name: &str) -> NodeId;
    /// `Errors.addMessage` for an error SANY recovers from, and the null node SANY returns after
    /// one.
    fn add_error(&mut self, location: &SanyLocation, text: String) -> NodeId;
    /// `Generator.illegalLabelRef`: whether the node being generated lies outside the scope of a
    /// declaration that the label lies in.
    fn is_out_of_label_scope(&self, label: NodeId) -> bool;
    /// `Generator.illegalAPPosRef`, for the clause at `position` of an ASSUME/PROVE.
    fn is_out_of_clause_scope(&self, assume_prove: NodeId, position: usize) -> bool;
}
