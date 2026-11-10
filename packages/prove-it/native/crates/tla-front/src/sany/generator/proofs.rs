//! The proofs of `generateModule` (`generator.ts` lines 2335–2997): facts, DEF clauses, USE and
//! HIDE, NEW, ASSUME/PROVE, theorem definitions, leaf and non-leaf proofs, step bodies, theorems
//! and assumptions.

// HACK: the bodies are stubs, to be ported.
#![allow(dead_code, unused_variables, clippy::ptr_arg)]

use crate::ast::{
    AssumeProve, Assumption, Expr, Fact, Location, NewSymbol, Proof, ProofStep, Statement,
    StepBody, Theorem, UseOrHide,
};
use crate::ordered_map::OrderedMap;
use crate::sany::Result;
use crate::sany::nodes::{Name, NodeId, SanyLocation};
use crate::sany::source::TokenSpan;

use super::{DefEntryParts, LocalContext, ModuleGenerator};

/// What `generateStepBody` gives: the step's node, and whether it is a PICK, whose context the
/// caller pops.
#[derive(Clone, Copy, Debug)]
pub(super) struct GeneratedStep {
    pub(super) node: NodeId,
    pub(super) is_pick: bool,
}

impl ModuleGenerator<'_> {
    /// `getFactModules` (generator.ts 2335–2345): the module a `Fact::Module` names, which SANY
    /// leaves out after reporting it at the module's name.
    pub(super) fn get_fact_modules(&mut self, name: &Name, location: &Location) -> Vec<NodeId> {
        todo!("port generator.ts 2335-2345")
    }

    /// `generateFacts` (generator.ts 2348–2356).
    pub(super) fn generate_facts(&mut self, facts: &[Fact]) -> Result<Vec<NodeId>> {
        todo!("port generator.ts 2348-2356")
    }

    /// `isParenthesized` (generator.ts 2358–2359).
    pub(super) fn is_parenthesized(&self, span: TokenSpan) -> bool {
        todo!("port generator.ts 2358-2359")
    }

    /// `getOperandSpan` (generator.ts 2360–2361).
    pub(super) fn get_operand_span(&self, expression: &Expr) -> TokenSpan {
        todo!("port generator.ts 2360-2361")
    }

    /// `getApplicationKind` (generator.ts 2363–2368): how SANY's parser shapes an application.
    /// `expression` is an `Apply`.
    pub(super) fn get_application_kind(&self, expression: &Expr, span: TokenSpan) -> &'static str {
        todo!("port generator.ts 2363-2368")
    }

    /// `getSyntaxKind` (generator.ts 2370–2375): the kind of SANY's syntax node for an
    /// expression, or for a token its text.
    pub(super) fn get_syntax_kind(&self, expression: &Expr, span: TokenSpan) -> Option<String> {
        todo!("port generator.ts 2370-2375")
    }

    /// `hasChildlessFirstChild` (generator.ts 2378–2383), whose `undefined` is `None`.
    pub(super) fn has_childless_first_child(
        &self,
        expression: &Expr,
        span: TokenSpan,
    ) -> Option<bool> {
        todo!("port generator.ts 2378-2383")
    }

    /// `getDefEntryParts` (generator.ts 2386–2474).
    pub(super) fn get_def_entry_parts(
        &self,
        expression: &Expr,
        span: TokenSpan,
    ) -> Option<DefEntryParts> {
        todo!("port generator.ts 2386-2474")
    }

    /// `reportDefEntry` (generator.ts 2476–2497).
    pub(super) fn report_def_entry(&mut self, expression: &Expr) -> bool {
        todo!("port generator.ts 2476-2497")
    }

    /// `generateDefs` (generator.ts 2499–2521).
    pub(super) fn generate_defs(&mut self, defs: &[Fact]) -> Result<Vec<NodeId>> {
        todo!("port generator.ts 2499-2521")
    }

    /// `checkKeywordOnly` (generator.ts 2525–2531), of a USE, HIDE or BY with `is_only`, `facts`
    /// and `defs`.
    pub(super) fn check_keyword_only(
        &mut self,
        is_only: bool,
        facts: &[Fact],
        defs: &[Fact],
        location: &SanyLocation,
    ) {
        todo!("port generator.ts 2525-2531")
    }

    /// `generateUseOrHide` (generator.ts 2533–2559).
    pub(super) fn generate_use_or_hide(&mut self, use_or_hide: &UseOrHide) -> Result<NodeId> {
        todo!("port generator.ts 2533-2559")
    }

    /// `generateNewSymbol` (generator.ts 2562–2586).
    pub(super) fn generate_new_symbol(&mut self, symbol: &NewSymbol) -> Result<NodeId> {
        todo!("port generator.ts 2562-2586")
    }

    /// `generateAssumeProve` (generator.ts 2589–2667): `goal` is the TypeScript's
    /// `goal?.isSuffices`, `None` without a goal.
    pub(super) fn generate_assume_prove(
        &mut self,
        assume_prove: &AssumeProve,
        depth: usize,
        goal: Option<bool>,
    ) -> Result<NodeId> {
        todo!("port generator.ts 2589-2667")
    }

    /// `createTheoremDefinition` (generator.ts 2671–2695). The TypeScript's default `isTheorem` is
    /// true.
    pub(super) fn create_theorem_definition(
        &mut self,
        uid: u32,
        name: Name,
        body: NodeId,
        location: SanyLocation,
        labels: OrderedMap<Name, NodeId>,
        is_theorem: bool,
    ) -> NodeId {
        todo!("port generator.ts 2671-2695")
    }

    /// `generateLeafProof` (generator.ts 2697–2713). `proof` is not `Steps`.
    pub(super) fn generate_leaf_proof(&mut self, proof: &Proof) -> Result<NodeId> {
        todo!("port generator.ts 2697-2713")
    }

    /// `generateStepBody` (generator.ts 2716–2758), whose `undefined` is `None`.
    pub(super) fn generate_step_body(
        &mut self,
        step: &ProofStep,
        body_span: TokenSpan,
    ) -> Result<Option<GeneratedStep>> {
        todo!("port generator.ts 2716-2758")
    }

    /// `isInfixExpression` (generator.ts 2761–2769): an expression SANY parses as N_InfixExpr.
    pub(super) fn is_infix_expression(&self, expression: &Expr) -> bool {
        todo!("port generator.ts 2761-2769")
    }

    /// `generateProof` (generator.ts 2772–2930).
    pub(super) fn generate_proof(&mut self, proof: &Proof) -> Result<NodeId> {
        todo!("port generator.ts 2772-2930")
    }

    /// `generateOtherStep` in `generateProof` (generator.ts 2784–2815): a DEFINE, USE, HIDE or
    /// INSTANCE step, whose instances join the proof's `instances`.
    pub(super) fn generate_other_step(
        &mut self,
        body: &StepBody,
        step_span: TokenSpan,
        body_span: TokenSpan,
        instances: &mut Vec<NodeId>,
    ) -> Result<Option<NodeId>> {
        todo!("port generator.ts 2784-2815")
    }

    /// `generateAssertion` in `generateProof` (generator.ts 2846–2880). `previous_right` is
    /// `infixStep.previousRight`, and `assume_context` the step's `assumeContext`, which the
    /// assertion takes for the context of an ASSUME/PROVE and gives back.
    pub(super) fn generate_assertion(
        &mut self,
        statement: &Statement,
        step: &ProofStep,
        is_suffices: bool,
        body_span: TokenSpan,
        assume_context: &mut LocalContext,
        previous_right: &mut Option<NodeId>,
    ) -> Result<NodeId> {
        todo!("port generator.ts 2846-2880")
    }

    /// `processTheorem` (generator.ts 2934–2972).
    pub(super) fn process_theorem(&mut self, theorem: &Theorem) -> Result<()> {
        todo!("port generator.ts 2934-2972")
    }

    /// `processAssumption` (generator.ts 2974–2995).
    pub(super) fn process_assumption(&mut self, assumption: &Assumption) -> Result<()> {
        todo!("port generator.ts 2974-2995")
    }
}
