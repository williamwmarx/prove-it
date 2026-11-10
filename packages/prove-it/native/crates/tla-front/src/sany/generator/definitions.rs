//! The definitions, instances and units of `generateModule` (`generator.ts` lines 1816–2334 and
//! 2999–3139): operators, functions, RECURSIVE, substitutions, instances, declarations, the
//! EXTENDS list and the loop over the module's units.

// HACK: the bodies are stubs, to be ported.
#![allow(dead_code, unused_variables, clippy::ptr_arg)]

use std::rc::Rc;

use crate::ast::{Declaration, Definition, Instance, Location};
use crate::sany::Result;
use crate::sany::nodes::{NodeId, SanyLocation, Subst};
use crate::sany::source::TokenSpan;

use super::ModuleGenerator;

impl ModuleGenerator<'_> {
    /// `processOperator` (generator.ts 1816–1880). `definition` is an operator definition, and
    /// `definitions` the definitions of the LET or DEFINE step that holds it, if any.
    pub(super) fn process_operator(
        &mut self,
        definition: &Rc<Definition>,
        definitions: Option<&mut Vec<NodeId>>,
    ) -> Result<()> {
        todo!("port generator.ts 1816-1880")
    }

    /// `endOpDefNode` (generator.ts 1882–1896).
    pub(super) fn end_op_def_node(
        &mut self,
        node: NodeId,
        body: NodeId,
        location: SanyLocation,
        pre_comments: Vec<String>,
    ) {
        todo!("port generator.ts 1882-1896")
    }

    /// `processFunction` (generator.ts 1898–1969). `definition` is a function definition.
    pub(super) fn process_function(
        &mut self,
        definition: &Rc<Definition>,
        definitions: Option<&mut Vec<NodeId>>,
    ) -> Result<()> {
        todo!("port generator.ts 1898-1969")
    }

    /// `processRecursive` (generator.ts 1971–1996).
    pub(super) fn process_recursive(&mut self, declarations: &[Rc<Declaration>]) {
        todo!("port generator.ts 1971-1996")
    }

    /// `checkForUndefinedRecursiveOps` (generator.ts 1998–2010).
    pub(super) fn check_for_undefined_recursive_ops(&mut self) {
        todo!("port generator.ts 1998-2010")
    }

    /// `processSubstitutions` (generator.ts 2014–2099): SubstInNode's constructor and
    /// processSubst, for an instance of `instancee`, the module whose context the TypeScript
    /// passes.
    pub(super) fn process_substitutions(
        &mut self,
        instance: &Instance,
        instancee: NodeId,
        location: &SanyLocation,
    ) -> Result<Vec<Subst>> {
        todo!("port generator.ts 2014-2099")
    }

    /// `checkArity` in `processSubstitutions` (generator.ts 2041–2051):
    /// Generator.checkSubstitutionForCorrectArity.
    pub(super) fn check_arity(&mut self, target: NodeId, substitute: NodeId) {
        todo!("port generator.ts 2041-2051")
    }

    /// `createSubstIn` (generator.ts 2101–2126): a SubstIn, or an APSubstIn when
    /// `is_assume_prove`. The TypeScript's default `instantiatingModule` is `self.module`.
    pub(super) fn create_subst_in(
        &mut self,
        is_assume_prove: bool,
        substs: Vec<Subst>,
        body: NodeId,
        instantiated_module: NodeId,
        location: SanyLocation,
        instantiating_module: NodeId,
    ) -> NodeId {
        todo!("port generator.ts 2101-2126")
    }

    /// `processModuleDefinition` (generator.ts 2128–2235): a named instance, `I == INSTANCE M`.
    /// `None` for `definitions` and `instances` is the TypeScript's `undefined`.
    pub(super) fn process_module_definition(
        &mut self,
        instance: &Rc<Instance>,
        definitions: Option<&mut Vec<NodeId>>,
        instances: Option<&mut Vec<NodeId>>,
    ) -> Result<()> {
        todo!("port generator.ts 2128-2235")
    }

    /// `generateInstance` (generator.ts 2237–2332): an unnamed INSTANCE, at the top level or as a
    /// proof step located at `step_location`. The TypeScript's default `isTopLevel` is true.
    pub(super) fn generate_instance(
        &mut self,
        instance: &Rc<Instance>,
        is_top_level: bool,
        step_location: Option<SanyLocation>,
    ) -> Result<NodeId> {
        todo!("port generator.ts 2237-2332")
    }

    /// `getOperatorSpan` (generator.ts 2999–3006): a declared operator or operator parameter is
    /// located with its arguments.
    pub(super) fn get_operator_span(&self, start: usize, arity: usize) -> TokenSpan {
        todo!("port generator.ts 2999-3006")
    }

    /// `getDeclarationSpan` (generator.ts 3008–3009).
    pub(super) fn get_declaration_span(&self, declaration: &Declaration) -> TokenSpan {
        todo!("port generator.ts 3008-3009")
    }

    /// `createDeclaration` (generator.ts 3011–3035).
    pub(super) fn create_declaration(
        &mut self,
        declaration: &Declaration,
        decl_kind: u32,
    ) -> NodeId {
        todo!("port generator.ts 3011-3035")
    }

    /// processExtendsList, `ast.extends.forEach` (generator.ts 3037–3071), of `self.ast`.
    pub(super) fn process_extends_list(&mut self) -> Result<()> {
        todo!("port generator.ts 3037-3071")
    }

    /// `checkRecursiveSection` (generator.ts 3073–3081): `kind` is the TypeScript's `type`.
    pub(super) fn check_recursive_section(&mut self, location: &Location, kind: &str) {
        todo!("port generator.ts 3073-3081")
    }

    /// `ast.units.forEach` and the `checkForUndefinedRecursiveOps` after it (generator.ts
    /// 3083–3138), over `self.ast`. An inner module is `generate_inner_module`.
    pub(super) fn process_units(&mut self) -> Result<()> {
        todo!("port generator.ts 3083-3138")
    }
}
