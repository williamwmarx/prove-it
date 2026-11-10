// STUB: replaced by the real port
//! The name and the signatures a literal port of `rewriter.ts` has, for the kernel
//! (`internalizer.ts` makes `new Rewriter(manager, KERNEL_REWRITER_OPTIONS)`; the quantifier
//! instantiation reaches it as `context.rewriter`). Only what the kernel touches is here.

use crate::core::ast::{AstManager, Expr};
use crate::util::error::SmtError;

/// The options of `rewriter.ts`. The real port adds `arith: ArithRewriterOptions`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RewriterOptions {
    pub is_eliminating_and: bool,
    pub is_rewriting_patterns: bool,
}

/// The kernel's rewriter options.
pub const KERNEL_REWRITER_OPTIONS: RewriterOptions = RewriterOptions {
    is_eliminating_and: false,
    is_rewriting_patterns: true,
};

#[derive(Clone, Debug)]
pub struct Rewriter {
    pub options: RewriterOptions,
}

impl Rewriter {
    /// `new Rewriter(manager, options, isNestedDer = false)`. The stub keeps only the options, so
    /// that a context can be made before the rewriter is ported.
    pub fn new(_m: &mut AstManager, options: RewriterOptions, _is_nested_der: bool) -> Rewriter {
        Rewriter { options }
    }

    /// rewrite: the expression rewritten, with a reference the caller releases. STUB: the
    /// identity, which takes none of the real rewriter's steps. The quantifier instantiation
    /// (`qi_queue.rs`) reaches it; `scripts/smt-ematching-reference.ts` checks that the
    /// TypeScript rewriter leaves the instances of `quantifier_manager.rs`'s tests as they are,
    /// and prints the steps it takes.
    pub fn rewrite(&mut self, m: &mut AstManager, expr: Expr) -> Result<Expr, SmtError> {
        m.inc_ref(expr);
        Ok(expr)
    }
}
