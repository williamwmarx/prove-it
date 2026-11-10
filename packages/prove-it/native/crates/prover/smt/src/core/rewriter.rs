// STUB: replaced by the real port
//! The name and the signatures a literal port of `rewriter.ts` has, for the kernel
//! (`internalizer.ts` makes `new Rewriter(manager, KERNEL_REWRITER_OPTIONS)`; the quantifier
//! instantiation reaches it as `context.rewriter`). Only what the kernel touches is here.

use crate::core::ast::AstManager;

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
}
