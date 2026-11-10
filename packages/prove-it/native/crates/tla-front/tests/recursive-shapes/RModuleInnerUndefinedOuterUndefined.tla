---- MODULE RModuleInnerUndefinedOuterUndefined ----
RECURSIVE F(_)
D == LET RECURSIVE G(_) IN 0
====
