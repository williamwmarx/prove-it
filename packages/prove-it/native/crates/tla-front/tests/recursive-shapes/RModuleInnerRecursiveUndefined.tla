---- MODULE RModuleInnerRecursiveUndefined ----
RECURSIVE F(_)
F(n) == LET RECURSIVE G(_) IN 0
====
