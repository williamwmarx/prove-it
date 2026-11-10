---- MODULE RModuleInnerRecursive ----
RECURSIVE F(_)
F(n) == LET RECURSIVE G(_) G(m) == G(m) IN G(n)
Use == F({})
====
