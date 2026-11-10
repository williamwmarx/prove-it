---- MODULE RModuleMutual ----
RECURSIVE F(_), G(_)
F(n) == G(n)
G(n) == F(n)
Use == F({})
====
