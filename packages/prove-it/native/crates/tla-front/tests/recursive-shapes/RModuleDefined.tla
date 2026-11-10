---- MODULE RModuleDefined ----
RECURSIVE F(_)
F(n) == IF n = {} THEN 0 ELSE F({})
Use == F({})
====
