---- MODULE RModuleWrongLevelFunction ----
RECURSIVE F
D == LET F[x \in {}] == 0 IN 0
====
