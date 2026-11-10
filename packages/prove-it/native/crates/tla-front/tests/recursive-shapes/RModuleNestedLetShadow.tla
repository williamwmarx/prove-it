---- MODULE RModuleNestedLetShadow ----
RECURSIVE F(_)
F(n) == LET F == 0 IN F
====
