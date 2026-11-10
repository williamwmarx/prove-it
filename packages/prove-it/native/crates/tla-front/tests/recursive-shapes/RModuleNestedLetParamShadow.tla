---- MODULE RModuleNestedLetParamShadow ----
RECURSIVE F(_)
F(n) == LET G(F) == 0 IN 0
====
