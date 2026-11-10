---- MODULE RLetShadowsConstant ----
CONSTANT F
Op ==
  LET
    RECURSIVE F(_)
    F(n) == 0
  IN F({})
====
