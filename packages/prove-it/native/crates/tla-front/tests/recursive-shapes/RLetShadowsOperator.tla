---- MODULE RLetShadowsOperator ----
F(n) == 0
Op ==
  LET
    RECURSIVE F(_)
    F(n) == 0
  IN F({})
====
