---- MODULE RLetShadowsParameter ----
Op(F) ==
  LET
    RECURSIVE F(_)
    F(n) == 0
  IN 0
====
