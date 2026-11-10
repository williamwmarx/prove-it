---- MODULE RLetOtherParamShadow ----
Op ==
  LET
    RECURSIVE F(_)
    G(F) == F
    F(n) == 0
  IN 0
====
