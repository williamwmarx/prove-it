---- MODULE RLetParamShadowDefined ----
Op ==
  LET
    RECURSIVE F(_)
    F(F) == 0
  IN 0
====
