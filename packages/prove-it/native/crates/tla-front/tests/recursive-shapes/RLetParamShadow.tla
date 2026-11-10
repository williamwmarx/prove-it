---- MODULE RLetParamShadow ----
Op ==
  LET
    RECURSIVE F(_), K
    F(F) == 0
  IN 0
====
