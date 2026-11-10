---- MODULE RNestedNestedLetParamShadow ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      F(n) == LET G(F) == 0 IN 0
    IN 0
  IN Outer
====
