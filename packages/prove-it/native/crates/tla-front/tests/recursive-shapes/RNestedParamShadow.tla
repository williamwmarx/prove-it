---- MODULE RNestedParamShadow ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_), K
      F(F) == 0
    IN 0
  IN Outer
====
