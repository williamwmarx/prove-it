---- MODULE RNestedParamShadowDefined ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      F(F) == 0
    IN 0
  IN Outer
====
