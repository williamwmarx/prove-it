---- MODULE RNestedOtherParamShadow ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      G(F) == F
      F(n) == 0
    IN 0
  IN Outer
====
