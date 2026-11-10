---- MODULE RNestedWrongLevel ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F
      D == LET F == 0 IN 0
    IN 0
  IN Outer
====
