---- MODULE RNestedWrongLevelUsed ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F
      D == LET F == 0 IN F
    IN F
  IN Outer
====
