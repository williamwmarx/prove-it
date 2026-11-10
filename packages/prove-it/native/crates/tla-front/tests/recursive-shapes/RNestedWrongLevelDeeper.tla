---- MODULE RNestedWrongLevelDeeper ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F
      D == LET E == LET F == 0 IN 0 IN 0
    IN 0
  IN Outer
====
