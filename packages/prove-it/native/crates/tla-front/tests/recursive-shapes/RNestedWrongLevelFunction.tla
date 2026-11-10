---- MODULE RNestedWrongLevelFunction ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F
      D == LET F[x \in {}] == 0 IN 0
    IN 0
  IN Outer
====
