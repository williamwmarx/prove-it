---- MODULE RNestedHigherOrderUsed ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_), K
      G == F(0)
      F(H(_)) == 0
    IN 0
  IN Outer
====
