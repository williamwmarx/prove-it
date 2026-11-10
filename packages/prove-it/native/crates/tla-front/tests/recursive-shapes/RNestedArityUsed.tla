---- MODULE RNestedArityUsed ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      G == F({})
      F(x, y) == 0
    IN G
  IN Outer
====
