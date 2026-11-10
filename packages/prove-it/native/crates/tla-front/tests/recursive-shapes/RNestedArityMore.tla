---- MODULE RNestedArityMore ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      F(x, y) == 0
    IN 0
  IN Outer
====
