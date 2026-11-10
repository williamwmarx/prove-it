---- MODULE RNestedArityZero ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F
      F(x) == x
    IN 0
  IN Outer
====
