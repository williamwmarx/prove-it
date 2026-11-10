---- MODULE RNestedPrimed ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      F(x) == x'
    IN 0
  IN Outer
====
