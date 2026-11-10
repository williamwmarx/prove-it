---- MODULE RNestedExtra ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      F(n) == 0
      F(n) == 1
    IN 0
  IN Outer
====
