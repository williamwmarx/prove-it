---- MODULE RNestedDefinedBefore ----
Op ==
  LET Outer ==
    LET
      F(n) == 0
      RECURSIVE F(_)
    IN 0
  IN Outer
====
