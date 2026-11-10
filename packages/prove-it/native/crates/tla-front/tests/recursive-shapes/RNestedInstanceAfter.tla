---- MODULE RNestedInstanceAfter ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      I == INSTANCE RecursiveHelper
      F(n) == I!H
    IN 0
  IN Outer
====
