---- MODULE RNestedInstanceNamed ----
Op ==
  LET Outer ==
    LET
      I == INSTANCE RecursiveHelper
      RECURSIVE I, K
    IN 0
  IN Outer
====
