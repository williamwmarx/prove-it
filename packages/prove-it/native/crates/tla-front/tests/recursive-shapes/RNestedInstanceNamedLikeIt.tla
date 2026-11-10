---- MODULE RNestedInstanceNamedLikeIt ----
Op ==
  LET Outer ==
    LET
      RECURSIVE I
      I == INSTANCE RecursiveHelper
    IN 0
  IN Outer
====
