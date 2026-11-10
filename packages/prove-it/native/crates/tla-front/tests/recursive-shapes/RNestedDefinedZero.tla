---- MODULE RNestedDefinedZero ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F
      F == 0
    IN F
  IN Outer
====
