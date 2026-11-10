---- MODULE RNestedBodyLevel ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F
    IN LET F == 0 IN 0
  IN Outer
====
