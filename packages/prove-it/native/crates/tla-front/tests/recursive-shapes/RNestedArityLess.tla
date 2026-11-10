---- MODULE RNestedArityLess ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      F == 0
    IN 0
  IN Outer
====
