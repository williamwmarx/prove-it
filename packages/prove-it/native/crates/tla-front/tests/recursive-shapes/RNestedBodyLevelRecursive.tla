---- MODULE RNestedBodyLevelRecursive ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F
    IN LET RECURSIVE G G == 0 IN 0
  IN Outer
====
