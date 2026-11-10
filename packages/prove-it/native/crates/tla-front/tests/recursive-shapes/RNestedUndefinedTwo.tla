---- MODULE RNestedUndefinedTwo ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_), G
      G == 0
    IN 0
  IN Outer
====
