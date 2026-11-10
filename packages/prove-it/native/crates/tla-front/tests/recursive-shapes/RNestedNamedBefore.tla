---- MODULE RNestedNamedBefore ----
Op ==
  LET Outer ==
    LET
      G == F({})
      RECURSIVE F(_)
      F(n) == 0
    IN G
  IN Outer
====
