---- MODULE RNestedMutual ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_), G(_)
      F(n) == G(n)
      G(n) == F(n)
    IN F({})
  IN Outer
====
