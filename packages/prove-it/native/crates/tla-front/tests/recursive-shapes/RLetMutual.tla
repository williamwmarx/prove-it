---- MODULE RLetMutual ----
Op ==
  LET
    RECURSIVE F(_), G(_)
    F(n) == G(n)
    G(n) == F(n)
  IN F({})
====
