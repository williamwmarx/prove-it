---- MODULE RNestedInnerRecursive ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      F(n) == LET RECURSIVE G(_) G(m) == G(m) IN G(n)
    IN F({})
  IN Outer
====
