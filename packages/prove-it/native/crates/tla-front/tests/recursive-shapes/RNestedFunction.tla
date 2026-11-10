---- MODULE RNestedFunction ----
Op ==
  LET Outer ==
    LET
      RECURSIVE f
      f[x \in {}] == f[x]
    IN f
  IN Outer
====
