---- MODULE RLetFunction ----
Op ==
  LET
    RECURSIVE f
    f[x \in {}] == f[x]
  IN f
====
