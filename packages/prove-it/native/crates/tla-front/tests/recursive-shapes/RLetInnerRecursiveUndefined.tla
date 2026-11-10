---- MODULE RLetInnerRecursiveUndefined ----
Op ==
  LET
    RECURSIVE F(_)
    F(n) == LET RECURSIVE G(_) IN 0
  IN 0
====
