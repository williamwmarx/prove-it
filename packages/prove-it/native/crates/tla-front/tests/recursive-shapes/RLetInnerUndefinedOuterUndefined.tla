---- MODULE RLetInnerUndefinedOuterUndefined ----
Op ==
  LET
    RECURSIVE F(_)
    D == LET RECURSIVE G(_) IN 0
  IN 0
====
