---- MODULE RNestedInnerUndefinedOuterUndefined ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      D == LET RECURSIVE G(_) IN 0
    IN 0
  IN Outer
====
