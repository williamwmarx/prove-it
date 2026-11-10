---- MODULE RNestedUndefined ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
    IN 0
  IN Outer
====
