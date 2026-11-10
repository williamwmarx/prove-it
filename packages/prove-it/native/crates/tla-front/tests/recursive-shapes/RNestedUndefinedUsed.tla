---- MODULE RNestedUndefinedUsed ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
    IN F({})
  IN Outer
====
