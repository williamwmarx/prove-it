---- MODULE RNestedHigherOrder ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      F(H(_)) == 0
    IN 0
  IN Outer
====
