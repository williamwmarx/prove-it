---- MODULE RNestedSetShadow ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      F(n) == {F \in {} : TRUE}
    IN 0
  IN Outer
====
