---- MODULE RLetSetShadow ----
Op ==
  LET
    RECURSIVE F(_)
    F(n) == {F \in {} : TRUE}
  IN 0
====
