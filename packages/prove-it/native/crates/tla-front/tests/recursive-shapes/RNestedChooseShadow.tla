---- MODULE RNestedChooseShadow ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      F(n) == CHOOSE F \in {} : TRUE
    IN 0
  IN Outer
====
