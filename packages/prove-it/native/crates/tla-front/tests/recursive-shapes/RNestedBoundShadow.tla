---- MODULE RNestedBoundShadow ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      F(n) == \E F \in {} : F
    IN 0
  IN Outer
====
