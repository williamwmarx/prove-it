---- MODULE RNestedBodyBoundShadow ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      F(n) == 0
    IN \A F \in {} : F
  IN Outer
====
