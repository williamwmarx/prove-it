---- MODULE RLetBodyBoundShadow ----
Op ==
  LET
    RECURSIVE F(_)
    F(n) == 0
  IN \A F \in {} : F
====
