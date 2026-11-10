---- MODULE RLetShadowsBound ----
Op == \E F \in {} :
  LET
    RECURSIVE F(_)
    F(n) == 0
  IN 0
====
