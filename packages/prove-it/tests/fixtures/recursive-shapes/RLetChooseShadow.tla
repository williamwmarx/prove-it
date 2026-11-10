---- MODULE RLetChooseShadow ----
Op ==
  LET
    RECURSIVE F(_)
    F(n) == CHOOSE F \in {} : TRUE
  IN 0
====
