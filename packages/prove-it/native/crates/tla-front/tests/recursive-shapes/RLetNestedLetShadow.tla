---- MODULE RLetNestedLetShadow ----
Op ==
  LET
    RECURSIVE F(_)
    F(n) == LET F == 0 IN F
  IN 0
====
