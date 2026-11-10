---- MODULE RNestedNestedLetShadow ----
Op ==
  LET Outer ==
    LET
      RECURSIVE F(_)
      F(n) == LET F == 0 IN F
    IN 0
  IN Outer
====
