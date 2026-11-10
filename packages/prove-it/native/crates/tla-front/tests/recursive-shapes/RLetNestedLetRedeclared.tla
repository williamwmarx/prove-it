---- MODULE RLetNestedLetRedeclared ----
Op ==
  LET
    RECURSIVE F(_)
    F(n) == LET RECURSIVE F(_) F(m) == 0 IN 0
  IN 0
====
