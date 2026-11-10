---- MODULE RLetRedeclared ----
Op ==
  LET
    RECURSIVE F(_)
    RECURSIVE F(_)
    F(n) == 0
  IN 0
====
