---- MODULE RLetDefinedBefore ----
Op ==
  LET
    F(n) == 0
    RECURSIVE F(_)
  IN 0
====
