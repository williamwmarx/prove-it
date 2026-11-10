---- MODULE RLetPrimed ----
Op ==
  LET
    RECURSIVE F(_)
    F(x) == x'
  IN 0
====
