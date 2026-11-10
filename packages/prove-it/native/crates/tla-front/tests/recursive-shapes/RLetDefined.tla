---- MODULE RLetDefined ----
Op ==
  LET
    RECURSIVE F(_)
    F(n) == IF n = {} THEN 0 ELSE F({})
  IN F({})
====
