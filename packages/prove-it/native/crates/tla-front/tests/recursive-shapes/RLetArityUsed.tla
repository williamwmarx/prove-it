---- MODULE RLetArityUsed ----
Op ==
  LET
    RECURSIVE F(_)
    G == F({})
    F(x, y) == 0
  IN G
====
