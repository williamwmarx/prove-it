---- MODULE RLetNamedBefore ----
Op ==
  LET
    G == F({})
    RECURSIVE F(_)
    F(n) == 0
  IN G
====
