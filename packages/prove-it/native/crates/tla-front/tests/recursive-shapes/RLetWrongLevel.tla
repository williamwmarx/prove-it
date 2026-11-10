---- MODULE RLetWrongLevel ----
Op ==
  LET
    RECURSIVE F
    D == LET F == 0 IN 0
  IN 0
====
