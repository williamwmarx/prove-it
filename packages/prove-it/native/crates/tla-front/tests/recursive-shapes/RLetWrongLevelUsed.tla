---- MODULE RLetWrongLevelUsed ----
Op ==
  LET
    RECURSIVE F
    D == LET F == 0 IN F
  IN F
====
