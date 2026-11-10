---- MODULE RLetHigherOrderUsed ----
Op ==
  LET
    RECURSIVE F(_), K
    G == F(0)
    F(H(_)) == 0
  IN 0
====
