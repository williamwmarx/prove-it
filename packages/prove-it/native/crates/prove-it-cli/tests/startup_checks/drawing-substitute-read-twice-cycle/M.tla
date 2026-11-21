---- MODULE M ----
EXTENDS Integers, TLC
RECURSIVE F(_), G(_)
G(n) == F(n)
F(n) == IF n > 0 THEN G(n - 1) ELSE RandomElement(1..100)
I1 == INSTANCE OU1 WITH c <- F(1)
I2 == INSTANCE OU2 WITH c <- G(1)
ASSUME TRUE
====
