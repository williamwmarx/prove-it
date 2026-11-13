---- MODULE M ----
EXTENDS Integers, TLC
RECURSIVE F(_)
F(x) == IF x = 0 THEN 0 ELSE F(F(x - 1))
Test == PrintT(F(1))
ASSUME Test
====
