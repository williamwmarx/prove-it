---- MODULE FixAct ----
EXTENDS Naturals
VARIABLE x
A == x < 2 /\ x' = x + 1
B == x' = x + TRUE
====
