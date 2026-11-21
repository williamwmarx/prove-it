---- MODULE Base ----
EXTENDS Integers, TLC
VARIABLE x
P == x < 2
NextB == x' = (x + 1) % 3 /\ PrintT(<<"P", P>>)
====
