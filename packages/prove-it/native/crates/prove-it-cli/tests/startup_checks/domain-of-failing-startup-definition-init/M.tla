---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
D0 == DOMAIN {}
Op(a) == DOMAIN a
Init == x = 0 /\ DOMAIN Op(D0) = {}
Next == x' = x
====
