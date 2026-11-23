---- MODULE DotParameters ----
EXTENDS Naturals
VARIABLE x
Inc(i) == x < 6 /\ x' = x + i
Next == \E i \in 1..2 : Inc(i)
Init == x = 0
====
