---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == \/ x < 3 /\ x' = x + 1 /\ y' = y
        \/ x = 3 /\ x' = 4 /\ y' = RandomElement(0..3)
Inv == y < 2
====
