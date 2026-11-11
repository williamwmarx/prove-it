---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == IF x = 0 /\ y = 0 THEN x' = 1 /\ y' = 1 ELSE x' = RandomElement(0..1) /\ y' = RandomElement(0..1)
Inv == x = y
====
