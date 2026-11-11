---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Inv == Print("checked once", TRUE)
Init == x = 0
Next == x < 2 /\ x' = x + 1
====