---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Test == PrintT({} \cap 0)
Init == FALSE /\ x = 0
Next == x' = x
Inv == Test
====
