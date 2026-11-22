---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 2
THEOREM T == x \in {0, 1}
C == PrintT("c") /\ T /\ PrintT("d")
====
