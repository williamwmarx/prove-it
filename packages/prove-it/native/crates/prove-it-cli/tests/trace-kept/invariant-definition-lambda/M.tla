---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets, Sequences
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
T == {<<s, t>> \in {f \in [1..2 -> {1}] : TRUE} : TRUE} # {}
D == IF TRUE THEN (IF [n \in Nat |-> n][1] = 1 THEN {3, 1, 2} ELSE {}) ELSE {x}
Next2 == x' = (x + 1) % 3 /\ (x < 1 \/ 3 \in D)
Inv == x < 2 \/ "a" \in D

====
