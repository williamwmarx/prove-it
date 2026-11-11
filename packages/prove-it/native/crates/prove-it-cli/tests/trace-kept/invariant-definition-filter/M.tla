---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets, Sequences
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
T == {<<s, t>> \in {f \in [1..2 -> {1}] : TRUE} : TRUE} # {}
D == IF TRUE THEN (IF 0 \in {n \in Nat : n < 2} THEN {3, 1, 2} ELSE {}) ELSE {x}
Inv == x < 2 \/ "a" \in D

====
