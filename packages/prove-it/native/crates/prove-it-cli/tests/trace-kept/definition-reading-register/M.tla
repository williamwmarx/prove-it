---- MODULE M ----
EXTENDS Naturals, Integers, TLC, FiniteSets, Sequences
VARIABLE x
D == IF FALSE THEN TLCGet(1) = 0 ELSE (IF 7 \in {n \in Nat : n > 5} THEN {3, 1, 2} ELSE {})
Init == x = 0
Next == x' = x + 1
Inv == x < 2 \/ "x" \in D

====
