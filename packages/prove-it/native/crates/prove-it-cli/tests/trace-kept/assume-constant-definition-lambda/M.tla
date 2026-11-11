---- MODULE M ----
EXTENDS Naturals, Integers, TLC, FiniteSets, Sequences
VARIABLE x
T == {<<s, t>> \in {f \in [1..2 -> {1}] : TRUE} : TRUE} # {}
D == IF FALSE THEN TLCSet(1, 2) ELSE <<[i \in Nat |-> i], {3, 1, 2}>>
Init == x = 0
Next == x' = x + 1
ASSUME T /\ "x" \in D[2]

====
