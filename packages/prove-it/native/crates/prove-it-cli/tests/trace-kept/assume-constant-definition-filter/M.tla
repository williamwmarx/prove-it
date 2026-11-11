---- MODULE M ----
EXTENDS Naturals, Integers, TLC, FiniteSets, Sequences
VARIABLE x
T == {<<s, t>> \in {f \in [1..2 -> {1}] : TRUE} : TRUE} # {}
Ev == {n \in Nat : n % 2 = 0}
D == IF FALSE THEN TLCSet(1, 2) ELSE IF 4 \in Ev THEN {3, 1, 2} ELSE {}
ASSUME T /\ "x" \in D
Init == x = 0
Next == x' = x + 1

====
