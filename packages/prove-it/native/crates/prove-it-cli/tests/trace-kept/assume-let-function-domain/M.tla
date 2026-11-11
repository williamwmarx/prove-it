---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets, Sequences
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
T == {<<s, t>> \in {f \in [1..2 -> {1}] : TRUE} : TRUE} # {}
ASSUME T /\ LET S == {20, 10} IN ([s \in S |-> s][20] = 20) /\ "a" \in S
====
