---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets, Sequences
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
T == {<<s, t>> \in {f \in [1..2 -> {1}] : TRUE} : TRUE} # {}
F(S) == [s \in S |-> s][20] = 20
G(S) == F(S) /\ "a" \in S
ASSUME T /\ G({20, 10})
====
