---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets, Sequences
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
T == {<<s, t>> \in {f \in [1..2 -> {1}] : TRUE} : TRUE} # {}
F(S, P(_)) == P(S) /\ "a" \in S
ASSUME T /\ F({20, 10}, LAMBDA u : [s \in u |-> s][20] = 20)
====
