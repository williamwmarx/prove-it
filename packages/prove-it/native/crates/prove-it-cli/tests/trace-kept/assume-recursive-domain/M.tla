---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets, Sequences
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
T == {<<s, t>> \in {f \in [1..2 -> {1}] : TRUE} : TRUE} # {}
RECURSIVE R(_, _)
R(S, n) == IF n = 0 THEN "a" \in S ELSE ([s \in S |-> s][20] = 20) /\ R(S, n - 1)
ASSUME T /\ R({20, 10}, 2)
====
