---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets, Sequences
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
T == {<<s, t>> \in {f \in [1..2 -> {1}] : TRUE} : TRUE} # {}
F(A) == A # {} /\ \A B \in {A} : (<<{1, 2}>> \in B) /\ (\A s \in B : "a" \in s[1])
ASSUME T /\ F({<<{2, 1}>>})
====
