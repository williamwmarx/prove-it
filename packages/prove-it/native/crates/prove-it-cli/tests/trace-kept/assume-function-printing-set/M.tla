---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets, Sequences
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
T == {<<s, t>> \in {f \in [1..2 -> {1}] : TRUE} : TRUE} # {}
F(f) == f[1] + f[1] = 2 /\ f[1] = 1
ASSUME T /\ F([i \in {1} |-> Print(<<i, {3, 1}>>, i)])
====
