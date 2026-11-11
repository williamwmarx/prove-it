---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets, Sequences
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
T == {<<s, t>> \in {f \in [1..2 -> {1}] : TRUE} : TRUE} # {}
G(a) == (a = {1, 2, 3}) /\ "x" \in a
ASSUME T /\ \A f \in {[i \in {1} |-> {3, 1, 2}]} : G(f[1])
====
