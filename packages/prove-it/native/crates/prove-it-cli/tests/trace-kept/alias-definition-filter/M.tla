---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets, Sequences
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
T == {<<s, t>> \in {f \in [1..2 -> {1}] : TRUE} : TRUE} # {}
D == {i \in Nat : i = x}
Inv == 2 \notin D
Alias == [x |-> x, d |-> 1 \in D]

====
