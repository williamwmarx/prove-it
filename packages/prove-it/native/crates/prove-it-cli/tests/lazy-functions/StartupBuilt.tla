---- MODULE StartupBuilt ----
EXTENDS Naturals, TLC
VARIABLE x
F[n \in 1..2] == PrintT(<<"F", n>>)
G == [n \in {"b", "a"} |-> PrintT(<<"G", n>>)]
H == [n \in 1..2 |-> [m \in 1..n |-> PrintT(<<"H", n, m>>)]]
Init == x = 0 /\ F[1] /\ F[2] /\ G["a"] /\ H[2][1]
Next == x < 1 /\ x' = x + 1 /\ F[1]
====
