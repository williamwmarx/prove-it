---- MODULE M ----
EXTENDS Integers
VARIABLES x, f
Init == x = 0 /\ f = [i \in 0..2, j \in 1..2 |-> i + j]
Next == x' = x + f[1, 1 \div x] /\ UNCHANGED f
====
