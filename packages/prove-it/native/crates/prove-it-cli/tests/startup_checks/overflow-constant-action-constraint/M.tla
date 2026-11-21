---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
RECURSIVE R(_)
R(n) == R(n + 1)
G[n \in Nat] == G[n + 1]
Init == x \in 1..2
Next == x' = x + 1
Con == R(0) = 0 \/ G[0] = 0
====
