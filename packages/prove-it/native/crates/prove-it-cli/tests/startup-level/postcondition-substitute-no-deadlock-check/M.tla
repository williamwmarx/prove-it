---- MODULE M ----
EXTENDS Naturals, TLC
CONSTANT C
VARIABLE n
I == INSTANCE N
D == <<{3, 1, 2}, I!Op(1)>>
Init == n = 0
Next == n < 2 /\ n' = n + 1
Inv == TRUE
P == "a" \in D[1]
====
