---- MODULE M ----
EXTENDS Naturals, TLC
CONSTANT C
VARIABLE n
I == INSTANCE N
D == [k |-> {3, 1, 2}, j |-> I!Op(1)]
Init == n = 0
Next == n' = n + 1
Inv == n < 2
====
