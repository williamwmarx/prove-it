---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE n
I == INSTANCE N
Al == I!Al
Init == n = 0
Next == n' = n + 1
Inv == n < 2
====
