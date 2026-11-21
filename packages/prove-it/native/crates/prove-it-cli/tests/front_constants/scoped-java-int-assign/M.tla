---- MODULE M ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x
Inv == -1 \in Int
====
