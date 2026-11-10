---- MODULE Lazy04 ----
EXTENDS Integers
VARIABLE x
ASSUME 1 \in ({1} \cup 0)
Init == x = 0
Next == x' = x
====
