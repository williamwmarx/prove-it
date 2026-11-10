---- MODULE Lazy11 ----
EXTENDS Integers
VARIABLE x
ASSUME [j \in {1} |-> 4] \in [{1} -> {n \in Int : n % 2 = 0}]
Init == x = 0
Next == x' = x
====
