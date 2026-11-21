---- MODULE LazyDomainMember ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == UNCHANGED x
ASSUME [n \in SUBSET {1} |-> 3][{1}] = 3
ASSUME [n \in SUBSET {1} |-> 3][1] = 3
====
