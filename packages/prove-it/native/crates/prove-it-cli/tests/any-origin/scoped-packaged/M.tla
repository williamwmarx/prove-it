---- MODULE M ----
EXTENDS AnySet
VARIABLE x
Init == x = (1 \in ANY)
Next == UNCHANGED x
Inv == x
====
