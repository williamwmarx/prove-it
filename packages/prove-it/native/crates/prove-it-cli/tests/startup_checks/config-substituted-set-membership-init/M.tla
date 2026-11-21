---- MODULE M ----
EXTENDS TLC, Integers
CONSTANT C
VARIABLE x
Z == {1}
Init == x = 0 /\ "a" \in C
Next == x' = x
====
