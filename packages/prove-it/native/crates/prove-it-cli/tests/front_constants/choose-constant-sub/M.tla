---- MODULE M ----
VARIABLE x
CONSTANT C
Foo == CHOOSE n \in {1, 2} : n = 5
Init == x = C
Next == x' = x
====
