---- MODULE M ----
EXTENDS TLC, Integers
VARIABLE x
A == Any
ASSUME SUBSET A = SUBSET A
Init == x = 0
Next == x' = x
====
