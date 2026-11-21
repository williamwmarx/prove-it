---- MODULE M ----
EXTENDS Integers, TLC, E
VARIABLE x
Init == x = 0
Next == x' = x
====
