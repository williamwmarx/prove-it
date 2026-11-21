---- MODULE M ----
EXTENDS TLC, Integers
VARIABLE x
INSTANCE Base
Init == x = 0
Q == FALSE
Next == NextB
====
