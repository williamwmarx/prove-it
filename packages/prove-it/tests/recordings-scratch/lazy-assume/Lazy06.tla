---- MODULE Lazy06 ----
EXTENDS Integers
VARIABLE x
ASSUME 1 \in ((1..2) \cup "a")
Init == x = 0
Next == x' = x
====
