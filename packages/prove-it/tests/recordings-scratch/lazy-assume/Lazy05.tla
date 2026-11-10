---- MODULE Lazy05 ----
EXTENDS Integers
VARIABLE x
ASSUME 1 \in (0 \cup {1})
Init == x = 0
Next == x' = x
====
