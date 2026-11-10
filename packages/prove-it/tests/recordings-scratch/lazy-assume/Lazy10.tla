---- MODULE Lazy10 ----
EXTENDS Integers
VARIABLE x
ASSUME 2 \in (0 \cup {1})
Init == x = 0
Next == x' = x
====
