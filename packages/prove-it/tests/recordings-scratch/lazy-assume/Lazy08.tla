---- MODULE Lazy08 ----
EXTENDS Integers
VARIABLE x
ASSUME 3 \in (0 \cap {1})
Init == x = 0
Next == x' = x
====
