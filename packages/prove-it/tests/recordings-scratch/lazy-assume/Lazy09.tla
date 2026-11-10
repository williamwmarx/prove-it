---- MODULE Lazy09 ----
EXTENDS Integers
VARIABLE x
ASSUME 3 \in ({1} \ 0)
Init == x = 0
Next == x' = x
====
