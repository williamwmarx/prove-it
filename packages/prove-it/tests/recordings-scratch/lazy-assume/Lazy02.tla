---- MODULE Lazy02 ----
EXTENDS Integers
VARIABLE x
ASSUME ({} \cap 0) = {}
Init == x = 0
Next == x' = x
====
