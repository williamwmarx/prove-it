---- MODULE Lazy03 ----
EXTENDS Integers
VARIABLE x
ASSUME ({} \ 0) = {}
Init == x = 0
Next == x' = x
====
