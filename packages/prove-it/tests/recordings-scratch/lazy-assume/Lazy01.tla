---- MODULE Lazy01 ----
EXTENDS Integers
VARIABLE x
ASSUME ({} \cup 0) = 0
Init == x = 0
Next == x' = x
====
