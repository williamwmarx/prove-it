---- MODULE M ----
EXTENDS Integers, TLC, HM, HN
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
====
