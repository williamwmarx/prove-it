---- MODULE M ----
EXTENDS Integers, TLC, HR
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
====
