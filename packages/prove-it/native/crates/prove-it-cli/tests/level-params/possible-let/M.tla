---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x = 0 /\ x' = 1
H == LET A == x' = x IN x = 1
====
