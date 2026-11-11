---- MODULE UnchangedInitUnreached ----
EXTENDS Naturals
VARIABLE x
Init == x = 0 /\ (FALSE /\ UNCHANGED x)
Next == x' = x
====
