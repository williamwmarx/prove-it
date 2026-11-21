---- MODULE instance_with_call_stack ----
EXTENDS Naturals
VARIABLE x
L == INSTANCE FixCall WITH c <- TRUE
Init == x = 0
Next == x' = L!G(1)
====

