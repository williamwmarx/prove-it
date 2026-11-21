---- MODULE instance_function_call_stack ----
EXTENDS Naturals
VARIABLE x
L == INSTANCE FixFunction WITH c <- TRUE
Init == x = 0
Next == x' = L!H
====

