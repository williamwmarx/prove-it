---- MODULE let_instance_call_stack ----
VARIABLE x
Init == x = 0
Next == x' = LET L == INSTANCE FixAdd IN L!G(1)
====

