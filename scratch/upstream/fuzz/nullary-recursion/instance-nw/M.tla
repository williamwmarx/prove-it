---- MODULE M ----
VARIABLE x
I == INSTANCE Inner
Spec == x = 0 /\ [][x' = x]_<<x, I!R>>
====
