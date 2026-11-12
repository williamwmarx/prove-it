---- MODULE M ----
VARIABLE x
K == CHOOSE n \in {} : TRUE
Init == x = K
Next == x' = x
====
