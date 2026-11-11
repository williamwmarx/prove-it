---- MODULE M ----
VARIABLE x
K == CHOOSE n \in {} : TRUE
Init == x = 0
Next == x' = x
Inv == K
====
