---- MODULE M ----
VARIABLE x
ASSUME (CHOOSE n \in {} : TRUE) = 1
Init == x = 0
Next == x' = x
====
