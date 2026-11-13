---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Test == PrintT(CHOOSE y \in {} : TRUE)
Init == x = Test
Next == x' = x
====
