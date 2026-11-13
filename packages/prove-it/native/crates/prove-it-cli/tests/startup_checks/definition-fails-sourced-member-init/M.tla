---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Test == PrintT(1 \in {1} \X {2})
Init == x = Test
Next == x' = x
====
