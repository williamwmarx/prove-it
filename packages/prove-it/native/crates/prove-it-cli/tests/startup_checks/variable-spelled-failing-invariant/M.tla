---- MODULE M ----
EXTENDS Integers, TLC
Inv == \A x \in {1} : x \div 0 = 1
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
====
