---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
ASSUME [[n \in Nat |-> n] EXCEPT ![-1] = 1 \div 0][1] = 1
Init == x=0
Next == x'=x
====
