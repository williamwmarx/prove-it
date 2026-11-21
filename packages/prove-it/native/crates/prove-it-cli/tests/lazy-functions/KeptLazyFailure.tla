---- MODULE KeptLazyFailure ----
EXTENDS Integers, TLC
VARIABLE x
Init == x \in 0..1
Next == UNCHANGED x
Inv == [[n \in 1..2 |-> IF n = x + 1 THEN 1 \div 0 ELSE n] EXCEPT ![2] = x][1] # 7
====
