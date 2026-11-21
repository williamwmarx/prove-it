---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Next == x < 2 /\ x' = x + 1
Bad == PrintT(1) /\ 1 \div 0 = 1
====
