---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Bad == PrintT("p") /\ 1 \div 0 = 0
Use == Bad
Init == x = 0
Next == x' = x
====
