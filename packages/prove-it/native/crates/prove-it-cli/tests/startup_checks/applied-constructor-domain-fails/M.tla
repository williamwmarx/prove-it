---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == x' = [i \in {1, 2} \cup {1 \div 0} |-> PrintT(i)][1]
====
