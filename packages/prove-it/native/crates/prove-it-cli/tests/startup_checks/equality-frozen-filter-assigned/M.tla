---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Filter == {n \in SUBSET {1} : 1 \div 0 = 1}
F2 == {n \in {1, 2} : 1 \div 0 = 1}
Next == x' = Filter /\ {} = x'
====
