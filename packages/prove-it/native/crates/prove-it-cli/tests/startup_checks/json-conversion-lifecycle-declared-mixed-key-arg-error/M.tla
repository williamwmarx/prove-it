---- MODULE M ----
EXTENDS Integers,TLC
CONSTANT F(_)
VARIABLE x
Init == x = 0 /\ F(1 \div 0)
Next == x' = x
====
