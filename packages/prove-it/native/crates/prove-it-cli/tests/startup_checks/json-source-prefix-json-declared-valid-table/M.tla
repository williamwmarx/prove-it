---- MODULE M ----
EXTENDS Integers,TLC,Json
CONSTANT F(_)
G(x) == x
VARIABLE x
Init == x = 0 /\ G(1 \div 0)
Next == x' = x
====
