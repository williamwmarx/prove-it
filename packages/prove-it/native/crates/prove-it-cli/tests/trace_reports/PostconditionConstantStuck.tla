---- MODULE PostconditionConstantStuck ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x > 0 /\ x' = x
Never == FALSE
====
