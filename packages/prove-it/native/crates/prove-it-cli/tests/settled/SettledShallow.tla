---- MODULE SettledShallow ----
EXTENDS Naturals
VARIABLE x
RECURSIVE H(_)
H(n) == IF n = 0 THEN {1} ELSE H(n - 1)
RECURSIVE F(_)
F(n) == IF n = 0 THEN FALSE ELSE ([b |-> n] \in [a : H(100)]) \/ F(n - 1)
Init == x = 0
Next == x' = x
Inv == F(100) = FALSE
====
